defmodule Mix.Tasks.Gate.Four do
  @moduledoc """
  Gate 4 Hardware Telemetry & Throughput Benchmark on `armix` (14-core ARM64 Neoverse-N1).

  Compares Pure Elixir Reference Layer-2 implementations against Zero-Copy Rustler NIF
  Layer-4 kernels (`nif_kbo_compare`, `nif_feature_vector`, and SIMD-vectorized
  `nif_fv_subsumes_batch`) over real `TPTP-Smoke` higher-order problem arenas.
  """
  use Mix.Task

  alias Astraea.{Arena, Native, TptpCorpus, TptpLower}

  @shortdoc "Runs Gate 4 Benchee throughput comparison (Elixir Reference vs Rust/SIMD NIF)"

  @impl Mix.Task
  def run(_args) do
    Mix.Task.run("app.start")

    smoke = TptpCorpus.load_split(:smoke)
    tptp_root = TptpCorpus.default_tptp_root()

    # Build a combined arena and 256 real THF0 formula roots from TPTP-Smoke
    {arena, roots} =
      smoke
      |> Enum.take(15)
      |> Enum.reduce({Arena.new(), []}, fn stem, {ar_acc, roots_acc} ->
        path = TptpCorpus.problem_path(stem, tptp_root)
        {:ok, lowered} = TptpLower.from_file(path, tptp_root: tptp_root)

        new_roots =
          Enum.map(lowered.axioms, &elem(&1, 2)) ++
            Enum.map(lowered.conjectures, &elem(&1, 1))

        # Keep largest arena with most formulas for microbenchmarking
        if map_size(lowered.arena.nodes) > map_size(ar_acc.nodes) do
          {lowered.arena, new_roots}
        else
          {ar_acc, roots_acc}
        end
      end)

    flat_bin = Arena.to_flat_binary(arena)
    sample_roots = Enum.take(Stream.cycle(roots), 64)
    fvs = Enum.map(sample_roots, &Arena.feature_vector(arena, &1))
    # Replicate to 1,024 clause feature vectors (64 KB flat buffer)
    fvs_1024 = Enum.take(Stream.cycle(fvs), 1024)
    targets_bin = Native.pack_feature_vectors(fvs_1024)
    cand_fv = hd(fvs_1024)
    pairs = for s <- Enum.take(sample_roots, 16), t <- Enum.take(sample_roots, 16), do: {s, t}

    IO.puts(
      "\n=== Gate 4 Benchmark: Arena nodes=#{map_size(arena.nodes)} (#{byte_size(flat_bin)} B), 256 KBO pairs, 1024 FVIndex targets ==="
    )

    Benchee.run(
      %{
        "KBO (256 pairs) - Elixir Reference" => fn ->
          for {s, t} <- pairs, do: Arena.kbo_compare(arena, s, t)
        end,
        "KBO (256 pairs) - Rust NIF (Zero-Copy)" => fn ->
          for {s, t} <- pairs, do: Native.nif_kbo_compare(flat_bin, s, t)
        end,
        "FVIndex Subsumption (1024 clauses) - Elixir Reference" => fn ->
          Enum.filter(fvs_1024, &Arena.fv_subsumes?(cand_fv, &1))
        end,
        "FVIndex Subsumption (1024 clauses) - Rust SIMD NIF" => fn ->
          Native.nif_fv_subsumes_batch(cand_fv, targets_bin)
        end
      },
      time: 1.5,
      warmup: 0.5,
      memory_time: 0.5,
      print: [fast_warning: false]
    )
  end
end
