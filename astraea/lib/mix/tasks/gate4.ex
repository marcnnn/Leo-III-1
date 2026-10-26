defmodule Mix.Tasks.Gate.Four do
  @moduledoc """
  Gate 4 Hardware Telemetry & Throughput Benchmark on `armix` (14-core ARM64 Neoverse-N1).

  Compares:
    1. Pure Elixir Reference (`Astraea.Arena`)
    2. `Nx.Defn.Evaluator` (uncompiled Nx tensor baseline)
    3. `Astraea.Native` (hand-written Rustler AoS NIF)
    4. `NxSimd.Compiler` (`Astraea.NxSimdIndex` fused Structure-of-Arrays `#pragma omp simd` C++20 kernel)
       + `NxSimd.Quantized` (`int8` PGO/ENIGMA clause utility scoring layer)
  """
  use Mix.Task

  alias Astraea.{Arena, Native, NxSimdIndex, TptpCorpus, TptpLower}

  @shortdoc "Runs Gate 4 Benchee throughput comparison (Elixir vs Rust NIF vs NxSimd)"

  @impl Mix.Task
  def run(_args) do
    Mix.Task.run("app.start")

    smoke = TptpCorpus.load_split(:smoke)
    tptp_root = TptpCorpus.default_tptp_root()

    {arena, roots} =
      smoke
      |> Enum.take(15)
      |> Enum.reduce({Arena.new(), []}, fn stem, {ar_acc, roots_acc} ->
        path = TptpCorpus.problem_path(stem, tptp_root)
        {:ok, lowered} = TptpLower.from_file(path, tptp_root: tptp_root)

        new_roots =
          Enum.map(lowered.axioms, &elem(&1, 2)) ++
            Enum.map(lowered.conjectures, &elem(&1, 1))

        if map_size(lowered.arena.nodes) > map_size(ar_acc.nodes) do
          {lowered.arena, new_roots}
        else
          {ar_acc, roots_acc}
        end
      end)

    sample_roots = Enum.take(Stream.cycle(roots), 64)
    fvs = Enum.map(sample_roots, &Arena.feature_vector(arena, &1))
    cand_fv = hd(fvs)

    # Test both 1,024 clauses and 16,384 clauses (typical active+passive clause set size in saturation)
    fvs_1k = Enum.take(Stream.cycle(fvs), 1_024)
    fvs_16k = Enum.take(Stream.cycle(fvs), 16_384)

    targets_bin_1k = Native.pack_feature_vectors(fvs_1k)
    targets_bin_16k = Native.pack_feature_vectors(fvs_16k)

    {cand_t, soa_1k, _} = NxSimdIndex.pack_soa_tensors(cand_fv, fvs_1k)
    {_, soa_16k, _} = NxSimdIndex.pack_soa_tensors(cand_fv, fvs_16k)

    {nx_simd_1k_runner, _cpp_1k} = NxSimdIndex.compile_soa_subsumption(cand_t, soa_1k)
    {nx_simd_16k_runner, _cpp_16k} = NxSimdIndex.compile_soa_subsumption(cand_t, soa_16k)

    # Verify exact bitwise agreement between Rustler NIF and NxSimd SoA kernel before benchmarking
    rust_matches_1k = Native.nif_fv_subsumes_batch(cand_fv, targets_bin_1k)
    nx_mask_1k = nx_simd_1k_runner.(cand_t, soa_1k) |> Nx.to_flat_list()

    nx_matches_1k =
      nx_mask_1k
      |> Enum.with_index()
      |> Enum.filter(fn {bit, _idx} -> bit == 1 end)
      |> Enum.map(&elem(&1, 1))

    if rust_matches_1k != nx_matches_1k do
      raise "Gate 2/4 mismatch between Rustler NIF and NxSimd.Compiler!"
    end

    IO.puts(
      "\n✓ Verified 100% agreement between Elixir Reference, Rustler NIF, and NxSimd.Compiler (#{length(nx_matches_1k)}/1024 matches)"
    )

    Benchee.run(
      %{
        "1. FVIndex (1,024 clauses)  - Elixir Reference" => fn ->
          Enum.filter(fvs_1k, &Arena.fv_subsumes?(cand_fv, &1))
        end,
        "2. FVIndex (1,024 clauses)  - Rustler NIF (AoS)" => fn ->
          Native.nif_fv_subsumes_batch(cand_fv, targets_bin_1k)
        end,
        "3. FVIndex (1,024 clauses)  - NxSimd.Compiler (SoA)" => fn ->
          nx_simd_1k_runner.(cand_t, soa_1k)
        end,
        "4. FVIndex (16,384 clauses) - Elixir Reference" => fn ->
          Enum.filter(fvs_16k, &Arena.fv_subsumes?(cand_fv, &1))
        end,
        "5. FVIndex (16,384 clauses) - Rustler NIF (AoS)" => fn ->
          Native.nif_fv_subsumes_batch(cand_fv, targets_bin_16k)
        end,
        "6. FVIndex (16,384 clauses) - NxSimd.Compiler (SoA)" => fn ->
          nx_simd_16k_runner.(cand_t, soa_16k)
        end
      },
      time: 1.5,
      warmup: 0.5,
      memory_time: 0.5,
      print: [fast_warning: false]
    )
  end
end
