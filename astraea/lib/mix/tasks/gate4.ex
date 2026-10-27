defmodule Mix.Tasks.Gate.Four do
  @moduledoc """
  Gate 4 throughput benchmark of the saturation engine's feature-vector index
  (`Astraea.Engine.FVIndex`) on `armix`.

  The index is filled with the subsumption feature vectors of clauses clausified
  from `TPTP-Smoke` problems, at the sizes the given-clause loop reaches (active set
  hundreds to a few thousand clauses, passive set up to tens of thousands), and
  queried through every available backend:

    1. plain Elixir (`backend: :elixir`, the reference),
    2. the same `defn` kernels on the default Nx backend (`Nx.Defn.Evaluator`),
    3. `NxSimd.Compiler` native SIMD code (`backend: :nx_simd`), when available,

  for single queries (forward subsumption of a given clause, backward subsumption)
  and batches of 32 queries (forward subsumption of newly generated clauses). All
  backends must return identical answers before timing starts.

      mix gate.four [--sizes 256,1024,4096,16384]
  """
  use Mix.Task

  alias Astraea.{Clausifier, NxKernel, TptpCorpus, TptpLower}
  alias Astraea.Engine.{FVIndex, Kernels, Subsumption}

  @shortdoc "Benchmarks FVIndex backends (Elixir, Nx evaluator, NxSimd) at loop sizes"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")
    {opts, _} = OptionParser.parse!(args, strict: [sizes: :string])

    sizes =
      opts
      |> Keyword.get(:sizes, "256,1024,4096,16384")
      |> String.split(",")
      |> Enum.map(&String.to_integer/1)

    fvs = smoke_feature_vectors()
    Mix.shell().info("#{length(fvs)} distinct clause feature vectors from TPTP-Smoke")
    queries = fvs |> Enum.shuffle() |> Enum.take(32)
    simd? = NxKernel.available?()

    Enum.each(sizes, fn n ->
      rows = fvs |> Stream.cycle() |> Enum.take(n) |> Enum.with_index(fn fv, id -> {id, fv} end)
      elixir = build(rows, :elixir)
      simd = if simd?, do: build(rows, :nx_simd)
      if simd, do: warm(simd)

      check!(elixir, simd, queries, n)

      jobs =
        %{
          "Elixir      1 query" => fn -> FVIndex.subsumers(elixir, hd(queries)) end,
          "Elixir     32 queries" => fn -> FVIndex.subsumers_batch(elixir, queries) end
        }
        |> Map.merge(evaluator_jobs(rows, hd(queries)))
        |> Map.merge(simd_jobs(simd, queries))

      Mix.shell().info(
        "\n== #{n} indexed clauses (#{length(elixir.segments)} sealed segments) =="
      )

      Benchee.run(jobs,
        time: 1.5,
        warmup: 0.5,
        print: [fast_warning: false, configuration: false]
      )
    end)
  end

  defp smoke_feature_vectors do
    root = TptpCorpus.default_tptp_root()

    :smoke
    |> TptpCorpus.load_split()
    |> Enum.take(20)
    |> Enum.flat_map(fn stem ->
      {:ok, lowered} = TptpLower.from_file(TptpCorpus.problem_path(stem, root), tptp_root: root)
      {arena, clauses} = Clausifier.clausify(lowered)
      Enum.map(clauses, &Subsumption.clause_fv(arena, &1))
    end)
    |> Enum.uniq()
  end

  defp build(rows, backend) do
    Enum.reduce(rows, FVIndex.new(backend: backend), fn {id, fv}, idx ->
      FVIndex.insert(idx, id, fv)
    end)
  end

  # Compiles the kernels for every sealed segment shape before timing.
  defp warm(index) do
    for seg <- index.segments do
      Kernels.warmup(
        subsumers: [{16}, {16, seg.cap}],
        subsumed: [{16}, {16, seg.cap}],
        subsumers_batch: [{16, 32}, {16, seg.cap}]
      )
    end
  end

  defp check!(elixir, simd, queries, n) do
    for idx <- [simd], idx != nil, dir <- [:subsumers, :subsumed] do
      batch = :"#{dir}_batch"

      unless sorted(apply(FVIndex, batch, [idx, queries])) ==
               sorted(apply(FVIndex, batch, [elixir, queries])) do
        Mix.raise("Gate 4: NxSimd and Elixir FVIndex answers differ (#{dir}, #{n} clauses)")
      end
    end

    Mix.shell().info("\n✓ backends agree on #{n} clauses")
  end

  defp sorted(lists), do: Enum.map(lists, &Enum.sort/1)

  # The `defn` itself on the default backend, one segment of at most 4096 columns:
  # it is the executable specification, far too slow for the loop.
  defp evaluator_jobs(rows, q) when length(rows) <= 4_096 do
    block =
      rows |> Enum.map(&Tuple.to_list(elem(&1, 1))) |> Nx.tensor(type: :u16) |> Nx.transpose()

    q = Nx.tensor(Tuple.to_list(q), type: :u16)
    %{"Nx evaluator 1 query" => fn -> Kernels.subsumers(q, block) end}
  end

  defp evaluator_jobs(_rows, _q), do: %{}

  defp simd_jobs(nil, _queries), do: %{}

  defp simd_jobs(simd, queries) do
    %{
      "NxSimd      1 query" => fn -> FVIndex.subsumers(simd, hd(queries)) end,
      "NxSimd     32 queries" => fn -> FVIndex.subsumers_batch(simd, queries) end
    }
  end
end
