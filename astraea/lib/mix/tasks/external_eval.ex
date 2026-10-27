defmodule Mix.Tasks.External.Eval do
  @moduledoc """
  Evaluates external prover integration on a TPTP split by comparing portfolio
  configurations under the same timeout and concurrency:

    1. `baseline` - internal strategies only
    2. `racers` - plus installed external provers racing on the original problem,
       with unsat-core reconstruction (`Astraea.External.Reconstruct`)
    3. `cooperate` - internal strategies with mid-search cooperation, sending the
       clause set to E (THF to `eprover-ho` if installed, else TFF to `eprover`)
    4. `leo3_racer` - internal strategies plus Leo-III racing on the original
       problem, with unsat-core reconstruction (only if `leo3` is on `$PATH`)
    5. `leo3` - Leo-III alone on the original problem, no internal strategies and
       no reconstruction; its proofs count as `external_unverified`

  Options: `--split smoke|dev|holdout` (default `smoke`), `--timeout` ms per problem
  (default 2500), `--concurrency` problems in parallel (default 3),
  `--configs` comma-separated subset, `--out` JSON report path, `--csv` path
  for one row per problem and configuration.

      mix external.eval --split dev --timeout 5000 --out /tmp/external_dev.json
  """
  use Mix.Task

  alias Astraea.External.Provers
  alias Astraea.Portfolio
  alias Astraea.TptpCorpus

  @shortdoc "Compares portfolio runs with and without external provers on a TPTP split"

  @racers [:eprover_ho, :vampire, :cvc5]

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start")

    {opts, _rest} =
      OptionParser.parse!(args,
        strict: [
          split: :string,
          timeout: :integer,
          concurrency: :integer,
          configs: :string,
          out: :string,
          csv: :string
        ]
      )

    split =
      Map.fetch!(
        %{"smoke" => :smoke, "dev" => :dev, "holdout" => :holdout},
        Keyword.get(opts, :split, "smoke")
      )

    timeout_ms = Keyword.get(opts, :timeout, 2_500)
    concurrency = Keyword.get(opts, :concurrency, 3)
    available = Provers.available()

    configs =
      configs(available)
      |> filter_configs(Keyword.get(opts, :configs))

    Mix.shell().info(
      "split=#{split} timeout=#{timeout_ms}ms concurrency=#{concurrency} provers=#{inspect(available)}"
    )

    runs =
      Enum.map(configs, fn {name, extra_opts} ->
        t0 = System.monotonic_time(:millisecond)

        result =
          Portfolio.evaluate_split(
            split,
            [timeout_ms: timeout_ms, max_concurrency: concurrency] ++ extra_opts
          )

        summary = summarize(result, System.monotonic_time(:millisecond) - t0)
        Mix.shell().info("#{name}: #{inspect(Map.drop(summary, [:assisted_problems]))}")
        {name, summary, result}
      end)

    if out = Keyword.get(opts, :out) do
      report = Map.new(runs, fn {name, summary, _result} -> {name, summary} end)
      File.write!(out, Jason.encode!(report, pretty: true))
      Mix.shell().info("report written to #{out}")
    end

    if csv = Keyword.get(opts, :csv) do
      write_csv(csv, split, timeout_ms, runs)
      Mix.shell().info("per-problem results written to #{csv}")
    end
  end

  defp configs(available) do
    racers = Enum.filter(@racers, &(&1 in available))

    cooperate =
      cond do
        :eprover_ho in available -> [:eprover_ho]
        :eprover in available -> [:eprover]
        true -> []
      end

    leo3 =
      if :leo3 in available do
        [
          {"leo3_racer", [external: [:leo3]]},
          {"leo3", [strategies: [], external: [{:leo3, reconstruct: false}]]}
        ]
      else
        []
      end

    [
      {"baseline", []},
      {"racers", [external: racers]},
      {"cooperate", [cooperate: cooperate, cooperate_interval: 30]}
    ] ++ leo3
  end

  defp filter_configs(configs, nil), do: configs

  defp filter_configs(configs, names) do
    wanted = String.split(names, ",", trim: true)
    Enum.filter(configs, fn {name, _} -> name in wanted end)
  end

  @csv_header ~w(problem domain expected config timeout_ms result solved_lcf
                 external_unverified winning_strategy external_prover elapsed_ms)

  # `Portfolio.evaluate_split/2` keeps manifest order, so killed tasks, which
  # carry no entry, are matched to their problem by position.
  defp write_csv(path, split, timeout_ms, runs) do
    entries = TptpCorpus.load_split_entries(split)

    rows =
      for {name, _summary, result} <- runs,
          {entry, {_entry, res, ms}} <- Enum.zip(entries, result.raw_results) do
        {tag, stats} = result_tag(res)
        thm? = entry.status == "Theorem"
        assist = Map.get(stats, :external_assist)

        [
          entry.problem,
          entry.domain,
          entry.status,
          name,
          timeout_ms,
          tag,
          if(thm? and tag == :proved, do: 1, else: 0),
          if(thm? and tag == :proved_external, do: 1, else: 0),
          format_strategy(Map.get(stats, :winning_strategy)),
          (assist && assist.prover) || Map.get(stats, :prover, ""),
          ms
        ]
      end

    lines = Enum.map([@csv_header | rows], &[Enum.join(&1, ","), "\n"])
    File.write!(path, lines)
  end

  defp result_tag({:proved, _steps, stats}), do: {:proved, stats}
  defp result_tag({:error, _reason}), do: {:error, %{}}
  defp result_tag({tag, stats}) when is_map(stats), do: {tag, stats}
  defp result_tag(tag) when is_atom(tag), do: {tag, %{}}

  defp format_strategy(nil), do: ""
  defp format_strategy({:external, name}), do: "external:#{name}"
  defp format_strategy(name), do: to_string(name)

  defp summarize(result, wall_ms) do
    %{
      wall_ms: wall_ms,
      thm_total: result.thm_total,
      csa_total: result.csa_total,
      thm_solved_lcf: result.thm_solved_count,
      externally_assisted_lcf: result.externally_assisted_count,
      external_unverified: result.external_thm_solved_count,
      csa_false_proofs: length(result.csa_false_proofs),
      lcf_failures: length(result.lcf_failures),
      external_unsound: Enum.map(result.external_unsound, &inspect/1),
      strategy_wins: Map.new(result.strategy_wins, fn {k, v} -> {inspect(k), v} end),
      assisted_problems:
        for(
          %{external_assist: %{} = assist} = s <- result.thm_solved,
          do: %{problem: s.problem, prover: assist.prover}
        )
    }
  end
end
