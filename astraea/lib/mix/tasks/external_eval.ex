defmodule Mix.Tasks.External.Eval do
  @moduledoc """
  Evaluates external prover integration on a TPTP split by comparing portfolio
  configurations under the same timeout and concurrency:

    1. `baseline` - internal strategies only
    2. `racers` - plus installed external provers racing on the original problem,
       with unsat-core reconstruction (`Astraea.External.Reconstruct`)
    3. `cooperate` - internal strategies with mid-search cooperation, sending the
       clause set to E (THF to `eprover-ho` if installed, else TFF to `eprover`)

  Options: `--split smoke|dev|holdout` (default `smoke`), `--timeout` ms per problem
  (default 2500), `--concurrency` problems in parallel (default 3),
  `--configs` comma-separated subset, `--out` JSON report path.

      mix external.eval --split dev --timeout 5000 --out /tmp/external_dev.json
  """
  use Mix.Task

  alias Astraea.External.Provers
  alias Astraea.Portfolio

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
          out: :string
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

    report =
      Map.new(configs, fn {name, extra_opts} ->
        t0 = System.monotonic_time(:millisecond)

        result =
          Portfolio.evaluate_split(
            split,
            [timeout_ms: timeout_ms, max_concurrency: concurrency] ++ extra_opts
          )

        summary = summarize(result, System.monotonic_time(:millisecond) - t0)
        Mix.shell().info("#{name}: #{inspect(Map.drop(summary, [:assisted_problems]))}")
        {name, summary}
      end)

    if out = Keyword.get(opts, :out) do
      File.write!(out, Jason.encode!(report, pretty: true))
      Mix.shell().info("report written to #{out}")
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

    [
      {"baseline", []},
      {"racers", [external: racers]},
      {"cooperate", [cooperate: cooperate, cooperate_interval: 30]}
    ]
  end

  defp filter_configs(configs, nil), do: configs

  defp filter_configs(configs, names) do
    wanted = String.split(names, ",", trim: true)
    Enum.filter(configs, fn {name, _} -> name in wanted end)
  end

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
