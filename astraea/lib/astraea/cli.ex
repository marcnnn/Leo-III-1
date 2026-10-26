defmodule Astraea.CLI do
  @moduledoc """
  Leo-III compatible command line, after `leo.Main`, `leo.Configuration` and
  `leo.modules.input.CLParameterParser`:

      astraea problem.p [-t 60] [-p] [-n cores] [--atp e=/path/to/eprover] ...

  Prints `% SZS status <Status> for <problem>` and, with `-p`, the TSTP refutation
  (`Astraea.Tstp`) in an `SZS output` block. Like Leo-III the exit code is 0 for
  every answer, including errors, which are reported as SZS statuses
  (`InputError`, `UsageError`, `Error`); a SIGTERM prints `Forced`.

  The problem runs through the time-sliced strategy schedule
  (`Astraea.Schedule`). External provers given with `--atp name=path` cooperate
  inside every strategy as in Leo-III (`--atp-call-interval`, `--atp-timeout`,
  `--atp-args`); with `--atp-race` they additionally race on the original problem
  in the first slice. Theorem/Unsatisfiable is only printed for LCF-verified proofs,
  unless `--trust-external` accepts external answers that could not be
  reconstructed.

  Options follow `CLParameterParser`: `-x value`, `--long value` or switches,
  repeated options accumulate, and the first non-option argument is the problem.
  """

  alias Astraea.{Portfolio, Schedule, TptpLower, Tstp}

  @version Mix.Project.config()[:version]

  @default_timeout_s 60
  @default_atp_timeout_s 15

  # Leo-III names of external provers (`TPTPProvers`) mapped to Astraea's specs.
  @atp_aliases %{
    "e" => :eprover,
    "eprover" => :eprover,
    "eprover-ho" => :eprover_ho,
    "ehoh" => :eprover_ho,
    "vampire" => :vampire,
    "cvc5" => :cvc5,
    "zipperposition" => :zipperposition,
    "iprover" => :iprover,
    "satallax" => :satallax,
    "leo3" => :leo3,
    "leo2" => :leo2,
    "leo" => :leo2
  }

  # Leo-III strategy parameters passed through to every strategy (see
  # `Astraea.Schedule`), with their value parser.
  @strategy_flags %{
    "primsubst" => {:primsubst_level, :integer},
    "unidepth" => {:unification_depth, :integer},
    "unifiers" => {:unifier_count, :integer},
    "matchingdepth" => {:matching_depth, :integer},
    "sos" => {:sos, :switch},
    "funcspec" => {:funcspec, :switch},
    "nochoice" => {:choice, :negated_switch},
    "restrict-uni-attempts" => {:restrict_uni_attempts, :boolean}
  }

  @switches ~w(p s h sos funcspec nochoice noaxiomselection consistency-only atp-race
               trust-external version usage help)

  # Accepted for compatibility; Astraea has no counterpart, so they are ignored.
  @ignored_flags ~w(v relevancefiltering passmark aging instantiate instantiate-maxdepth
                    renaming xType parSched encode-threaded guided embedding-param seq par
                    scheduled-run compressProof print-signature print-clauses atp-max-jobs ll)

  @usage """
  Astraea -- a higher-order theorem prover with LCF-verified proofs (Leo-III compatible CLI).

  Usage: astraea problem [option ...]

  Options:
  -t <timeout>
  \tTimeout in seconds (default: 60)
  -p
  \tDisplay proof output (default: false)
  -n <N>
  \tNumber of strategies run in parallel (default: number of cores)
  -s, --sos
  \tEnable set-of-support search strategy (default: false)
  -a name=call, --atp name=call
  \tAddition of external provers (default: none)
  -e name=N, --atp-timeout name=N
  \tTimeout for an external prover in seconds (default: 15)
  -x name="args", --atp-args name="args"
  \tArguments directly passed to the external prover
  --atp-call-interval <N>
  \tIterations between external prover calls
  --atp-race
  \tAlso race the external provers on the original problem
  --trust-external
  \tReport external answers even if they cannot be reconstructed as LCF proofs
  --primsubst <N>, --unidepth <N>, --unifiers <N>, --funcspec, --nochoice
  \tCalculus parameters, passed to every strategy
  --strategies s1,s2,...
  \tRun only the named strategies (Leo-III or Astraea names)
  --noaxiomselection
  \tDisable SInE axiom selection
  --consistency-only
  \tIgnore the conjecture and check the consistency of the axioms
  --version
  \tPrint the version
  -h, --usage
  \tDisplay this help message
  """

  @doc """
  Escript / release entry point: runs `run/1` and halts with its exit code.
  """
  @spec main([String.t()]) :: no_return()
  def main(argv) do
    {:ok, _apps} = Application.ensure_all_started(:astraea)
    System.halt(run(argv))
  end

  @doc """
  Runs the command line `argv`, printing to stdout, and returns the exit code.
  """
  @spec run([String.t()]) :: non_neg_integer()
  def run(argv) do
    t0 = System.monotonic_time(:millisecond)
    params = parse(argv)

    cond do
      Map.has_key?(params, "version") or params[:problem] == "--version" ->
        IO.puts("Astraea #{@version}")

      Map.has_key?(params, "h") or Map.has_key?(params, "usage") or Map.has_key?(params, "help") ->
        IO.write(@usage)

      params[:problem] == nil ->
        IO.puts(Tstp.status_line(:usage_error, "<unknown>", "No problem file given"))
        IO.puts("")
        IO.write(@usage)

      true ->
        prove(params, t0)
    end

    0
  end

  @doc """
  Parses `argv` like Leo-III's `CLParameterParser` into a map from option names
  (without dashes) to lists of values, plus `:problem` (the first argument that is
  no option) and `:rest` (further arguments). Combined short switches (`-ps`) are
  split.
  """
  @spec parse([String.t()]) :: map()
  def parse(argv), do: parse(argv, %{problem: nil, rest: []})

  defp parse([], acc), do: %{acc | rest: Enum.reverse(acc.rest)}

  defp parse(["--" <> long | tail], acc) when long != "", do: option(long, tail, acc)

  defp parse(["-" <> short | tail], acc) when byte_size(short) == 1, do: option(short, tail, acc)

  defp parse(["-" <> shorts | tail], acc) when byte_size(shorts) > 1 do
    parse(Enum.map(String.graphemes(shorts), &("-" <> &1)) ++ tail, acc)
  end

  defp parse([arg | tail], %{problem: nil} = acc), do: parse(tail, %{acc | problem: arg})
  defp parse([arg | tail], acc), do: parse(tail, %{acc | rest: [arg | acc.rest]})

  # Switches never take a value, so `-p problem.p` keeps the problem.
  defp option(key, [value | tail], acc) do
    if key in @switches or String.starts_with?(value, "-"),
      do: parse([value | tail], Map.put_new(acc, key, [])),
      else: parse(tail, Map.update(acc, key, [value], &(&1 ++ [value])))
  end

  defp option(key, [], acc), do: parse([], Map.put_new(acc, key, []))

  # ---------------------------------------------------------------------------
  # Proving
  # ---------------------------------------------------------------------------

  defp prove(params, t0) do
    problem = params.problem
    trap_sigterm(problem)

    with {:ok, config} <- config(params),
         {:ok, lowered} <- lower(problem, config) do
      lowered = if config.consistency_only, do: drop_conjectures(lowered), else: lowered
      elapsed = System.monotonic_time(:millisecond) - t0
      budget = max(config.timeout_ms - elapsed - reserve_ms(config.timeout_ms), 100)

      result = Schedule.prove_lowered(lowered, Keyword.put(config.opts, :timeout_ms, budget))
      report(result, lowered, problem, config, t0)
    else
      {:error, status, message} ->
        IO.puts(Tstp.status_line(status, problem, message))
    end
  end

  # Time kept back for proof compression, the ContradictoryAxioms check and output.
  defp reserve_ms(timeout_ms), do: min(1_000, div(timeout_ms, 10))

  defp lower(problem, config) do
    cond do
      not File.regular?(problem) ->
        {:error, :input_error, "Problem file not found: #{problem}"}

      true ->
        case TptpLower.from_file(problem, tptp_root: config.tptp_root) do
          {:ok, lowered} -> {:ok, lowered}
          {:error, reason} -> {:error, :input_error, inspect(reason, limit: 5)}
        end
    end
  rescue
    e -> {:error, :input_error, Exception.message(e)}
  end

  defp drop_conjectures(lowered) do
    axioms = Enum.reject(lowered.axioms, fn {_name, role, _t} -> role == "negated_conjecture" end)
    %{lowered | conjectures: [], axioms: axioms}
  end

  defp report(result, lowered, problem, config, t0) do
    status = status(result, config)
    time = System.monotonic_time(:millisecond) - t0

    if strategy = winning_strategy(result),
      do: IO.puts("% Solved by strategy #{inspect(strategy)}")

    IO.puts("% Time passed: #{time}ms")
    IO.puts(Tstp.status_line(status, problem, "#{time} ms"))

    case result do
      {:proved, steps, stats} when config.proof ->
        IO.puts("% No. of inferences in proof: #{length(steps)}")

        derivation =
          Tstp.derivation(lowered, steps, stats,
            problem: problem,
            problem_path: problem,
            tptp_root: config.tptp_root
          )

        IO.write(Tstp.output_block("CNFRefutation", problem, derivation))

      _ ->
        :ok
    end
  end

  # Unverified external refutations are only reported with `--trust-external`.
  defp status({:proved_external, _stats} = result, %{trust_external: true}),
    do: Portfolio.szs_status(result)

  defp status({:proved_external, _stats}, _config), do: :gave_up
  defp status(result, _config), do: Portfolio.szs_status(result)

  defp winning_strategy({:proved, _steps, stats}), do: stats[:winning_strategy]

  defp winning_strategy({tag, stats}) when is_map(stats) and tag != :error,
    do: stats[:winning_strategy]

  defp winning_strategy(_result), do: nil

  # ---------------------------------------------------------------------------
  # Configuration
  # ---------------------------------------------------------------------------

  defp config(params) do
    with {:ok, timeout_s} <- int(params, "t", @default_timeout_s),
         {:ok, cores} <- int(params, "n", System.schedulers_online()),
         {:ok, interval} <- int(params, "atp-call-interval", nil),
         {:ok, overrides} <- strategy_overrides(params),
         {:ok, strategies} <- strategies(params) do
      warn_ignored(params)
      atps = atps(params)
      timeout_ms = if timeout_s == 0, do: 86_400_000, else: timeout_s * 1_000

      overrides =
        if Map.has_key?(params, "noaxiomselection"),
          do: Keyword.put(overrides, :sine_limit, nil),
          else: overrides

      opts =
        [
          cores: max(cores, 1),
          strategy_overrides: overrides,
          tptp_root: tptp_root(),
          problem_path: params.problem,
          trust_external: Map.has_key?(params, "trust-external")
        ]
        |> put_if(:schedule_strategies, strategies)
        |> put_if(:cooperate, if(atps != [], do: atps))
        |> put_if(:cooperate_interval, interval)
        |> put_if(:external, if(atps != [] and Map.has_key?(params, "atp-race"), do: atps))

      {:ok,
       %{
         opts: opts,
         timeout_ms: timeout_ms,
         proof: Map.has_key?(params, "p"),
         trust_external: Keyword.fetch!(opts, :trust_external),
         consistency_only: Map.has_key?(params, "consistency-only"),
         tptp_root: Keyword.fetch!(opts, :tptp_root)
       }}
    end
  end

  defp tptp_root, do: Astraea.TptpCorpus.default_tptp_root()

  defp int(params, key, default) do
    case Map.get(params, key) do
      nil ->
        {:ok, default}

      [value | _] ->
        case Integer.parse(value) do
          {n, ""} when n >= 0 ->
            {:ok, n}

          _ ->
            {:error, :usage_error, "Option -#{key} expects a non-negative integer, got #{value}"}
        end

      [] ->
        {:error, :usage_error, "Option -#{key} expects a value"}
    end
  end

  defp strategy_overrides(params) do
    params = if Map.has_key?(params, "s"), do: Map.put_new(params, "sos", []), else: params

    Enum.reduce_while(@strategy_flags, {:ok, []}, fn {flag, {opt, kind}}, {:ok, acc} ->
      case {kind, Map.get(params, flag)} do
        {_kind, nil} ->
          {:cont, {:ok, acc}}

        {:switch, _} ->
          {:cont, {:ok, Keyword.put(acc, opt, true)}}

        {:negated_switch, _} ->
          {:cont, {:ok, Keyword.put(acc, opt, false)}}

        {:boolean, [value | _]} ->
          {:cont, {:ok, Keyword.put(acc, opt, value not in ["false", "0"])}}

        {:boolean, []} ->
          {:cont, {:ok, Keyword.put(acc, opt, true)}}

        {:integer, _} ->
          case int(params, flag, nil) do
            {:ok, n} -> {:cont, {:ok, Keyword.put(acc, opt, n)}}
            err -> {:halt, err}
          end
      end
    end)
  end

  # `--strategies s1,s3b,goal_standard` selects strategies of the default list by name.
  defp strategies(params) do
    case Map.get(params, "strategies") do
      nil ->
        {:ok, nil}

      values ->
        known = Map.new(Schedule.strategies(), &{Atom.to_string(&1.name), &1})
        names = values |> Enum.flat_map(&String.split(&1, ",", trim: true))

        case Enum.reject(names, &Map.has_key?(known, &1)) do
          [] -> {:ok, Enum.map(names, &Map.fetch!(known, &1))}
          unknown -> {:error, :usage_error, "Unknown strategies: #{Enum.join(unknown, ", ")}"}
        end
    end
  end

  # `--atp name=call` (or `-a`), with `--atp-timeout name=N` (`-e`) and
  # `--atp-args name="args"` (`-x`), as in Leo-III's `Configuration.ATPS`.
  defp atps(params) do
    timeouts = pairs(params, ["e", "atp-timeout", "atp-timout"])
    args = pairs(params, ["x", "atp-args"])

    params
    |> values(["a", "atp"])
    |> Enum.flat_map(fn spec ->
      {name, call} =
        case String.split(spec, "=", parts: 2) do
          [name, call] -> {name, call}
          [name] -> {name, ""}
        end

      case Map.fetch(@atp_aliases, String.downcase(name)) do
        {:ok, prover} ->
          timeout_s =
            case Integer.parse(Map.get(timeouts, name, "")) do
              {n, ""} when n > 0 -> n
              _ -> @default_atp_timeout_s
            end

          [
            {prover,
             [timeout_ms: timeout_s * 1_000]
             |> put_if(:path, if(call != "", do: call))
             |> put_if(:extra_args, if(args[name], do: OptionParser.split(args[name])))}
          ]

        :error ->
          warn("Unknown external prover '#{name}' ignored (known: #{known_atps()})")
          []
      end
    end)
  end

  defp known_atps, do: @atp_aliases |> Map.keys() |> Enum.sort() |> Enum.join(", ")

  defp values(params, keys), do: Enum.flat_map(keys, &Map.get(params, &1, []))

  defp pairs(params, keys) do
    params
    |> values(keys)
    |> Enum.flat_map(fn pair ->
      case String.split(pair, "=", parts: 2) do
        [name, value] -> [{name, value}]
        _ -> []
      end
    end)
    |> Map.new()
  end

  defp warn_ignored(params) do
    known =
      ~w(t p n s h a e x atp atp-timeout atp-timout atp-args atp-call-interval atp-race
         trust-external strategies noaxiomselection consistency-only version usage help) ++
        Map.keys(@strategy_flags)

    for key <- Map.keys(params), is_binary(key), key not in known do
      if key in @ignored_flags,
        do: warn("Option '#{key}' is not supported by Astraea and ignored"),
        else: warn("Unknown option '#{key}' ignored")
    end

    for arg <- params.rest, do: warn("Extra argument '#{arg}' ignored")
  end

  defp warn(message), do: IO.puts("% Warning: #{message}")

  defp put_if(opts, _key, nil), do: opts
  defp put_if(opts, key, value), do: Keyword.put(opts, key, value)

  # ---------------------------------------------------------------------------
  # SIGTERM
  # ---------------------------------------------------------------------------

  # Like Leo-III's shutdown hook: a SIGTERM (e.g. from StarExec's or CASC's
  # wall-clock limit) prints `SZS status Forced` before the VM stops.
  defp trap_sigterm(problem) do
    if Process.whereis(:erl_signal_server) do
      :os.set_signal(:sigterm, :handle)

      :gen_event.swap_handler(
        :erl_signal_server,
        {:erl_signal_handler, []},
        {Astraea.CLI.SignalHandler, problem}
      )
    end

    :ok
  end

  defmodule SignalHandler do
    @moduledoc false
    @behaviour :gen_event

    @impl true
    def init({problem, _swap}), do: {:ok, problem}
    def init(problem), do: {:ok, problem}

    @impl true
    def handle_event(:sigterm, problem) do
      IO.puts(Astraea.Tstp.status_line(:forced, problem, "Astraea stopped externally."))
      System.halt(0)
      {:ok, problem}
    end

    def handle_event(_signal, problem), do: {:ok, problem}

    @impl true
    def handle_call(_request, problem), do: {:ok, :ok, problem}
  end
end
