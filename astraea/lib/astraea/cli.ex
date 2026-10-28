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

  # Leo-III calculus flags applied to every strategy, as `Astraea.Prover` options
  # (see `Astraea.Schedule`), with their value parser.
  @strategy_flags %{
    "primsubst" => {:prim_subst, :integer},
    "unidepth" => {:unify_depth, :integer},
    "unifiers" => {:unifier_count, :integer},
    "matchingdepth" => {:matching_depth, :integer},
    "sos" => {:sos, :switch},
    "funcspec" => {:funcspec, :switch},
    "nochoice" => {:choice, :negated_switch},
    "restrict-uni-attempts" => {:flex_resolution, :restricted},
    "nleq" => {:leibniz_eq, :negated_switch},
    "naeq" => {:andrews_eq, :negated_switch},
    "acsimp" => {:ac_simp, :switch},
    "instantiate-sets" => {:instantiate_sets, :switch},
    "instantiate" => {:instantiate, :level},
    "instantiate-maxdepth" => {:instantiate_max_depth, :integer},
    "renaming" => {:renaming, :renaming},
    "ordering" => {:term_ordering, :ordering},
    "sine" => {:sine, :sine},
    "standard-sine" => {:standard_sine, :switch},
    "subsumption" => {:subsumption, :subsumption},
    "noOrdCheck1" => {:no_ord_check, {:ord_check, 1}},
    "noOrdCheck2" => {:no_ord_check, {:ord_check, 2}},
    "noOrdCheck3" => {:no_ord_check, {:ord_check, 3}}
  }

  @switches ~w(p s h sos funcspec nochoice noaxiomselection consistency-only atp-race
               trust-external version usage help nleq naeq acsimp instantiate-sets
               relevancefiltering processOnly cnf xLocal toTHF syntaxcheck typecheck seq
               scheduled compressProof print-signature print-clauses overlord guided encode-threaded
               standard-sine noOrdCheck1 noOrdCheck2 noOrdCheck3 no-default-types DEBUG
               atpdebug)

  # Leo-III modes that print something other than a proof attempt (`leo.modules.Modes`).
  @modes ~w(processOnly toTHF syntaxcheck typecheck)

  # Accepted for compatibility without effect: `parSched` and `encode-threaded` are
  # read by no Leo-III code, `compressProof` is Astraea's default (`Astraea.Compressor`),
  # `overlord` keeps temporary files that Astraea never deletes early, and `par` and
  # `scheduled-run` select modes that are Astraea's default (the parallel schedule).
  @ignored_flags ~w(parSched encode-threaded compressProof overlord ll par scheduled-run)

  # Leo-III verbosity levels 0-6 (`Configuration.VERBOSITY`) as `Logger` levels.
  @verbosity %{
    0 => :none,
    1 => :error,
    2 => :warning,
    3 => :notice,
    4 => :info,
    5 => :debug,
    6 => :debug
  }

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
  --strategies s1,s2,..., --strategy s1
  \tRun only the named strategies (Leo-III or Astraea names)
  --noaxiomselection
  \tDisable SInE axiom selection
  --relevancefiltering [--passmark <x>] [--aging <x>]
  \tLeo-III's relevance filter instead of SInE (defaults 0.56, 2.35)
  --renaming <true|false|N>
  \tFormula renaming in the CNF, N is the threshold (default: per strategy)
  --ordering <CPO|KBO|none>
  \tTerm ordering of every strategy (default: per strategy)
  --nleq, --naeq
  \tDo not replace Leibniz / Andrews equalities
  --acsimp
  \tSimplify modulo associativity and commutativity
  --instantiate <N>, --instantiate-maxdepth <N>, --instantiate-sets
  \tInstantiate input clauses (special instances, sets of properties)
  --lambda-elim <ski|lambda-lifting>
  \tLambda elimination for first-order external provers (default: lambda-lifting)
  --atp-max-jobs <N>
  \tExternal prover calls running at once per strategy (default: 2)
  --seq
  \tRun Leo-III's default strategy only, instead of the schedule
  --processOnly [--cnf] [--renaming N] [--xType N] [--xLocal]
  \tPrint the normalized problem instead of proving it
  --toTHF, --syntaxcheck, --typecheck
  \tPrint the problem as THF, or only check its syntax / types
  --print-signature, --print-clauses
  \tPrint the signature of the problem / the processed clauses after the result
  --sine [<threshold;size;depth>], --standard-sine
  \tLeo-III's SInE selection (configuration guessed from the axiom counts, or given)
  --subsumption <ho-pattern|trivial>
  \tSubsumption by matching (default) or by literal inclusion only
  --embedding-param <P>
  \tModal embedding parameter (e.g. MODALITIES_SYNTACTICAL), repeatable
  --guided
  \tInteractive given-clause loop on stdin (Leo-III commands, "exit" continues)
  -v <0-6>
  \tVerbosity of log messages (default: 3)
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
    # The time limit includes booting the VM, as with Leo-III's JVM.
    {vm_uptime_ms, _} = :erlang.statistics(:wall_clock)
    started = System.monotonic_time(:millisecond) - vm_uptime_ms
    {:ok, _apps} = Application.ensure_all_started(:astraea)
    System.halt(run(argv, started))
  end

  @doc """
  Runs the command line `argv`, printing to stdout, and returns the exit code.
  The time limit counts from `t0` (`System.monotonic_time(:millisecond)`).
  """
  @spec run([String.t()], integer()) :: non_neg_integer()
  def run(argv, t0 \\ System.monotonic_time(:millisecond)) do
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

      mode = Enum.find(@modes, &Map.has_key?(params, &1)) ->
        run_mode(mode, params)

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
      if config.print_signature, do: print_signature(lowered)
      if config.print_clauses, do: print_clauses(result)
    else
      {:error, status, message} ->
        IO.puts(Tstp.status_line(status, problem, message))
    end
  end

  # ---------------------------------------------------------------------------
  # Modes
  # ---------------------------------------------------------------------------

  defp run_mode(mode, params) do
    problem = params.problem

    with {:ok, embedding_params} <- embedding_params(params),
         {:ok, lowered} <-
           lower(problem, %{
             tptp_root: tptp_root(),
             embedding_params: embedding_params,
             default_types: not Map.has_key?(params, "no-default-types")
           }) do
      case mode do
        "processOnly" ->
          case Astraea.Normalization.normalize_lowered(lowered, normalization_opts(params)) do
            {:ok, text} -> IO.write(text)
            {:error, reason} -> IO.puts(Tstp.status_line(:error, problem, inspect(reason)))
          end

        "toTHF" ->
          IO.puts(Tstp.status_line(:success, problem))
          IO.write(Tstp.output_block("ListOfTHF", problem, Astraea.Normalization.to_thf(lowered)))

        _check ->
          IO.puts(Tstp.status_line(:success, problem))
      end
    else
      {:error, status, message} -> IO.puts(Tstp.status_line(status, problem, message))
    end
  end

  # `--cnf`, `--renaming N`, `--xType N`, `--xLocal` (Leo-III `modes.Normalization`).
  defp normalization_opts(params) do
    renaming =
      case Map.get(params, "renaming") do
        ["false" | _] -> false
        [n | _] -> parse_int(n, 0)
        _ -> 0
      end

    [
      cnf: Map.has_key?(params, "cnf"),
      renaming: renaming,
      extraction: parse_int(List.first(Map.get(params, "xType", [])), 1),
      extract_local: Map.has_key?(params, "xLocal")
    ]
  end

  defp parse_int(nil, default), do: default

  defp parse_int(value, default) do
    case Integer.parse(value) do
      {n, ""} -> n
      _ -> default
    end
  end

  # Leo-III `--DEBUG`: the proof as internal clauses (`id: clause <- rule(parents)`)
  # instead of a TSTP derivation.
  defp print_debug_proof(steps, stats) do
    {:ok, _arena, derived} = Astraea.ProofChecker.derive_steps(stats.arena, steps)

    for step <- steps do
      id = elem(step, 1)
      clause = Astraea.External.ThfPrinter.clause_to_string(stats.arena, Map.fetch!(derived, id))
      parents = Astraea.ProofChecker.step_parents(step)
      IO.puts("% #{id}: #{clause} <- #{elem(step, 0)}(#{Enum.join(parents, ", ")})")
    end
  end

  # Leo-III `--print-clauses`: the processed clauses of the strategy that answered.
  defp print_clauses(result) do
    stats =
      case result do
        {:proved, _steps, stats} -> stats
        {_tag, stats} when is_map(stats) -> stats
        _ -> %{}
      end

    case stats do
      %{arena: arena, final_clauses: clauses} ->
        IO.puts("% Processed clauses at termination:")

        for c <- Enum.sort_by(clauses, &MapSet.size/1),
            do: IO.puts("%   " <> Astraea.External.ThfPrinter.clause_to_string(arena, c))

      _ ->
        IO.puts("% Processed clauses at termination: not available")
    end
  end

  # Leo-III `--print-signature`: the user symbols of the problem with their types.
  defp print_signature(lowered) do
    arena = lowered.arena

    symbols =
      for {_id, node} <- arena.nodes,
          {1, _, ty, sym, _} <- [Astraea.Arena.decode_node(node)],
          name = Map.get(arena.symbol_names, sym, ""),
          not String.starts_with?(name, "$"),
          uniq: true,
          do: {name, ty}

    IO.puts("% Signature:")

    for {name, ty} <- Enum.sort(symbols),
        do: IO.puts("%   #{name}: #{Astraea.External.ThfPrinter.type(arena, ty)}")
  end

  # Time kept back for proof compression, the ContradictoryAxioms check and output.
  defp reserve_ms(timeout_ms), do: min(1_000, div(timeout_ms, 10))

  defp lower(problem, config) do
    cond do
      not File.regular?(problem) ->
        {:error, :input_error, "Problem file not found: #{problem}"}

      true ->
        case TptpLower.from_file(problem,
               tptp_root: config.tptp_root,
               embedding_params: Map.get(config, :embedding_params, []),
               default_types: Map.get(config, :default_types, true)
             ) do
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
      {:proved, steps, stats} when config.proof and config.debug ->
        IO.puts("% No. of inferences in proof: #{length(steps)}")
        print_debug_proof(steps, stats)

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
  defp status({:resource_out, %{guided: :killed}}, _config), do: :user
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
         {:ok, max_jobs} <- int(params, "atp-max-jobs", nil),
         {:ok, verbosity} <- int(params, "v", nil),
         {:ok, overrides} <- strategy_overrides(params),
         {:ok, overrides} <- relevance_filter(params, overrides),
         {:ok, encoding} <- encoding(params),
         {:ok, embedding_params} <- embedding_params(params),
         {:ok, strategies} <- strategies(params) do
      warn_ignored(params)
      if verbosity, do: Logger.configure(level: Map.get(@verbosity, min(verbosity, 6)))
      atps = atps(params, encoding)
      guided = Map.has_key?(params, "guided")

      # Like Leo-III, guided runs ignore the time limit.
      timeout_ms = if timeout_s == 0 or guided, do: 86_400_000, else: timeout_s * 1_000

      # `NoAxiomFilter` wins over every selection (Leo-III `getBestFilterConfig`).
      overrides =
        if Map.has_key?(params, "noaxiomselection"),
          do: Keyword.merge(overrides, sine_limit: nil, sine: nil, relevance_filter: nil),
          else: overrides

      overrides =
        overrides
        |> put_if(:guided, if(guided, do: true))
        |> put_if(:keep_clauses, if(Map.has_key?(params, "print-clauses"), do: true))

      opts =
        [
          cores: if(guided, do: 1, else: max(cores, 1)),
          strategy_overrides: overrides,
          tptp_root: tptp_root(),
          problem_path: params.problem,
          trust_external: Map.has_key?(params, "trust-external")
        ]
        |> put_if(:schedule_strategies, strategies || seq_strategy(params, guided))
        |> put_if(:cooperate, if(atps != [], do: atps))
        |> put_if(:cooperate_interval, interval)
        |> put_if(:cooperate_max_jobs, max_jobs)
        |> put_if(:external, if(atps != [] and Map.has_key?(params, "atp-race"), do: atps))

      {:ok,
       %{
         opts: opts,
         timeout_ms: timeout_ms,
         proof: Map.has_key?(params, "p"),
         trust_external: Keyword.fetch!(opts, :trust_external),
         consistency_only: Map.has_key?(params, "consistency-only"),
         print_signature: Map.has_key?(params, "print-signature"),
         print_clauses: Map.has_key?(params, "print-clauses"),
         debug: Map.has_key?(params, "DEBUG"),
         embedding_params: embedding_params,
         default_types: not Map.has_key?(params, "no-default-types"),
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

        {:restricted, values} ->
          restricted? = values == [] or hd(values) not in ["false", "0"]
          {:cont, {:ok, Keyword.put(acc, opt, if(restricted?, do: :ground, else: :all))}}

        {:integer, _} ->
          case int(params, flag, nil) do
            {:ok, n} -> {:cont, {:ok, Keyword.put(acc, opt, n)}}
            err -> {:halt, err}
          end

        # Leo-III's level is a bit set of primitive substitutions; 0 turns it off.
        {:level, values} ->
          {:cont, {:ok, Keyword.put(acc, opt, values == [] or hd(values) != "0")}}

        # `true`/`false`, or a number: renaming on with that threshold.
        {:renaming, values} ->
          case values do
            ["false" | _] ->
              {:cont, {:ok, Keyword.put(acc, :renaming, false)}}

            [n | _] when n != "true" ->
              case int(params, flag, nil) do
                {:ok, n} ->
                  {:cont,
                   {:ok,
                    acc |> Keyword.put(:renaming, true) |> Keyword.put(:renaming_threshold, n)}}

                err ->
                  {:halt, err}
              end

            _ ->
              {:cont, {:ok, Keyword.put(acc, :renaming, true)}}
          end

        {:ordering, [value | _]} ->
          case String.downcase(value) do
            "cpo" ->
              {:cont, {:ok, acc ++ [ordered: true, term_ordering: :cpo]}}

            kbo when kbo in ["kbo", "hkbo"] ->
              {:cont, {:ok, acc ++ [ordered: true, term_ordering: :kbo]}}

            "none" ->
              {:cont, {:ok, Keyword.put(acc, :ordered, false)}}

            _ ->
              {:halt, {:error, :usage_error, "Unknown term ordering #{value} (CPO, KBO, none)"}}
          end

        {:ordering, []} ->
          {:halt, {:error, :usage_error, "Option -#{flag} expects a value"}}

        # `--sine "threshold;size;depth"`; without a value (or an unparsable one) the
        # configuration is guessed as in Leo-III (`Astraea.Sine`).
        {:sine, values} ->
          {:cont, {:ok, Keyword.put(acc, opt, List.first(values) || :auto)}}

        {{:ord_check, n}, _} ->
          {:cont, {:ok, Keyword.update(acc, opt, [n], &Enum.uniq([n | &1]))}}

        # Leo-III falls back to its default for unknown methods.
        {:subsumption, values} ->
          method = if List.first(values) == "trivial", do: :trivial, else: :matching
          {:cont, {:ok, Keyword.put(acc, opt, method)}}
      end
    end)
  end

  # `--relevancefiltering` with `--passmark`/`--aging` (also `--relevance-passmark`,
  # `--relevance-aging`), see `Astraea.RelevanceFilter`.
  defp relevance_filter(params, overrides) do
    keys = [
      {:passmark, ["passmark", "relevance-passmark"]},
      {:aging, ["aging", "relevance-aging"]}
    ]

    given? =
      Map.has_key?(params, "relevancefiltering") or
        Enum.any?(keys, fn {_, names} -> values(params, names) != [] end)

    Enum.reduce_while(keys, {:ok, %{}}, fn {key, names}, {:ok, acc} ->
      case values(params, names) do
        [] ->
          {:cont, {:ok, acc}}

        [value | _] ->
          case Float.parse(value) do
            {x, ""} when x >= 0 ->
              {:cont, {:ok, Map.put(acc, key, x)}}

            _ ->
              {:halt,
               {:error, :usage_error, "Option -#{hd(names)} expects a number, got #{value}"}}
          end
      end
    end)
    |> case do
      {:ok, filter} when given? -> {:ok, Keyword.put(overrides, :relevance_filter, filter)}
      {:ok, _} -> {:ok, overrides}
      err -> err
    end
  end

  # `--embedding-param P` (repeatable, Leo-III `EMBEDDING_PARAMS`), see `Astraea.Input.Modal`.
  defp embedding_params(params) do
    values = params |> Map.get("embedding-param", []) |> Enum.flat_map(&String.split(&1, ","))

    case Astraea.Input.Modal.parse_params(values) do
      {:ok, _} ->
        {:ok, values}

      {:error, {:unknown_embedding_param, name}} ->
        {:error, :usage_error,
         "Unknown embedding parameter #{name} (known: #{Enum.join(Astraea.Input.Modal.param_names(), ", ")})"}
    end
  end

  # `--lambda-elim` (Leo-III `LAMBDA_ELIM_STRATEGY`) for the external provers.
  defp encoding(params) do
    case Map.get(params, "lambda-elim") do
      nil -> {:ok, nil}
      ["ski" | _] -> {:ok, [lambda: :ski]}
      ["lambda-lifting" | _] -> {:ok, [lambda: :lambda_lifting]}
      _ -> {:error, :usage_error, "Option -lambda-elim expects ski or lambda-lifting"}
    end
  end

  # `--seq` (and `--guided`, which asks on stdin): Leo-III's sequential loop with
  # its default strategy.
  defp seq_strategy(params, guided) do
    if guided or Map.has_key?(params, "seq"),
      do: Enum.filter(Schedule.strategies(), &(&1.name == :default))
  end

  # `--strategies s1,s3b,goal_standard` selects strategies of the default list by name;
  # Leo-III's `--strategy s1` (one `RunStrategy` for its sequential loop) is the same
  # with a single name.
  defp strategies(params) do
    case values(params, ["strategies", "strategy"]) do
      [] ->
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
  defp atps(params, encoding) do
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
             |> put_if(:extra_args, if(args[name], do: OptionParser.split(args[name])))
             |> put_if(:encoding, encoding)
             |> put_if(:debug, if(Map.has_key?(params, "atpdebug"), do: true))}
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
      ~w(t p n s h a e x v atp atp-timeout atp-timout atp-args atp-call-interval atp-race
         atp-max-jobs trust-external strategies noaxiomselection consistency-only version
         strategy usage help relevancefiltering passmark aging relevance-passmark relevance-aging
         lambda-elim seq scheduled print-signature print-clauses cnf xType xLocal
         embedding-param guided noOrdCheck1 noOrdCheck2 noOrdCheck3 no-default-types DEBUG
         atpdebug) ++
        @modes ++ Map.keys(@strategy_flags)

    for key <- Map.keys(params), is_binary(key), key not in known do
      if key in @ignored_flags,
        do: warn("Option '#{key}' has no effect in Astraea"),
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
