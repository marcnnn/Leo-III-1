defmodule Astraea.Schedule do
  @moduledoc """
  Time-sliced strategy schedule over the OTP portfolio, after Leo-III's
  `ScheduledRun` and `RunStrategy` / `StrategyControl.generateRunStrategies`.

  Leo-III runs its strategies one after another, strategy `s` for
  `share(s) * MINTIME` seconds while the global timeout lasts, and spreads the
  remainder over the strategies that fit. Astraea runs several strategies at once:
  the ordered strategy list is cut into slices of `cores` strategies, each slice
  races as one `Astraea.Portfolio.prove_lowered/2` call, and the next slice starts
  when it ends. A slice's time is `max share * @min_slice_ms`; as in Leo-III the
  slices that fit are kept and the remaining time is distributed over them in
  proportion to their weight, and a single slice that does not fit gets all the
  time left. Strategies often finish early (iteration limits, saturation), so the
  schedule is re-planned before every slice with the time actually remaining.

  Strategies are data (`%{name:, share:, opts:}`). `leo3_strategies/0` holds
  Leo-III's 17 `RunStrategy` definitions, translated by `leo3_opts/1` into the
  calculus options of `Astraea.Prover`:

  | Leo-III `RunStrategy` | Astraea option |
  |---|---|
  | `primSubst` | `:prim_subst` |
  | `unifierCount` | `:unifier_count` |
  | `uniDepth` | `:unify_depth` |
  | `boolExt` | `:ext_inferences` |
  | `choice` | `:choice` |
  | `ordering` | `:ordered` (`false` for Leo-III's `NO_ORDERING`), `:term_ordering` (`:cpo` for `CPO_Naive`) |
  | `restrictUniAttempts` | `:flex_resolution` (`:ground` when restricted, else `:all`) |

  Leo-III parameters without an Astraea counterpart yet (`sos`, `renaming`,
  `funcspec`, `domConstr`, `specialInstances`) are passed through under their
  snake_case names and ignored by the engine.
  """

  alias Astraea.{Portfolio, TptpLower}

  # Leo-III's MINTIME (80 s) scaled to Astraea's shorter strategy runs.
  @min_slice_ms 10_000

  # Leo-III's `Configuration.DEFAULT_UNIFICATIONDEPTH`.
  @leo3_uni_depth 8

  # Iteration limits of the deeper strategies after the first slice.
  @deep_iterations 2_000
  @deeper_iterations 10_000

  @type strategy :: %{name: atom(), share: number(), opts: keyword()}
  @type slice :: %{strategies: [Portfolio.strategy_spec()], timeout_ms: non_neg_integer()}

  @doc """
  Dedicated `:funcspec` strategy definition for function synthesis via choice.
  """
  @spec funcspec_strategy() :: strategy()
  def funcspec_strategy do
    strat = Enum.find(leo3_strategies(), &(&1.name == :funcspec))
    %{name: :funcspec, share: strat.share, opts: leo3_opts(strat.params)}
  end

  @doc """
  Leo-III's 17 `RunStrategy` definitions (`s1` ... `s6`, `funcspec` and the
  `Configuration` defaults as `default`) with their original parameters.
  """
  @spec leo3_strategies() :: [%{name: atom(), share: number(), params: map()}]
  def leo3_strategies do
    # {name, share, primSubst, sos, unifierCount, uniDepth, choice, renaming, funcspec,
    #  domConstr, specialInstances, restrictUniAttempts, ordering}; boolExt is always on
    [
      {:s1, 1, 1, false, 10, @leo3_uni_depth, true, true, false, 0, 18, true, :cpo_naive},
      {:s1unrestricted, 1, 1, false, 10, @leo3_uni_depth, false, true, false, 0, -1, false,
       :none},
      {:s1general, 1, 3, false, 2, @leo3_uni_depth, true, true, false, 0, 0, false, :cpo_naive},
      {:s1a, 1, 1, false, 1, @leo3_uni_depth, false, true, false, 0, 31, true, :cpo_naive},
      {:s1b, 1, 1, false, 1, @leo3_uni_depth, true, false, false, 0, -1, true, :cpo_naive},
      {:s2, 1, 2, false, 3, @leo3_uni_depth, true, true, false, 0, -1, true, :cpo_naive},
      {:s3, 0.5, 1, true, 1, @leo3_uni_depth, true, true, false, 0, -1, true, :cpo_naive},
      {:s3a, 0.5, 1, true, 1, @leo3_uni_depth, false, true, false, 0, -1, true, :cpo_naive},
      {:s3b, 0.5, 3, true, 3, @leo3_uni_depth, true, true, false, 0, -1, true, :cpo_naive},
      {:s3bb, 0.5, 3, true, 3, @leo3_uni_depth, false, false, false, 0, -1, true, :cpo_naive},
      {:s4, 0.25, 3, false, 3, @leo3_uni_depth, true, false, true, 0, -1, true, :cpo_naive},
      {:s5a, 1, 1, false, 1, @leo3_uni_depth, true, true, false, -1, -1, true, :cpo_naive},
      {:s5b, 1, 1, false, 1, @leo3_uni_depth, true, false, false, -1, -1, true, :cpo_naive},
      {:s5c, 0.5, 3, true, 3, @leo3_uni_depth, true, true, false, -1, -1, true, :cpo_naive},
      {:s6, 0.5, 1, false, 1, @leo3_uni_depth, false, true, false, 0, -1, true, :cpo_naive},
      {:funcspec, 0.5, 2, false, 10, @leo3_uni_depth, true, true, true, 0, -1, false, :none},
      {:default, 1, 3, false, 4, @leo3_uni_depth, true, true, false, 0, 39, true, :cpo_naive}
    ]
    |> Enum.map(fn {name, share, prim, sos, unif, depth, choice, renaming, funcspec, dom, special,
                    restrict, ordering} ->
      %{
        name: name,
        share: share,
        params: %{
          prim_subst: prim,
          sos: sos,
          unifier_count: unif,
          uni_depth: depth,
          bool_ext: true,
          choice: choice,
          renaming: renaming,
          funcspec: funcspec,
          dom_constr: dom,
          special_instances: special,
          restrict_uni_attempts: restrict,
          ordering: ordering
        }
      }
    end)
  end

  @doc """
  Translates Leo-III strategy parameters into Astraea options (see the moduledoc).
  """
  @spec leo3_opts(map()) :: keyword()
  def leo3_opts(params) do
    [
      prim_subst: params.prim_subst,
      unifier_count: params.unifier_count,
      unify_depth: params.uni_depth,
      ext_inferences: params.bool_ext,
      choice: params.choice,
      ordered: params.ordering != :none,
      term_ordering: if(params.ordering == :cpo_naive, do: :cpo, else: :kbo),
      flex_resolution: if(params.restrict_uni_attempts, do: :ground, else: :all),
      sos: params.sos,
      renaming: params.renaming,
      funcspec: params.funcspec,
      dom_constr: params.dom_constr,
      special_instances: params.special_instances
    ]
  end

  @doc """
  The default strategy order: Astraea's four portfolio strategies
  (`Astraea.Portfolio.default_strategies/0`), then Leo-III's strategies (in the
  order of Leo-III's preferred `s1, s1a` schedule and its commented-out extension
  `s3bb, s2, s1b, s6, s3b`, then the rest) on rotating Astraea bases with deeper
  iteration limits, then the four portfolio strategies with twice the SInE
  window, negative literal selection, flex paramodulation and the deepest limits.
  A limit-free `:complete_saturation` strategy runs right after the first slice,
  since it is the only one whose saturation can prove a model exists.
  """
  @spec strategies() :: [strategy()]
  def strategies do
    bases = Portfolio.default_strategies()
    leo3 = Map.new(leo3_strategies(), &{&1.name, &1})

    first = Enum.map(bases, fn {name, opts} -> %{name: name, share: 1, opts: opts} end)

    leo3_order =
      [:s1, :s1a, :s3bb, :s2, :s1b, :s6, :s3b] ++
        [:s1general, :s1unrestricted, :s3, :s3a, :s4, :s5a, :s5b, :s5c, :funcspec, :default]

    leo3_derived =
      leo3_order
      |> Enum.zip(Stream.cycle(bases))
      |> Enum.map(fn {name, {_base, base_opts}} ->
        strat = Map.fetch!(leo3[name], :params)

        %{
          name: name,
          share: leo3[name].share,
          opts:
            base_opts
            |> Keyword.merge(leo3_opts(strat))
            |> Keyword.put(:max_iterations, @deep_iterations)
        }
      end)

    deep =
      Enum.map(bases, fn {name, opts} ->
        %{
          name: :"#{name}_deep",
          share: 1,
          opts:
            opts
            |> Keyword.update!(:sine_limit, &(&1 * 2))
            |> Keyword.merge(
              max_iterations: @deeper_iterations,
              literal_selection: :neg_max,
              paramod_flex: true
            )
        }
      end)

    # The only strategy that can find models: without SInE and clause limits, a
    # saturation with `stats.complete` proves CounterSatisfiable/Satisfiable.
    saturate = %{name: :complete_saturation, share: 1, opts: [sine_limit: nil]}

    # FluidSup and stated-induction instances (Pillars 3 and 4).
    extensions =
      for {name, opts} <- Portfolio.wide_strategies(),
          name in [:fluid, :induction],
          do: %{name: name, share: 1, opts: Keyword.put(opts, :max_iterations, @deep_iterations)}

    first ++ [saturate] ++ extensions ++ leo3_derived ++ deep
  end

  @doc """
  Plans the slices for `timeout_ms` on `cores` cores (see the moduledoc). The
  slice times sum to at most `timeout_ms`.
  """
  @spec build(non_neg_integer(), pos_integer(), [strategy()]) :: [slice()]
  def build(timeout_ms, cores, strategies \\ strategies()) when cores >= 1 do
    groups =
      strategies
      |> Enum.chunk_every(cores)
      |> Enum.map(fn group -> {group, Enum.max(Enum.map(group, & &1.share))} end)

    {fitting, remaining} =
      Enum.reduce_while(groups, {[], timeout_ms}, fn {group, weight}, {acc, left} ->
        ms = round(weight * @min_slice_ms)

        if ms <= left,
          do: {:cont, {[{group, weight, ms} | acc], left - ms}},
          else: {:halt, {acc, left}}
      end)

    case Enum.reverse(fitting) do
      [] ->
        case groups do
          [] -> []
          [{group, _weight} | _] -> [slice(group, timeout_ms)]
        end

      fitting ->
        total_weight = fitting |> Enum.map(&elem(&1, 1)) |> Enum.sum()

        Enum.map(fitting, fn {group, weight, ms} ->
          slice(group, ms + floor(remaining * weight / total_weight))
        end)
    end
  end

  defp slice(group, ms) do
    %{strategies: Enum.map(group, &{&1.name, &1.opts}), timeout_ms: ms}
  end

  @doc """
  Parses and lowers `path`, then runs the schedule (see `prove_lowered/2`).
  """
  @spec prove_file(Path.t(), keyword()) :: Portfolio.result()
  def prove_file(path, opts \\ []) do
    case TptpLower.from_file(path, opts) do
      {:ok, lowered} -> prove_lowered(lowered, Keyword.put_new(opts, :problem_path, path))
      {:error, _} = err -> err
    end
  end

  @doc """
  Runs the schedule on a lowered problem until a slice returns an answer or the
  time is up. Options are passed to every `Astraea.Portfolio.prove_lowered/2`
  call (strategy options take precedence), plus:
    * `:timeout_ms` - global time limit (default 2 500)
    * `:cores` - strategies per slice (default `System.schedulers_online/0`)
    * `:schedule_strategies` - the strategy list (default `strategies/0`)
    * `:strategy_overrides` - options applied on top of every strategy, e.g.
      `sine_limit: nil` for Leo-III's `--noaxiomselection`

  External racers (`:external`) only run in the first slice. An unverified
  external answer (`:proved_external`) does not stop the schedule unless
  `:trust_external` is set, since a later slice may still find an LCF proof.
  """
  @spec prove_lowered(TptpLower.t(), keyword()) :: Portfolio.result()
  def prove_lowered(%TptpLower{} = lowered, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    cores = Keyword.get_lazy(opts, :cores, &System.schedulers_online/0)
    overrides = Keyword.get(opts, :strategy_overrides, [])

    strategies =
      opts
      |> Keyword.get_lazy(:schedule_strategies, &strategies/0)
      |> Enum.map(fn strat -> %{strat | opts: Keyword.merge(strat.opts, overrides)} end)

    deadline = System.monotonic_time(:millisecond) + timeout_ms
    run(lowered, strategies, cores, deadline, opts, nil)
  end

  defp run(_lowered, [], _cores, _deadline, _opts, best), do: finish(best)

  defp run(lowered, strategies, cores, deadline, opts, best) do
    left = deadline - System.monotonic_time(:millisecond)

    case build(max(left, 0), cores, strategies) do
      [%{timeout_ms: ms} = slice | _] when ms > 0 ->
        slice_opts =
          opts
          |> Keyword.drop([:schedule_strategies, :strategy_overrides, :cores])
          |> Keyword.merge(strategies: slice.strategies, timeout_ms: ms)

        result = Portfolio.prove_lowered(lowered, slice_opts)
        rest = Enum.drop(strategies, length(slice.strategies))
        opts = Keyword.delete(opts, :external)

        if answer?(result, opts),
          do: result,
          else: run(lowered, rest, cores, deadline, opts, better(best, result))

      _ ->
        finish(best)
    end
  end

  defp answer?({:proved, _steps, _stats}, _opts), do: true
  defp answer?({tag, _stats}, _opts) when tag in [:counter_satisfiable, :satisfiable], do: true
  defp answer?({:proved_external, _stats}, opts), do: Keyword.get(opts, :trust_external, false)
  defp answer?({:error, _reason}, _opts), do: true
  defp answer?(_result, _opts), do: false

  defp better({:proved_external, _} = held, _result), do: held
  defp better(_best, result), do: result

  # The last slice's outcome (`szs: :timeout` or `:gave_up`) is the answer.
  defp finish(nil), do: {:resource_out, %{iterations: 0, szs: :timeout}}
  defp finish(result), do: result
end
