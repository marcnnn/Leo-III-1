defmodule Astraea.Portfolio do
  @moduledoc """
  WP3: Multi-Core OTP Strategy Portfolio Runner for `Astraea.Prover`.

  Coordinates concurrent strategy workers over a shared problem input, varying:
  1. `:goal_standard` — Balanced SInE (`sine_limit: 55`), bridge-predicate preservation,
     and goal-directed variable-penalized clause ordering.
  2. `:sine_tight_unit` — Tight SInE premise selection (`sine_limit: 16`) for large
     axiomatizations (`ITP`, `SEU`, `CSR`) with unit-focused clause selection.
  3. `:full_inline_weight` — Full constant & bridge-predicate expansion into conjectures
     (`inline_bridges: true`, `sine_limit: 40`) with weight-first KBO ordering.
  4. `:broad_breadth` — Wide SInE window (`sine_limit: 90`) and breadth-first depth
     ordering with higher literal/weight ceilings (`max_clause_lits: 8`).

  Workers race concurrently under an OTP monitor loop; as soon as the first worker
  constructs an LCF-verified refutation (`Astraea.ProofChecker.verify_refutation/2`),
  sibling workers are terminated immediately (`Process.exit(pid, :kill)`).

  External provers (`:external` option, see `Astraea.External`) race alongside the
  internal strategies as MuonTrap-supervised OS processes. Killing their worker
  closes the port and MuonTrap kills the prover process tree. An external
  refutation is reconstructed from its unsat core by `Astraea.Prover`
  (`Astraea.External.Reconstruct`) and then reported as an ordinary LCF-verified
  `{:proved, ...}` with `:external_assist` stats. Answers that cannot be
  reconstructed stay unverified oracle results, reported as
  `{:proved_external, stats}`, `{:counter_satisfiable, stats}` or
  `{:satisfiable, stats}`.

  ## SZS answers

  Like Leo-III (`appropriateThmStatus`, `appropriateSatStatus`), results carry the
  SZS status they establish, read with `szs_status/1`:

    * an LCF-verified refutation is a `Theorem` when the problem has a conjecture,
      `ContradictoryAxioms` when its input clauses all stem from the axioms alone,
      and `Unsatisfiable` without a conjecture
    * an internal strategy that saturates with `stats.complete == true` (no clause
      lost to limits, no SInE filtering, no unification cutoffs) has found a model
      of the clause set: `{:counter_satisfiable, stats}` with a conjecture,
      `{:satisfiable, stats}` without one. Such an answer ends the race like a proof.
    * other outcomes are `GaveUp`, or `Timeout` when the time limit was reached
  """

  alias Astraea.{
    Clausifier,
    Compressor,
    Evaluator,
    External,
    ProofChecker,
    Prover,
    TptpCorpus,
    TptpLower,
    Tstp
  }

  alias Astraea.External.Reconstruct

  # The ContradictoryAxioms check clausifies all axioms; when that takes longer the
  # answer is Theorem.
  @cax_check_ms 1_000

  @model_tags [:counter_satisfiable, :satisfiable]
  @external_tags [:proved_external | @model_tags]

  @type strategy_spec :: {atom(), keyword()}

  @type result ::
          Prover.result()
          | {:proved_external, map()}
          | {:counter_satisfiable, map()}
          | {:satisfiable, map()}

  @doc """
  Returns the default 4-strategy portfolio schedule.
  """
  @spec default_strategies() :: [strategy_spec()]
  def default_strategies do
    [
      {:goal_standard,
       [
         sine_limit: 55,
         inline_bridges: false,
         scoring_mode: :goal_directed,
         max_clause_lits: 8,
         max_clause_weight: 60
       ]},
      {:sine_tight_unit,
       [
         sine_limit: 16,
         inline_bridges: false,
         scoring_mode: :unit_focused,
         max_clause_lits: 7,
         max_clause_weight: 55
       ]},
      {:full_inline_weight,
       [
         sine_limit: 40,
         inline_bridges: true,
         scoring_mode: :weight_first,
         max_clause_lits: 8,
         max_clause_weight: 65,
         funcspec: true
       ]},
      {:broad_breadth,
       [
         sine_limit: 90,
         inline_bridges: false,
         scoring_mode: :breadth_first,
         max_clause_lits: 10,
         max_clause_weight: 75,
         special_instances: true,
         funcspec: true
       ]}
    ]
  end

  @doc """
  The dedicated `:funcspec` strategy for function synthesis via choice.
  """
  @spec funcspec_strategy() :: strategy_spec()
  def funcspec_strategy do
    {:funcspec,
     [
       funcspec: true,
       choice: true,
       prim_subst: 2,
       unifier_count: 10,
       unify_depth: 8,
       ordered: false,
       flex_resolution: :all,
       max_clause_lits: 8,
       max_clause_weight: 60
     ]}
  end

  @doc """
  The dedicated `:eval_reflection` strategy that eagerly normalizes ground
  lambda/combinator/boolean literals.
  """
  @spec eval_reflection_strategy() :: strategy_spec()
  def eval_reflection_strategy do
    {:eval_reflection,
     [
       eval_simplify: true,
       prim_subst_filter: true,
       sine_limit: 30,
       scoring_mode: :unit_focused,
       max_clause_lits: 5,
       max_clause_weight: 40
     ]}
  end

  @doc """
  Parses, lowers, and runs the multi-strategy portfolio on a TPTP problem file.
  """
  @spec prove_file(Path.t(), keyword()) :: result()
  def prove_file(path, opts \\ []) do
    case TptpLower.from_file(path, opts) do
      {:ok, lowered} ->
        prove_lowered(lowered, Keyword.put_new(opts, :problem_path, path))

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Runs all portfolio strategies concurrently on a `%Astraea.TptpLower{}` problem,
  returning the first LCF-verified refutation and immediately killing sibling workers.
  If `:compress => true` (default `true`), compresses the winning LCF proof DAG via
  `Astraea.Compressor.compress_dag/2`.

  External provers are enabled with `:external`, a list of prover names or
  `{name, opts}` tuples. The opts are those of `Astraea.External.run/3` plus
  `:input` (`:problem` passes the original file from `:problem_path`, `:clauses`
  passes Astraea's clause set; defaults to `:problem` when a path is known),
  `:spec` for custom provers, and `:reconstruct` (default `true`).

  `:cooperate` is passed to every internal strategy (see `Astraea.Prover.prove_clauses/3`).

  `:external_policy` decides how external answers are used:
    * `:race` (default) - the first definitive answer, internal or external, wins
    * `:fallback` - an external answer is only returned when no internal strategy
      finds an LCF-verified proof
  """
  @spec prove_lowered(TptpLower.t(), keyword()) :: result()
  def prove_lowered(%TptpLower{} = lowered, opts \\ []) do
    conjecture? = lowered.conjectures != []

    counterexample =
      if conjecture? and Keyword.get(opts, :model_probe, true) do
        case lowered.conjectures do
          [{_name, conj_term} | _] ->
            axioms = Enum.map(lowered.axioms, &elem(&1, 2))
            Evaluator.find_counterexample(lowered.arena, conj_term, axioms)

          _ ->
            :not_found
        end
      else
        :not_found
      end

    case counterexample do
      {:counterexample, env} ->
        {:counter_satisfiable,
         %{
           szs: :counter_satisfiable,
           counterexample: env,
           complete: true,
           iterations: 0,
           reductions: 0
         }}

      :not_found ->
        do_prove_lowered(lowered, opts)
    end
  end

  defp do_prove_lowered(%TptpLower{} = lowered, opts) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    strategies = Keyword.get(opts, :strategies, default_strategies())
    raw_externals = Keyword.get(opts, :external)

    externals =
      cond do
        is_list(raw_externals) ->
          Enum.map(raw_externals, &normalize_external/1)

        raw_externals == :auto or Keyword.get(opts, :competitive, false) ->
          [:cvc5, :vampire, :eprover_ho]
          |> Enum.filter(&(&1 in External.Provers.available()))
          |> Enum.map(&normalize_external/1)

        true ->
          []
      end
    policy = Keyword.get(opts, :external_policy, :race)
    compress? = Keyword.get(opts, :compress, true)
    conjecture? = lowered.conjectures != []
    deadline_ms = System.monotonic_time(:millisecond) + timeout_ms

    parent = self()
    race_ref = make_ref()

    # Killed external workers cannot remove their own problem files.
    tmp_dir =
      if externals != [] do
        dir =
          Path.join(System.tmp_dir!(), "astraea_portfolio_#{System.unique_integer([:positive])}")

        File.mkdir_p!(dir)
        dir
      end

    internal_workers =
      Map.new(strategies, fn {strat_name, strat_opts} ->
        merged_opts =
          opts
          |> Keyword.merge(strat_opts)
          |> Keyword.put(:timeout_ms, timeout_ms)

        {pid, mon_ref} =
          spawn_monitor(fn ->
            res = lowered |> Prover.prove_lowered(merged_opts) |> model_answer(conjecture?)
            send(parent, {race_ref, self(), strat_name, res})
          end)

        {pid, {mon_ref, strat_name}}
      end)

    external_workers =
      Map.new(externals, fn {ext_name, ext_opts} ->
        ext_opts =
          ext_opts
          |> Keyword.put_new(:timeout_ms, timeout_ms)
          |> Keyword.put(:tmp_dir, tmp_dir)

        strat_name = {:external, ext_name}

        {pid, mon_ref} =
          spawn_monitor(fn ->
            res =
              ext_name
              |> run_external(ext_opts, lowered, opts, deadline_ms)
              |> model_answer_external(conjecture?)

            send(parent, {race_ref, self(), strat_name, res})
          end)

        {pid, {mon_ref, strat_name}}
      end)

    workers = Map.merge(internal_workers, external_workers)

    race_result =
      try do
        await_race(race_ref, workers, deadline_ms, nil, policy)
      after
        if tmp_dir, do: File.rm_rf(tmp_dir)
      end

    case race_result do
      {:proved, steps, stats} ->
        {steps, stats} =
          if compress? and is_map_key(stats, :arena) do
            {:ok, comp_arena, comp_steps, comp_meta} =
              Compressor.compress_dag(stats.arena, steps)

            {comp_steps,
             stats
             |> Map.put(:arena, comp_arena)
             |> Map.put(:raw_proof_length, length(steps))
             |> Map.put(:proof_length, length(comp_steps))
             |> Map.put(:compression, comp_meta)}
          else
            {steps, stats}
          end

        {:proved, steps, Map.put(stats, :szs, refutation_status(lowered, steps, stats))}

      {:proved_external, stats} ->
        status =
          cond do
            not conjecture? -> :unsatisfiable
            stats[:szs_status] == :contradictory_axioms -> :contradictory_axioms
            true -> :theorem
          end

        {:proved_external, Map.put(stats, :szs, status)}

      {tag, stats} when tag in @model_tags ->
        {tag, Map.put(stats, :szs, tag)}

      {tag, stats} when tag in [:resource_out, :saturated] and is_map(stats) ->
        out_of_time? = System.monotonic_time(:millisecond) >= deadline_ms
        {tag, Map.put(stats, :szs, if(out_of_time?, do: :timeout, else: :gave_up))}

      other ->
        other
    end
  end

  @doc """
  Returns the SZS status established by a portfolio result (see the moduledoc).
  Unverified external answers (`:proved_external`) report the status they claim.
  """
  @spec szs_status(result()) :: atom()
  def szs_status({:proved, _steps, stats}), do: Map.get(stats, :szs, :theorem)
  def szs_status({:proved_external, stats}), do: Map.get(stats, :szs, :theorem)
  def szs_status({tag, _stats}) when tag in @model_tags, do: tag
  def szs_status({:error, {:lcf_verification_failed, _, _}}), do: :error
  def szs_status({:error, _reason}), do: :error
  def szs_status({_tag, stats}) when is_map(stats), do: Map.get(stats, :szs, :gave_up)

  # A saturated clause set is a model only if the search was complete.
  defp model_answer({:saturated, stats} = res, conjecture?) do
    cond do
      not Map.get(stats, :complete, false) -> res
      conjecture? -> {:counter_satisfiable, stats}
      true -> {:satisfiable, stats}
    end
  end

  defp model_answer(res, _conjecture?), do: res

  # Leo-III reports ContradictoryAxioms when the refutation does not use the
  # conjecture. Here every input clause of the proof must be a clause of the axioms
  # alone (up to variable renaming), which the clausifier derives without SInE.
  defp refutation_status(%TptpLower{conjectures: []}, _steps, _stats), do: :unsatisfiable

  defp refutation_status(%TptpLower{} = lowered, steps, %{arena: arena}) do
    parent = self()
    ref = make_ref()

    {pid, mon_ref} =
      spawn_monitor(fn ->
        {ax_arena, ax_clauses} =
          Clausifier.clausify(%{lowered | conjectures: []}, sine_limit: nil)

        keys = MapSet.new(ax_clauses, &Tstp.clause_key(ax_arena, &1))

        axioms_only? =
          Enum.all?(steps, fn
            {:axiom, _id, clause} -> MapSet.member?(keys, Tstp.clause_key(arena, clause))
            _step -> true
          end)

        send(parent, {ref, axioms_only?})
      end)

    receive do
      {^ref, axioms_only?} ->
        Process.demonitor(mon_ref, [:flush])
        if axioms_only?, do: :contradictory_axioms, else: :theorem

      {:DOWN, ^mon_ref, :process, ^pid, _reason} ->
        :theorem
    after
      @cax_check_ms ->
        Process.exit(pid, :kill)
        Process.demonitor(mon_ref, [:flush])
        :theorem
    end
  end

  defp refutation_status(_lowered, _steps, _stats), do: :theorem

  defp model_answer_external({:counter_satisfiable, stats}, false), do: {:satisfiable, stats}
  defp model_answer_external(res, _conjecture?), do: res

  defp normalize_external(name) when is_atom(name), do: {name, []}

  defp normalize_external({name, ext_opts}) when is_atom(name) and is_list(ext_opts),
    do: {name, ext_opts}

  defp run_external(ext_name, ext_opts, lowered, opts, deadline_ms) do
    prover = Keyword.get(ext_opts, :spec, ext_name)
    problem_path = Keyword.get(opts, :problem_path)
    input = Keyword.get(ext_opts, :input, if(problem_path, do: :problem, else: :clauses))

    {run, reconstruct} =
      case input do
        :problem ->
          tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
          ext_opts = Keyword.put_new(ext_opts, :tptp_root, tptp_root)

          {External.prove_problem(prover, problem_path, ext_opts),
           &Reconstruct.problem(lowered, &1, &2)}

        :clauses ->
          {arena, clauses} =
            Clausifier.clausify(lowered,
              sine_limit: Keyword.get(ext_opts, :sine_limit, 55),
              inline_bridges: Keyword.get(ext_opts, :inline_bridges, false)
            )

          {External.prove_clauses(prover, arena, clauses, ext_opts),
           &Reconstruct.clauses(arena, clauses, &1, &2)}
      end

    case run do
      {:ok, %External.Result{} = res} ->
        stats = %{
          iterations: 0,
          prover: res.prover,
          input: input,
          szs_status: res.status,
          dataform: res.dataform,
          proof: res.proof,
          external_elapsed_ms: res.elapsed_ms
        }

        case {External.SZS.classify(res.status), input} do
          {:unsat, _} ->
            if Keyword.get(ext_opts, :reconstruct, true),
              do: reconstruct_external(res, stats, reconstruct, opts, deadline_ms),
              else: {:proved_external, stats}

          # A model of the SInE-filtered clause set is not a model of the problem.
          {:sat, :problem} ->
            {:counter_satisfiable, stats}

          _ ->
            {:resource_out, stats}
        end

      {:error, reason} ->
        {:error, {:external, ext_name, reason}}
    end
  end

  # Re-proves the unsat core of an external refutation with `Astraea.Prover`, which
  # turns the oracle answer into an LCF-verified `{:proved, ...}` result.
  defp reconstruct_external(res, stats, reconstruct, opts, deadline_ms) do
    core = Reconstruct.core_names(res.proof)
    remaining = max(deadline_ms - System.monotonic_time(:millisecond), 0)

    recon_opts =
      opts
      |> Keyword.drop([:external, :external_policy, :strategies, :cooperate])
      |> Keyword.put(:timeout_ms, remaining)

    case reconstruct.(core, recon_opts) do
      {:proved, steps, recon_stats} ->
        {:proved, steps,
         Map.put(recon_stats, :external_assist, %{
           prover: res.prover,
           input: stats.input,
           szs_status: res.status,
           core_size: MapSet.size(core),
           external_elapsed_ms: res.elapsed_ms
         })}

      other ->
        {:proved_external,
         Map.merge(stats, %{core_size: MapSet.size(core), reconstruction: elem(other, 0)})}
    end
  end

  defp await_race(_race_ref, workers, _deadline_ms, last_non_proof, _policy)
       when map_size(workers) == 0 do
    last_non_proof || {:resource_out, %{iterations: 0}}
  end

  defp await_race(race_ref, workers, deadline_ms, last_non_proof, policy) do
    rem_ms = max(0, deadline_ms - System.monotonic_time(:millisecond))

    receive do
      {^race_ref, _pid, strat_name, {:proved, steps, stats}} ->
        shutdown_workers(workers)

        {:proved, steps,
         stats
         |> Map.put(:winning_strategy, strat_name)}

      {^race_ref, _pid, _strat_name, {:error, {:lcf_verification_failed, _, _}} = lcf_err} ->
        shutdown_workers(workers)
        lcf_err

      {^race_ref, _pid, strat_name, {tag, stats}}
      when tag in @model_tags and is_atom(strat_name) ->
        shutdown_workers(workers)
        {tag, Map.put(stats, :winning_strategy, strat_name)}

      {^race_ref, _pid, strat_name, {tag, stats}}
      when tag in @external_tags and policy == :race ->
        shutdown_workers(workers)
        {tag, Map.put(stats, :winning_strategy, strat_name)}

      {^race_ref, pid, strat_name, non_proof} ->
        case Map.pop(workers, pid) do
          {{mon_ref, _}, rest} ->
            Process.demonitor(mon_ref, [:flush])
            tagged = tag_non_proof(non_proof, strat_name)

            continue_race(
              race_ref,
              rest,
              deadline_ms,
              pick_better_non_proof(last_non_proof, tagged),
              policy
            )

          {nil, rest} ->
            continue_race(race_ref, rest, deadline_ms, last_non_proof, policy)
        end

      {:DOWN, _mon_ref, :process, pid, _reason} ->
        rest = Map.delete(workers, pid)
        continue_race(race_ref, rest, deadline_ms, last_non_proof, policy)
    after
      rem_ms + 250 ->
        shutdown_workers(workers)
        finish_external(last_non_proof) || {:resource_out, %{iterations: 0}}
    end
  end

  # Under `:fallback`, a held external answer is returned as soon as no internal
  # strategy is left that could still produce an LCF-verified proof.
  defp continue_race(race_ref, workers, deadline_ms, best, policy) do
    internal_left? =
      Enum.any?(workers, fn {_pid, {_mon_ref, name}} -> not match?({:external, _}, name) end)

    if external_answer?(best) and not internal_left? do
      shutdown_workers(workers)
      finish_external(best)
    else
      await_race(race_ref, workers, deadline_ms, best, policy)
    end
  end

  defp external_answer?({tag, _stats}), do: tag in @external_tags
  defp external_answer?(_other), do: false

  defp finish_external({tag, stats} = answer) do
    if external_answer?(answer),
      do: {tag, Map.put(stats, :winning_strategy, stats.strategy)},
      else: answer
  end

  defp finish_external(other), do: other

  defp shutdown_workers(workers) do
    Enum.each(workers, fn {pid, {mon_ref, _strat_name}} ->
      Process.demonitor(mon_ref, [:flush])
      Process.exit(pid, :kill)
    end)
  end

  defp tag_non_proof({tag, stats}, strat_name) when is_map(stats) do
    {tag, Map.put(stats, :strategy, strat_name)}
  end

  defp tag_non_proof(other, _strat_name), do: other

  defp pick_better_non_proof(nil, candidate), do: candidate

  defp pick_better_non_proof({tag, _} = ext, _candidate) when tag in @external_tags, do: ext
  defp pick_better_non_proof(_prev, {tag, _} = ext) when tag in @external_tags, do: ext

  defp pick_better_non_proof({:saturated, _} = sat, _candidate), do: sat
  defp pick_better_non_proof(_prev, {:saturated, _} = sat), do: sat
  defp pick_better_non_proof(prev, _candidate), do: prev

  @doc """
  Evaluates a TPTP split (`:smoke`, `:dev`, `:holdout`, or `:extended`) using the multi-strategy
  portfolio, enforcing Gate 3 (0 `CSA` false proofs, 100% LCF proof verification)
  and aggregating strategy win counts and proof compression telemetry.

  A wrong answer in either direction is a soundness failure: a proof of a
  CounterSatisfiable/Satisfiable problem (`csa_false_proofs`) and an internal
  CounterSatisfiable/Satisfiable claim on a Theorem/Unsatisfiable problem
  (`false_model_claims`); `soundness_failures` counts both. Correct model answers
  are reported as `csa_solved`.

  With `schedule: true` problems are run through `Astraea.Schedule.prove_file/2`
  (the CLI's time-sliced schedule) instead of a single portfolio race.
  """
  @spec evaluate_split(TptpCorpus.split(), keyword()) :: map()
  def evaluate_split(split, opts \\ []) when split in [:smoke, :dev, :holdout, :extended] do
    tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    default_conc = max(1, div(System.schedulers_online(), 2))
    max_concurrency = Keyword.get(opts, :max_concurrency, default_conc)

    entries = TptpCorpus.load_split_entries(split)

    results =
      entries
      |> Task.async_stream(
        fn entry ->
          abs_path = Path.join(tptp_root, entry.rel_path)
          t0 = System.monotonic_time(:microsecond)
          run_opts = Keyword.put(opts, :tptp_root, tptp_root)

          res =
            if Keyword.get(opts, :schedule, false),
              do: Astraea.Schedule.prove_file(abs_path, run_opts),
              else: prove_file(abs_path, run_opts)

          elapsed_ms = Float.round((System.monotonic_time(:microsecond) - t0) / 1000.0, 2)
          {entry, res, elapsed_ms}
        end,
        max_concurrency: max_concurrency,
        timeout: timeout_ms + 8_000,
        on_timeout: :kill_task
      )
      |> Enum.map(fn
        {:ok, item} -> item
        {:exit, :timeout} -> {:timeout, :resource_out, timeout_ms * 1.0}
      end)

    thm_solved =
      for {entry, {:proved, steps, st}, ms} <- results,
          is_map(entry) and entry.status == "Theorem" do
        %{
          problem: entry.problem,
          domain: entry.domain,
          proof_length: length(steps),
          raw_proof_length: Map.get(st, :raw_proof_length, length(steps)),
          iterations: st.iterations,
          elapsed_ms: ms,
          winning_strategy: Map.get(st, :winning_strategy, :goal_standard),
          compression: Map.get(st, :compression, %{}),
          external_assist: Map.get(st, :external_assist)
        }
      end

    csa_false_proofs =
      for {entry, {:proved, _steps, _st}, _ms} <- results,
          is_map(entry) and entry.status in ["CounterSatisfiable", "Satisfiable"] do
        entry.problem
      end

    # Model answers of internal strategies (external ones are tallied below).
    model_answers =
      for {entry, {tag, st}, ms} <- results,
          is_map(entry) and tag in @model_tags and is_atom(st.winning_strategy) do
        {entry, tag, st, ms}
      end

    false_model_claims =
      for {entry, tag, st, _ms} <- model_answers,
          entry.status in ["Theorem", "Unsatisfiable", "ContradictoryAxioms"] do
        {entry.problem, tag, st.winning_strategy}
      end

    csa_solved =
      for {entry, tag, st, ms} <- model_answers,
          entry.status in ["CounterSatisfiable", "Satisfiable"] do
        %{
          problem: entry.problem,
          domain: entry.domain,
          szs: tag,
          elapsed_ms: ms,
          winning_strategy: st.winning_strategy
        }
      end

    lcf_failures =
      for {entry, {:error, {:lcf_verification_failed, reason, _}}, _ms} <- results,
          is_map(entry) do
        {entry.problem, reason}
      end

    strategy_wins =
      Enum.frequencies_by(thm_solved, & &1.winning_strategy)

    # LCF-verified proofs found with external help (portfolio racer or mid-search cooperation).
    externally_assisted = Enum.count(thm_solved, & &1.external_assist)

    domain_breakdown =
      thm_solved
      |> Enum.group_by(& &1.domain)
      |> Map.new(fn {dom, list} -> {dom, length(list)} end)

    # External oracle answers are tallied apart from LCF-verified proofs.
    external_thm_solved =
      for {entry, {:proved_external, st}, ms} <- results,
          is_map(entry) and entry.status == "Theorem" do
        %{
          problem: entry.problem,
          domain: entry.domain,
          elapsed_ms: ms,
          winning_strategy: st.winning_strategy
        }
      end

    # Internal model answers on Theorem problems are counted in `false_model_claims`.
    external_unsound =
      for {entry, {tag, st}, _ms} <- results,
          is_map(entry),
          is_map(st) and match?({:external, _}, st[:winning_strategy]),
          {tag, entry.status} in [
            {:proved_external, "CounterSatisfiable"},
            {:proved_external, "Satisfiable"},
            {:counter_satisfiable, "Theorem"},
            {:counter_satisfiable, "Unsatisfiable"},
            {:satisfiable, "Theorem"},
            {:satisfiable, "Unsatisfiable"}
          ] do
        {entry.problem, st.winning_strategy, st.szs_status}
      end

    %{
      split: split,
      total: length(entries),
      thm_total: Enum.count(entries, &(&1.status == "Theorem")),
      csa_total: Enum.count(entries, &(&1.status in ["CounterSatisfiable", "Satisfiable"])),
      thm_solved_count: length(thm_solved),
      thm_solved: thm_solved,
      externally_assisted_count: externally_assisted,
      strategy_wins: strategy_wins,
      domain_breakdown: domain_breakdown,
      csa_false_proofs: csa_false_proofs,
      false_model_claims: false_model_claims,
      soundness_failures: length(csa_false_proofs) + length(false_model_claims),
      csa_solved_count: length(csa_solved),
      csa_solved: csa_solved,
      lcf_failures: lcf_failures,
      external_thm_solved_count: length(external_thm_solved),
      external_thm_solved: external_thm_solved,
      external_strategy_wins: Enum.frequencies_by(external_thm_solved, & &1.winning_strategy),
      external_unsound: external_unsound,
      raw_results: results
    }
  end

  @spec verify_proof(Astraea.Arena.t(), [ProofChecker.step()]) ::
          :ok | {:error, term()}
  def verify_proof(arena, steps) do
    ProofChecker.verify_refutation(arena, steps)
  end
end
