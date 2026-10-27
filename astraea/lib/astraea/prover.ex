defmodule Astraea.Prover do
  @moduledoc """
  Higher-Order THF0 Given-Clause Micro-Prover & OTP Portfolio Runner.

  Implements a discount-style saturation loop over `Astraea.Arena` terms with:
  - Clause Condensation (`condense_clause/2` via `:subst`)
  - Eager Unit-Clause Subsumption Resolution (`unit_simplify/2` via `:subst` + `:resolve`)
  - Demodulation with KBO-ordered unit equations, forward and backward
    (`Astraea.Engine.Demodulator`, via `:subst` + `:paramod`)
  - Equality Resolution (`~(s = t)` via unification + `:refl` + `:resolve`)
  - Positive & Negative Factoring (`:subst`)
  - Positive Functional Extensionality (`:func_ext` xi-rule)
  - Binary Resolution with higher-order pattern/abstraction unification (`:subst` + `:resolve`)
  - KBO-oriented Superposition / Paramodulation (`:subst` + `:paramod`)
  - Higher-Order Predicate Reflexivity Instantiation (`P := ^ [Z]: (Z = u)`)
  - Forward and backward multiset subsumption (`Astraea.Engine.Subsumption`) behind
    feature-vector indexes of the active and passive sets (`Astraea.Engine.FVIndex`)

  The passive set is an `Astraea.Engine.PassiveQueue` with Leo-III style weighted
  round-robin selection. No clause is dropped unless a limit option asks for it, so
  with the defaults the loop is refutationally complete relative to its inference
  rules; `stats/1` reports `:discarded_clauses` and `:complete` accordingly.

  Every refutation (`SZS status Theorem`) constructs a minimal DAG of primitive inference
  steps and passes it through `Astraea.ProofChecker.verify_refutation/2` before returning.
  Redundancy elimination only removes clauses from the search state, never steps, so
  deleted clauses remain available as proof ancestors.

  With `:cooperate`, the loop periodically hands its current clause set to external
  provers (Leo-III style cooperation, see `Astraea.External`). An external refutation
  is reconstructed by a seeded sub-search on its unsat core whose proof is spliced onto
  the existing derivations of the core clauses, so cooperation never weakens the LCF
  guarantee unless `:trust_external` is set.
  """

  alias Astraea.{Arena, Clausifier, External, ProofChecker, TptpCorpus, TptpLower}
  alias Astraea.Engine.{Demodulator, FVIndex, HeadIndex, PassiveQueue, Subsumption}
  alias Astraea.External.Reconstruct

  # Below this remaining budget an external call cannot finish in time.
  @min_external_ms 300

  # Rewrite steps per clause simplification; KBO-decreasing rewriting terminates,
  # this only bounds the cost of long chains.
  @max_rewrites 64

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_bvar 2
  @tag_fvar 3
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10
  @tag_comb 11

  defstruct arena: nil,
            steps: %{},
            next_step_id: 1,
            next_fvar_id: 100_000,
            active: [],
            active_by_id: %{},
            active_index: nil,
            passive: nil,
            passive_index: nil,
            units: %{},
            unit_count: 0,
            rules: %{},
            seen_clauses: MapSet.new(),
            iterations: 0,
            max_iterations: :infinity,
            max_clause_lits: :infinity,
            max_clause_weight: :infinity,
            max_units: :infinity,
            backward_subsumption: true,
            demodulation: true,
            scoring_mode: :goal_directed,
            sine_filtered: false,
            discarded_clauses: 0,
            # Unifier searches cut off by a depth limit (counted by the calculus).
            unification_cutoffs: 0,
            forward_subsumed: 0,
            backward_subsumed: 0,
            rewrites: 0,
            backward_rewritten: 0,
            deadline_ms: nil,
            opts: [],
            cooperate: [],
            coop_interval: 40,
            coop_max_clauses: 400,
            coop_last_dispatch: 0,
            coop_inflight: %{},
            coop_log: []

  @type result ::
          {:proved, [ProofChecker.step()], map()}
          | {:saturated, map()}
          | {:resource_out, map()}
          | {:error, term()}

  @doc """
  Loads, lowers, clausifies, and attempts to prove a TPTP THF0 problem file.
  Every discovered refutation is verified by `Astraea.ProofChecker.verify_refutation/2`.
  """
  @spec prove_file(Path.t(), keyword()) :: result()
  def prove_file(path, opts \\ []) do
    case TptpLower.from_file(path, opts) do
      {:ok, lowered} ->
        prove_lowered(lowered, opts)

      {:error, _} = err ->
        err
    end
  end

  @spec prove_string(String.t(), keyword()) :: result()
  def prove_string(source, opts \\ []) do
    case TptpLower.from_string(source, opts) do
      {:ok, lowered} ->
        prove_lowered(lowered, opts)

      {:error, _} = err ->
        err
    end
  end

  @spec prove_lowered(TptpLower.t(), keyword()) :: result()
  def prove_lowered(%TptpLower{} = lowered, opts \\ []) do
    sine_limit = Keyword.get(opts, :sine_limit, 55)
    inline_bridges = Keyword.get(opts, :inline_bridges, false)

    {arena, clauses} =
      Clausifier.clausify(lowered,
        sine_limit: sine_limit,
        inline_bridges: inline_bridges
      )

    prove_clauses(
      arena,
      clauses,
      Keyword.put(opts, :sine_filtered, sine_filtered?(lowered, sine_limit))
    )
  end

  # Mirrors the SInE trigger in `Clausifier.clausify/2`. It counts definitions the
  # clausifier inlines before filtering, so it may report a filter that kept every
  # axiom: `:complete` errs on the safe side.
  defp sine_filtered?(%TptpLower{} = lowered, sine_limit) do
    is_integer(sine_limit) and length(lowered.axioms) > sine_limit and lowered.conjectures != []
  end

  @doc """
  Saturates `input_clauses`. Strategy options:
    * `:timeout_ms` - wall-clock budget (default 2500)
    * `:scoring_mode` - clause score for the passive queue (default `:goal_directed`)
    * `:pick_ratio` - passive selection schedule, `{priority, weight}` pairs over
      `:score`, `:age`, `:weight`, `:depth` (default `[score: 3, age: 1]`)
    * `:backward_subsumption`, `:demodulation` - redundancy elimination (default `true`)
    * `:index_backend` - `Astraea.Engine.FVIndex` backend (default `:auto`)
  Limits, all `:infinity` by default; a clause dropped by `:max_clause_lits` or
  `:max_clause_weight` counts as discarded and makes the run incomplete:
    * `:max_iterations` - given-clause iterations
    * `:max_clause_lits`, `:max_clause_weight` - generated clauses above both limits
      (weight only for clauses with more than two literals) are discarded
    * `:max_units` - unit clauses kept for unit simplification (no effect on completeness)
  External cooperation:
    * `:cooperate` - external provers to call during search, as names or
      `{name, opts}` (options of `Astraea.External.run/3`, plus `:spec`, `:format`)
    * `:cooperate_interval` - iterations between external calls (default 40)
    * `:cooperate_max_clauses` - clauses per call: all active and unit clauses, then
      the best-scored passive ones (default 400)
    * `:trust_external` - return `{:proved_external, stats}` when an external
      refutation cannot be reconstructed (default `false`)
    * `:seed` - `%{steps:, ids:, next_step_id:, next_fvar_id:}`: the input clauses
      were already derived as steps `ids` of `steps`, so they are not registered as
      axioms and a refutation includes their derivations
    * `:sine_filtered` - the input omits axioms (set by `prove_lowered/2`)
  """
  @spec prove_clauses(Arena.t(), [ProofChecker.clause()], keyword()) ::
          result() | {:proved_external, map()}
  def prove_clauses(%Arena{} = arena, input_clauses, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    deadline = System.monotonic_time(:millisecond) + timeout_ms
    index_opts = [backend: Keyword.get(opts, :index_backend, :auto)]

    state = %__MODULE__{
      arena: arena,
      active_index: FVIndex.new(index_opts),
      passive: PassiveQueue.new(Keyword.get(opts, :pick_ratio, score: 3, age: 1)),
      passive_index: FVIndex.new(index_opts),
      max_iterations: Keyword.get(opts, :max_iterations, :infinity),
      max_clause_lits: Keyword.get(opts, :max_clause_lits, :infinity),
      max_clause_weight: Keyword.get(opts, :max_clause_weight, :infinity),
      max_units: Keyword.get(opts, :max_units, :infinity),
      backward_subsumption: Keyword.get(opts, :backward_subsumption, true),
      demodulation: Keyword.get(opts, :demodulation, true),
      scoring_mode: Keyword.get(opts, :scoring_mode, :goal_directed),
      sine_filtered: Keyword.get(opts, :sine_filtered, false),
      deadline_ms: deadline,
      opts: opts,
      cooperate: opts |> Keyword.get(:cooperate, []) |> Enum.map(&normalize_external/1),
      coop_interval: Keyword.get(opts, :cooperate_interval, 40),
      coop_max_clauses: Keyword.get(opts, :cooperate_max_clauses, 400)
    }

    {state, seed_ids} =
      case Keyword.get(opts, :seed) do
        nil ->
          {state, nil}

        seed ->
          {%{
             state
             | steps: seed.steps,
               next_step_id: seed.next_step_id,
               next_fvar_id: max(state.next_fvar_id, seed.next_fvar_id)
           }, seed.ids}
      end

    case init_clauses(state, input_clauses, seed_ids) do
      {:proved, state, empty_id} ->
        finalize_proof(state, empty_id)

      {:cont, state} ->
        saturation_loop(state)
    end
  end

  @doc """
  Evaluates a TPTP split (`:smoke` or `:dev`) concurrently using OTP `Task.async_stream/3`.
  Enforces Gate 3: verifies that 0 `CounterSatisfiable` / `Satisfiable` problems are falsely
  proved and 100% of proved `Theorem` problems pass `Astraea.ProofChecker.verify_refutation/2`.
  """
  @spec evaluate_split(:smoke | :dev, keyword()) :: map()
  def evaluate_split(split, opts \\ []) when split in [:smoke, :dev] do
    tptp_root = Keyword.get(opts, :tptp_root, TptpCorpus.default_tptp_root())
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    max_concurrency = Keyword.get(opts, :max_concurrency, System.schedulers_online())

    entries = TptpCorpus.load_split_entries(split)

    results =
      entries
      |> Task.async_stream(
        fn entry ->
          abs_path = Path.join(tptp_root, entry.rel_path)
          t0 = System.monotonic_time(:microsecond)
          res = prove_file(abs_path, Keyword.put(opts, :tptp_root, tptp_root))
          elapsed_ms = Float.round((System.monotonic_time(:microsecond) - t0) / 1000.0, 2)
          {entry, res, elapsed_ms}
        end,
        max_concurrency: max_concurrency,
        timeout: timeout_ms + 5_000,
        on_timeout: :kill_task
      )
      |> Enum.map(fn
        {:ok, item} -> item
        {:exit, :timeout} -> {:timeout, :resource_out, timeout_ms * 1.0}
      end)

    thm_solved =
      for {entry, {:proved, steps, st}, ms} <- results,
          is_map(entry) and entry.status == "Theorem" do
        {entry.problem, entry.domain, length(steps), st.iterations, ms}
      end

    csa_false_proofs =
      for {entry, {:proved, _steps, _st}, _ms} <- results,
          is_map(entry) and entry.status in ["CounterSatisfiable", "Satisfiable"] do
        entry.problem
      end

    lcf_failures =
      for {entry, {:error, {:lcf_verification_failed, reason, _}}, _ms} <- results,
          is_map(entry) do
        {entry.problem, reason}
      end

    %{
      split: split,
      total: length(entries),
      thm_total: Enum.count(entries, &(&1.status == "Theorem")),
      csa_total: Enum.count(entries, &(&1.status in ["CounterSatisfiable", "Satisfiable"])),
      thm_solved_count: length(thm_solved),
      thm_solved: thm_solved,
      csa_false_proofs: csa_false_proofs,
      lcf_failures: lcf_failures,
      raw_results: results
    }
  end

  # ---------------------------------------------------------------------------
  # Initialization & Saturation Loop
  # ---------------------------------------------------------------------------

  defp init_clauses(%__MODULE__{} = state, clauses, seed_ids) do
    # Pass 1: Register all initial clauses as `:axiom` steps in their original order;
    # seeded clauses keep the ids of their existing derivations instead.
    entries = if seed_ids, do: Enum.zip(clauses, seed_ids), else: Enum.map(clauses, &{&1, nil})

    {state, axiom_items} =
      Enum.reduce(entries, {state, []}, fn {clause, seed_id}, {st, acc} ->
        {st, c_item} =
          case seed_id do
            nil -> add_step(st, {:axiom, st.next_step_id, clause}, clause, 0)
            id -> {st, clause_item(st, id, clause, 0)}
          end

        {add_unit(st, c_item), [c_item | acc]}
      end)

    axiom_items = Enum.reverse(axiom_items)

    # Pass 2: Condense, unit-simplify, and equality-resolve initial clauses
    Enum.reduce_while(axiom_items, {:cont, state}, fn c_item, {:cont, st} ->
      if MapSet.size(c_item.lits) == 0 do
        {:halt, {:proved, st, c_item.id}}
      else
        {st, cond_item} = condense_clause(st, c_item)

        case unit_simplify(st, cond_item) do
          {:proved, st2, empty_id} ->
            {:halt, {:proved, st2, empty_id}}

          {:ok, st2, simp_item} ->
            case try_immediate_eq_resolution(st2, simp_item) do
              {:proved, st3, empty_id} ->
                {:halt, {:proved, st3, empty_id}}

              {:cont, st3, derived_items} ->
                st4 = enqueue_passive(st3, [simp_item | derived_items])
                {:cont, {:cont, st4}}
            end
        end
      end
    end)
  end

  defp saturation_loop(%__MODULE__{iterations: iters, max_iterations: max_iters} = state)
       when is_integer(max_iters) and iters >= max_iters do
    finish(state, {:resource_out, stats(state)})
  end

  defp saturation_loop(%__MODULE__{} = state) do
    cond do
      PassiveQueue.empty?(state.passive) ->
        finish(state, {:saturated, stats(state)})

      System.monotonic_time(:millisecond) >= state.deadline_ms ->
        finish(state, {:resource_out, stats(state)})

      true ->
        case cooperate(state) do
          {:done, result, state} -> finish(state, result)
          {:cont, state} -> given_clause_step(state)
        end
    end
  end

  # One iteration of the given-clause loop (Leo-III `SeqLoop`): select, simplify
  # (condensation, unit simplification, demodulation), drop if redundant, else
  # simplify the processed set with it (backward subsumption and demodulation),
  # generate inferences and activate it.
  defp given_clause_step(%__MODULE__{} = state) do
    {given, passive} = PassiveQueue.pop(state.passive)

    state = %{
      state
      | passive: passive,
        passive_index: FVIndex.delete(state.passive_index, [given.id]),
        iterations: state.iterations + 1
    }

    {state, given} = condense_clause(state, given)

    case simplify(state, given) do
      {:proved, state, empty_id} ->
        finish(state, finalize_proof(state, empty_id))

      {:ok, state, given} ->
        cond do
          tautology_clause?(state.arena, given.lits) ->
            saturation_loop(state)

          forward_subsumed?(state, given) ->
            saturation_loop(%{state | forward_subsumed: state.forward_subsumed + 1})

          true ->
            state = state |> backward_subsume(given) |> backward_demodulate(given)

            case generate_inferences(state, given) do
              {:proved, state, empty_id} ->
                finish(state, finalize_proof(state, empty_id))

              {:cont, state, new_items} ->
                state
                |> activate(given)
                |> enqueue_passive(new_items)
                |> saturation_loop()
            end
        end
    end
  end

  defp activate(%__MODULE__{} = state, item) do
    state = %{
      state
      | active: [item | state.active],
        active_by_id: Map.put(state.active_by_id, item.id, item),
        active_index:
          FVIndex.insert(state.active_index, item.id, Subsumption.subsumption_fv(item))
    }

    state = add_unit(state, item)

    if state.demodulation,
      do: %{
        state
        | rules:
            Demodulator.add_rules(state.rules, state.arena, Demodulator.rules(state.arena, item))
      },
      else: state
  end

  defp add_unit(%__MODULE__{} = state, item) do
    if MapSet.size(item.lits) == 1 and below?(state.unit_count, state.max_units) do
      [{pol, atom}] = MapSet.to_list(item.lits)

      %{
        state
        | units: HeadIndex.put(state.units, state.arena, pol, atom, item),
          unit_count: state.unit_count + 1
      }
    else
      state
    end
  end

  defp below?(_n, :infinity), do: true
  defp below?(n, limit), do: n < limit

  defp exceeds?(_n, :infinity), do: false
  defp exceeds?(n, limit), do: n > limit

  # Removes processed clauses (e.g. backward-subsumed or rewritten ones) from the
  # search state; their steps stay, so they can still be proof ancestors.
  defp remove_active(%__MODULE__{} = state, []), do: state

  defp remove_active(%__MODULE__{} = state, ids) do
    gone = MapSet.new(ids)
    units = HeadIndex.reject(state.units, gone)

    %{
      state
      | active: Enum.reject(state.active, &MapSet.member?(gone, &1.id)),
        active_by_id: Map.drop(state.active_by_id, ids),
        active_index: FVIndex.delete(state.active_index, ids),
        units: units,
        unit_count: length(HeadIndex.values(units)),
        rules: HeadIndex.reject(state.rules, gone)
    }
  end

  defp enqueue_passive(%__MODULE__{} = state, items) do
    {state, fresh} =
      Enum.reduce(items, {state, []}, fn item, {st, acc} ->
        num_lits = MapSet.size(item.lits)

        cond do
          exceeds?(num_lits, st.max_clause_lits) or
              (exceeds?(item.weight, st.max_clause_weight) and num_lits > 2) ->
            {%{st | discarded_clauses: st.discarded_clauses + 1}, acc}

          tautology_clause?(st.arena, item.lits) ->
            {st, acc}

          true ->
            sig = canonical_clause_sig(st.arena, item.lits)

            if MapSet.member?(st.seen_clauses, sig),
              do: {st, acc},
              else: {%{st | seen_clauses: MapSet.put(st.seen_clauses, sig)}, [item | acc]}
        end
      end)

    fresh = Enum.reverse(fresh)

    subsumers =
      FVIndex.subsumers_batch(state.active_index, Enum.map(fresh, &Subsumption.subsumption_fv/1))

    Enum.zip_reduce(fresh, subsumers, state, fn item, candidate_ids, st ->
      if subsumed_by_any?(st, candidate_ids, item) do
        %{st | forward_subsumed: st.forward_subsumed + 1}
      else
        %{
          st
          | passive: PassiveQueue.insert(st.passive, item),
            passive_index:
              FVIndex.insert(st.passive_index, item.id, Subsumption.subsumption_fv(item))
        }
      end
    end)
  end

  # ---------------------------------------------------------------------------
  # Redundancy Elimination (Subsumption & Demodulation)
  # ---------------------------------------------------------------------------

  defp forward_subsumed?(%__MODULE__{} = state, item) do
    subsumed_by_any?(
      state,
      FVIndex.subsumers(state.active_index, Subsumption.subsumption_fv(item)),
      item
    )
  end

  defp subsumed_by_any?(%__MODULE__{} = state, candidate_ids, item) do
    Enum.any?(candidate_ids, fn id ->
      Subsumption.subsumes?(state.arena, Map.fetch!(state.active_by_id, id), item)
    end)
  end

  # Leo-III `SubsumptionControl.testBackwardSubsumptionFVI`, on both clause sets.
  defp backward_subsume(%__MODULE__{backward_subsumption: false} = state, _given), do: state

  defp backward_subsume(%__MODULE__{} = state, given) do
    fv = Subsumption.subsumption_fv(given)

    active_ids =
      for id <- FVIndex.subsumed(state.active_index, fv),
          Subsumption.subsumes?(state.arena, given, Map.fetch!(state.active_by_id, id)),
          do: id

    passive_ids =
      for id <- FVIndex.subsumed(state.passive_index, fv),
          item = state.passive.items[id],
          Subsumption.subsumes?(state.arena, given, item),
          do: id

    state = remove_active(state, active_ids)

    %{
      state
      | passive: PassiveQueue.delete(state.passive, passive_ids),
        passive_index: FVIndex.delete(state.passive_index, passive_ids),
        backward_subsumed: state.backward_subsumed + length(active_ids) + length(passive_ids)
    }
  end

  # Forward simplification to a fixpoint: unit simplification and demodulation.
  defp simplify(%__MODULE__{} = state, item, fuel \\ @max_rewrites) do
    with {:ok, state, item} <- unit_simplify(state, item) do
      case demodulate(state, item, fuel) do
        {state, ^item, _fuel} -> {:ok, state, item}
        {state, rewritten, 0} -> {:ok, state, rewritten}
        {state, rewritten, fuel} -> simplify(state, rewritten, fuel)
      end
    end
  end

  # Rewrites `item` with the rules in `rules` (default: all) until no redex is left
  # or `fuel` steps were taken. Each step is a `:subst` instance of the unit
  # equation followed by a `:paramod` replacing the redex in one literal.
  defp demodulate(state, item, fuel, rules \\ nil)

  defp demodulate(%__MODULE__{} = state, item, 0, _rules), do: {state, item, 0}

  defp demodulate(%__MODULE__{} = state, item, fuel, rules) do
    case Demodulator.find_redex(state.arena, rules || state.rules, item) do
      {:none, arena} ->
        {%{state | arena: arena}, item, fuel}

      {:ok, arena, redex} ->
        state = %{state | arena: arena}

        {state, rule_inst, eq_inst} =
          apply_subst_if_needed(state, redex.rule.item, redex.subst, redex.rule.eq)

        {pol, atom} = lit = redex.lit
        {arena, replaced} = ProofChecker.replace_subterm(state.arena, atom, redex.from, redex.to)
        {arena, new_atom} = Arena.beta_eta_norm(arena, replaced)
        lits = item.lits |> MapSet.delete(lit) |> MapSet.put({pol, new_atom})
        state = %{state | arena: arena, rewrites: state.rewrites + 1}

        step =
          {:paramod, state.next_step_id, rule_inst.id, item.id, eq_inst, lit, {pol, new_atom}}

        {state, rewritten} = add_step(state, step, lits, item.depth)
        demodulate(state, rewritten, fuel - 1, rules)
    end
  end

  # Leo-III `SimplificationControl.rewritable`: active clauses the new rules of
  # `given` can rewrite leave the active set; their normal forms re-enter the
  # passive set. Candidates are prefiltered with each rule's left-hand side as a
  # feature-vector query (a redex instance is a subterm of the clause).
  defp backward_demodulate(%__MODULE__{demodulation: false} = state, _given), do: state

  defp backward_demodulate(%__MODULE__{} = state, given) do
    case Demodulator.rules(state.arena, given) do
      [] ->
        state

      rules ->
        index = Demodulator.add_rules(HeadIndex.new(), state.arena, rules)
        queries = Enum.map(rules, &Subsumption.term_query_fv(state.arena, &1.lhs))

        candidates =
          state.active_index
          |> FVIndex.subsumed_batch(queries)
          |> Enum.concat()
          |> Enum.uniq()
          |> Enum.map(&Map.fetch!(state.active_by_id, &1))

        {state, rewritten} =
          Enum.reduce(candidates, {state, []}, fn item, {st, acc} ->
            case demodulate(st, item, @max_rewrites, index) do
              {st, ^item, _} -> {st, acc}
              {st, new_item, _} -> {st, [{item.id, new_item} | acc]}
            end
          end)

        state
        |> remove_active(Enum.map(rewritten, &elem(&1, 0)))
        |> Map.update!(:backward_rewritten, &(&1 + length(rewritten)))
        |> enqueue_passive(Enum.map(rewritten, &elem(&1, 1)))
    end
  end

  # Clause Condensation (`condense_clause/2`):
  # If matching two same-polarity literals `{pol, a2}` -> `{pol, a1}` yields a substitution
  # `subst` that maps `clause_item.lits` onto a strict subset of itself, replaces `clause_item`
  # with the condensed clause via an LCF `:subst` step.
  defp condense_clause(%__MODULE__{} = state, clause_item) do
    if MapSet.size(clause_item.fvars) <= 1 or MapSet.size(clause_item.lits) <= 1 do
      {state, clause_item}
    else
      lits = MapSet.to_list(clause_item.lits)

      cond_subst =
        Enum.find_value(lits, fn {pol1, a1} ->
          Enum.find_value(lits, fn {pol2, a2} ->
            if pol1 == pol2 and a1 != a2 do
              case Arena.match_pattern(state.arena, a2, a1) do
                {:ok, subst} when map_size(subst) > 0 ->
                  {arena, cand_lits} =
                    Enum.reduce(clause_item.lits, {state.arena, MapSet.new()}, fn {p, id},
                                                                                  {ar, acc} ->
                      {ar, id2} = Arena.subst_fvar(ar, id, subst)
                      {ar, MapSet.put(acc, {p, id2})}
                    end)

                  if MapSet.size(cand_lits) < MapSet.size(clause_item.lits) and
                       MapSet.subset?(cand_lits, clause_item.lits) do
                    {arena, subst}
                  else
                    nil
                  end

                _ ->
                  nil
              end
            else
              nil
            end
          end)
        end)

      case cond_subst do
        nil ->
          {state, clause_item}

        {arena, subst} ->
          st = %{state | arena: arena}
          {st, condensed_item} = emit_subst_step(st, clause_item, subst, clause_item.depth)
          condense_clause(st, condensed_item)
      end
    end
  end

  # Eager Unit-Clause Subsumption Resolution (`unit_simplify/2`):
  # Strips any literal `{pol, target_atom}` from `clause_item` that is matched by an
  # opposite-polarity 1-literal unit clause in `state.units` via `:subst` + `:resolve`.
  defp unit_simplify(%__MODULE__{unit_count: 0} = state, clause_item),
    do: {:ok, state, clause_item}

  defp unit_simplify(%__MODULE__{} = state, clause_item) do
    match_res =
      Enum.find_value(clause_item.lits, fn {pol, target_atom} ->
        state.units
        |> HeadIndex.lookup(state.arena, opposite(pol), target_atom)
        |> Enum.find_value(fn unit_c ->
          [{unit_pol, unit_atom}] = MapSet.to_list(unit_c.lits)

          with true <- unit_c.id != clause_item.id,
               {:ok, subst} <- Arena.match_pattern(state.arena, unit_atom, target_atom),
               true <- Demodulator.idempotent?(state.arena, subst) do
            {pol, target_atom, unit_c, unit_pol, unit_atom, subst}
          else
            _ -> nil
          end
        end)
      end)

    case match_res do
      nil ->
        {:ok, state, clause_item}

      {_pol, target_atom, unit_c, unit_pol, unit_atom, subst} ->
        {st, unit_inst, _} = apply_subst_if_needed(state, unit_c, subst, unit_atom)

        {pos_inst, neg_inst} =
          if unit_pol == :pos do
            {unit_inst, clause_item}
          else
            {clause_item, unit_inst}
          end

        case find_resolvable_atom(st.arena, pos_inst.lits, neg_inst.lits, target_atom) do
          {:ok, arena, resolve_atom, pos_lit, neg_lit} ->
            st = %{st | arena: arena}

            resolvent =
              MapSet.union(
                MapSet.delete(pos_inst.lits, pos_lit),
                MapSet.delete(neg_inst.lits, neg_lit)
              )

            depth = max(clause_item.depth, unit_c.depth)

            {st, res_item} =
              add_step(
                st,
                {:resolve, st.next_step_id, pos_inst.id, neg_inst.id, {:pos, resolve_atom}},
                resolvent,
                depth
              )

            if MapSet.size(resolvent) == 0 do
              {:proved, st, res_item.id}
            else
              unit_simplify(st, res_item)
            end

          :error ->
            {:ok, state, clause_item}
        end
    end
  end

  # ---------------------------------------------------------------------------
  # Inference Generation (EqRes, Factoring, HO Instantiation, Resolution, Paramod)
  # ---------------------------------------------------------------------------

  defp generate_inferences(%__MODULE__{} = state, given) do
    with {:cont, state, items0} <- try_func_ext_unit(state, given),
         {:cont, state, items1} <- try_immediate_eq_resolution(state, given),
         {:cont, state, items2} <- try_factoring(state, given),
         {:cont, state, items3} <- try_ho_pred_instantiation(state, given),
         {:cont, state, items4} <- try_binary_resolution(state, given),
         {:cont, state, items5} <- try_superposition(state, given) do
      {:cont, state, items0 ++ items1 ++ items2 ++ items3 ++ items4 ++ items5}
    end
  end

  # 0. Positive Functional Extensionality (xi-rule) on 1-variable unit equations:
  # `u(X) = v(X) |- (^ [X]: u(X)) = (^ [X]: v(X))` (e.g., `f @ X = X |- f = (^ [X]: X)`)
  defp try_func_ext_unit(%__MODULE__{} = state, clause_item) do
    with [{:pos, eq_id}] <- MapSet.to_list(clause_item.lits),
         [{fvar_id, var_ty}] <- MapSet.to_list(clause_item.fvars),
         {@tag_eq, _, _, lhs, rhs} <- Arena.get_node(state.arena, eq_id) do
      {arena, fv_node} = Arena.mk_fvar(state.arena, fvar_id, var_ty)
      {arena, abs_l} = Arena.abstract_subterm(arena, lhs, fv_node, 0)
      {arena, abs_r} = Arena.abstract_subterm(arena, rhs, fv_node, 0)
      {arena, lam_l} = Arena.mk_lam(arena, var_ty, abs_l)
      {arena, lam_r} = Arena.mk_lam(arena, var_ty, abs_r)
      {arena, norm_l} = Arena.beta_eta_norm(arena, lam_l)
      {arena, norm_r} = Arena.beta_eta_norm(arena, lam_r)
      {arena, new_eq} = Arena.mk_eq(arena, norm_l, norm_r)
      st = %{state | arena: arena}
      step = {:func_ext, st.next_step_id, clause_item.id, fvar_id, var_ty}
      {st, ext_item} = add_step(st, step, MapSet.new([{:pos, new_eq}]), clause_item.depth + 1)
      {:cont, st, [ext_item]}
    else
      _ -> {:cont, state, []}
    end
  end

  # 1. Equality Resolution: `C \/ ~(s = t)` where `s` and `t` unify under `subst`
  defp try_immediate_eq_resolution(%__MODULE__{} = state, clause_item) do
    neg_eqs =
      clause_item.lits
      |> Enum.filter(fn
        {:neg, id} -> match?({@tag_eq, _, _, _, _}, Arena.get_node(state.arena, id))
        _ -> false
      end)

    Enum.reduce_while(neg_eqs, {:cont, state, []}, fn {:neg, eq_id}, {:cont, st, acc} ->
      {@tag_eq, _, _, lhs, rhs} = Arena.get_node(st.arena, eq_id)

      case Arena.unify(st.arena, lhs, rhs) do
        {:ok, arena, subst} ->
          st = %{st | arena: arena}
          {st, parent_item, u_id} = apply_subst_if_needed(st, clause_item, subst, lhs)
          {arena, eq_uu} = Arena.mk_eq(st.arena, u_id, u_id)
          st = %{st | arena: arena}

          if MapSet.member?(parent_item.lits, {:neg, eq_uu}) do
            {st, refl_item} =
              add_step(st, {:refl, st.next_step_id, u_id}, MapSet.new([{:pos, eq_uu}]), 0)

            resolvent = MapSet.delete(parent_item.lits, {:neg, eq_uu})

            {st, res_item} =
              add_step(
                st,
                {:resolve, st.next_step_id, refl_item.id, parent_item.id, {:pos, eq_uu}},
                resolvent,
                clause_item.depth + 1
              )

            if MapSet.size(resolvent) == 0 do
              {:halt, {:proved, st, res_item.id}}
            else
              case try_immediate_eq_resolution(st, res_item) do
                {:proved, _, _} = proved ->
                  {:halt, proved}

                {:cont, st2, more} ->
                  {:cont, {:cont, st2, [res_item | more] ++ acc}}
              end
            end
          else
            {:cont, {:cont, st, acc}}
          end

        :error ->
          {:cont, {:cont, st, acc}}
      end
    end)
  end

  # 2. Factoring: unify two literals of the same polarity in `given`
  defp try_factoring(%__MODULE__{} = state, clause_item) do
    lits = MapSet.to_list(clause_item.lits)

    pairs =
      for {{pol1, a1}, idx1} <- Enum.with_index(lits),
          {{pol2, a2}, idx2} <- Enum.with_index(lits),
          idx1 < idx2 and pol1 == pol2,
          do: {a1, a2}

    Enum.reduce_while(pairs, {:cont, state, []}, fn {a1, a2}, {:cont, st, acc} ->
      case Arena.unify(st.arena, a1, a2) do
        {:ok, arena, subst} when map_size(subst) > 0 ->
          st = %{st | arena: arena}
          {st, sub_item} = emit_subst_step(st, clause_item, subst, clause_item.depth + 1)

          case try_immediate_eq_resolution(st, sub_item) do
            {:proved, _, _} = proved ->
              {:halt, proved}

            {:cont, st2, eq_items} ->
              {st3, fresh_sub} = freshen_clause_item(st2, sub_item)
              {:cont, {:cont, st3, [fresh_sub | eq_items] ++ acc}}
          end

        _ ->
          {:cont, {:cont, st, acc}}
      end
    end)
  end

  # 3. Higher-Order Predicate Reflexivity Instantiation (`P := ^ [Z]: (Z = u)`)
  defp try_ho_pred_instantiation(%__MODULE__{} = state, clause_item) do
    candidates =
      Enum.flat_map(clause_item.lits, fn
        {:neg, atom_id} ->
          case Arena.get_node(state.arena, atom_id) do
            {@tag_app, _, _, fun_id, arg_id} ->
              case Arena.get_node(state.arena, fun_id) do
                {@tag_fvar, _, f_ty, fvar_id, _} ->
                  case Map.get(state.arena.type_table, f_ty) do
                    {:arrow, dom_ty, 0} ->
                      if Arena.occurs_fvar?(state.arena, arg_id, fvar_id) do
                        []
                      else
                        [{fvar_id, dom_ty, arg_id}]
                      end

                    _ ->
                      []
                  end

                _ ->
                  []
              end

            _ ->
              []
          end

        _ ->
          []
      end)

    Enum.reduce_while(candidates, {:cont, state, []}, fn {fvar_id, dom_ty, arg_id},
                                                         {:cont, st, acc} ->
      {arena, arg_s} = Arena.shift(st.arena, arg_id, 1, 0)
      {arena, z0} = Arena.mk_bvar(arena, 0, dom_ty)
      {arena, eq_z_arg} = Arena.mk_eq(arena, z0, arg_s)
      {arena, lam_id} = Arena.mk_lam(arena, dom_ty, eq_z_arg)
      st = %{st | arena: arena}

      {st, sub_item} =
        emit_subst_step(st, clause_item, %{fvar_id => lam_id}, clause_item.depth + 1)

      case try_immediate_eq_resolution(st, sub_item) do
        {:proved, _, _} = proved ->
          {:halt, proved}

        {:cont, st2, eq_items} ->
          {:cont, {:cont, st2, eq_items ++ [sub_item | acc]}}
      end
    end)
  end

  # 4. Binary Resolution between `given` and `active` clauses
  defp try_binary_resolution(%__MODULE__{} = state, given) do
    Enum.reduce_while(state.active, {:cont, state, []}, fn active_c, {:cont, st, acc} ->
      case resolve_clause_pair(st, given, active_c) do
        {:proved, _, _} = proved ->
          {:halt, proved}

        {:cont, st2, new_items} ->
          {:cont, {:cont, st2, new_items ++ acc}}
      end
    end)
  end

  defp resolve_clause_pair(%__MODULE__{} = state, c1, c2) do
    {state, c2_disjoint} = ensure_disjoint_fvars(state, c1, c2)

    lit_pairs =
      for {pol1, a1} <- c1.lits,
          {pol2, a2} <- c2_disjoint.lits,
          pol1 != pol2 do
        if pol1 == :pos do
          {c1, a1, c2_disjoint, a2}
        else
          {c2_disjoint, a2, c1, a1}
        end
      end

    Enum.reduce_while(lit_pairs, {:cont, state, []}, fn {pos_c, pos_atom, neg_c, neg_atom},
                                                        {:cont, st, acc} ->
      case unify_literals(st.arena, pos_atom, neg_atom) do
        {:ok, arena, subst} ->
          st = %{st | arena: arena}
          depth = max(pos_c.depth, neg_c.depth) + 1

          {st, pos_inst, pos_atom_inst} = apply_subst_if_needed(st, pos_c, subst, pos_atom)
          {st, neg_inst, _neg_atom_inst} = apply_subst_if_needed(st, neg_c, subst, neg_atom)

          case find_resolvable_atom(st.arena, pos_inst.lits, neg_inst.lits, pos_atom_inst) do
            {:ok, arena, resolve_atom, pos_lit, neg_lit} ->
              st = %{st | arena: arena}

              resolvent =
                MapSet.union(
                  MapSet.delete(pos_inst.lits, pos_lit),
                  MapSet.delete(neg_inst.lits, neg_lit)
                )

              {st, res_item} =
                add_step(
                  st,
                  {:resolve, st.next_step_id, pos_inst.id, neg_inst.id, {:pos, resolve_atom}},
                  resolvent,
                  depth
                )

              if MapSet.size(resolvent) == 0 do
                {:halt, {:proved, st, res_item.id}}
              else
                case try_immediate_eq_resolution(st, res_item) do
                  {:proved, _, _} = proved ->
                    {:halt, proved}

                  {:cont, st2, eq_items} ->
                    {st3, res_fresh} = freshen_clause_item(st2, res_item)
                    {:cont, {:cont, st3, eq_items ++ [res_fresh | acc]}}
                end
              end

            :error ->
              {:cont, {:cont, st, acc}}
          end

        :error ->
          {:cont, {:cont, st, acc}}
      end
    end)
  end

  defp unify_literals(%Arena{} = arena, a1, a2) do
    case Arena.unify(arena, a1, a2) do
      {:ok, _, _} = ok ->
        ok

      :error ->
        try_const_pred_unify(arena, a1, a2)
    end
  end

  defp try_const_pred_unify(%Arena{} = arena, a1, a2) do
    case match_const_pred(arena, a1, a2) do
      {:ok, _, _} = ok -> ok
      :error -> match_const_pred(arena, a2, a1)
    end
  end

  defp match_const_pred(%Arena{} = arena, app_id, other_id) do
    case Arena.get_node(arena, app_id) do
      {@tag_app, _, _, fun_id, arg_id} ->
        case Arena.get_node(arena, fun_id) do
          {@tag_fvar, _, _f_ty, fvar_id, _} ->
            if Arena.occurs_fvar?(arena, other_id, fvar_id) or
                 MapSet.size(Arena.free_vars(arena, other_id)) > 0 do
              :error
            else
              arg_ty = Arena.type_of(arena, arg_id)
              {arena, body_s} = Arena.shift(arena, other_id, 1, 0)
              {arena, lam_id} = Arena.mk_lam(arena, arg_ty, body_s)
              {:ok, arena, %{fvar_id => lam_id}}
            end

          _ ->
            :error
        end

      _ ->
        :error
    end
  end

  defp find_resolvable_atom(%Arena{} = arena, pos_lits, neg_lits, atom_id) do
    cond do
      MapSet.member?(pos_lits, {:pos, atom_id}) and MapSet.member?(neg_lits, {:neg, atom_id}) ->
        {:ok, arena, atom_id, {:pos, atom_id}, {:neg, atom_id}}

      true ->
        case Arena.get_node(arena, atom_id) do
          {@tag_eq, _, _, l, r} ->
            {arena, sym_id} = Arena.mk_eq(arena, r, l)

            cond do
              MapSet.member?(pos_lits, {:pos, atom_id}) and
                  MapSet.member?(neg_lits, {:neg, sym_id}) ->
                {:ok, arena, atom_id, {:pos, atom_id}, {:neg, sym_id}}

              MapSet.member?(pos_lits, {:pos, sym_id}) and
                  MapSet.member?(neg_lits, {:neg, atom_id}) ->
                {:ok, arena, sym_id, {:pos, sym_id}, {:neg, atom_id}}

              true ->
                :error
            end

          _ ->
            :error
        end
    end
  end

  # 5. KBO-Oriented Superposition / Paramodulation
  defp try_superposition(%__MODULE__{} = state, given) do
    Enum.reduce_while(state.active, {:cont, state, []}, fn active_c, {:cont, st, acc} ->
      with {:cont, st, items1} <- paramod_directed(st, given, active_c),
           {:cont, st, items2} <- paramod_directed(st, active_c, given) do
        {:cont, {:cont, st, items1 ++ items2 ++ acc}}
      else
        {:proved, _, _} = proved -> {:halt, proved}
      end
    end)
  end

  defp paramod_directed(%__MODULE__{} = state, eq_clause, target_clause) do
    if MapSet.size(eq_clause.lits) > 2 or
         MapSet.size(eq_clause.lits) + MapSet.size(target_clause.lits) - 1 > state.max_clause_lits do
      {:cont, state, []}
    else
      pos_eqs =
        Enum.filter(eq_clause.lits, fn
          {:pos, id} -> match?({@tag_eq, _, _, _, _}, Arena.get_node(state.arena, id))
          _ -> false
        end)

      if pos_eqs == [] do
        {:cont, state, []}
      else
        {state, target_disjoint} = ensure_disjoint_fvars(state, eq_clause, target_clause)

        candidates =
          for {:pos, eq_id} <- pos_eqs,
              {@tag_eq, _, _, lhs, rhs} = Arena.get_node(state.arena, eq_id),
              {from_term, to_term} <- orient_equation(state.arena, lhs, rhs),
              not fvar_node?(state.arena, from_term),
              {pol, target_atom} = target_lit <- target_disjoint.lits,
              subterm_id <- non_var_subterms(state.arena, target_atom),
              Arena.type_of(state.arena, subterm_id) == Arena.type_of(state.arena, from_term) do
            {eq_id, from_term, to_term, target_lit, pol, target_atom, subterm_id}
          end

        Enum.reduce_while(candidates, {:cont, state, []}, fn {eq_id, from_term, to_term,
                                                              _target_lit, pol, target_atom,
                                                              subterm_id},
                                                             {:cont, st, acc} ->
          case Arena.unify(st.arena, from_term, subterm_id) do
            {:ok, arena, subst} ->
              st = %{st | arena: arena}
              depth = max(eq_clause.depth, target_disjoint.depth) + 1

              {st, eq_inst, eq_atom_inst} = apply_subst_if_needed(st, eq_clause, subst, eq_id)

              {st, target_inst, target_atom_inst} =
                apply_subst_if_needed(st, target_disjoint, subst, target_atom)

              {arena, from_inst} = Arena.subst_fvar(st.arena, from_term, subst)
              {arena, to_inst} = Arena.subst_fvar(arena, to_term, subst)

              {arena, rep_raw} =
                ProofChecker.replace_subterm(arena, target_atom_inst, from_inst, to_inst)

              {arena, rewritten_atom} = Arena.beta_eta_norm(arena, rep_raw)
              st = %{st | arena: arena}

              if rewritten_atom != target_atom_inst and
                   MapSet.member?(eq_inst.lits, {:pos, eq_atom_inst}) and
                   MapSet.member?(target_inst.lits, {pol, target_atom_inst}) do
                new_lits =
                  MapSet.union(
                    MapSet.delete(eq_inst.lits, {:pos, eq_atom_inst}),
                    MapSet.delete(target_inst.lits, {pol, target_atom_inst})
                  )
                  |> MapSet.put({pol, rewritten_atom})

                step =
                  {:paramod, st.next_step_id, eq_inst.id, target_inst.id, eq_atom_inst,
                   {pol, target_atom_inst}, {pol, rewritten_atom}}

                {st, para_item} = add_step(st, step, new_lits, depth)

                case try_immediate_eq_resolution(st, para_item) do
                  {:proved, _, _} = proved ->
                    {:halt, proved}

                  {:cont, st2, eq_items} ->
                    {st3, para_fresh} = freshen_clause_item(st2, para_item)
                    {:cont, {:cont, st3, eq_items ++ [para_fresh | acc]}}
                end
              else
                {:cont, {:cont, st, acc}}
              end

            :error ->
              {:cont, {:cont, st, acc}}
          end
        end)
      end
    end
  end

  defp orient_equation(%Arena{} = arena, lhs, rhs) do
    case Arena.kbo_compare(arena, lhs, rhs) do
      :gt -> [{lhs, rhs}]
      :lt -> [{rhs, lhs}]
      :eq -> []
      :inc -> [{lhs, rhs}, {rhs, lhs}]
    end
  end

  defp fvar_node?(%Arena{} = arena, term_id) do
    match?({@tag_fvar, _, _, _, _}, Arena.get_node(arena, term_id))
  end

  defp non_var_subterms(%Arena{} = arena, term_id) do
    collect_subterms(arena, term_id, MapSet.new())
    |> MapSet.to_list()
  end

  defp collect_subterms(%Arena{} = arena, term_id, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    acc =
      if tag not in [@tag_bvar, @tag_fvar] and not Arena.has_loose_bvar?(arena, term_id, 0) do
        MapSet.put(acc, term_id)
      else
        acc
      end

    case tag do
      @tag_not ->
        collect_subterms(arena, left, acc)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        acc = collect_subterms(arena, left, acc)
        collect_subterms(arena, right, acc)

      _ ->
        acc
    end
  end

  # ---------------------------------------------------------------------------
  # Substitution, Variable Standardization, & Proof DAG Extraction
  # ---------------------------------------------------------------------------

  defp apply_subst_if_needed(%__MODULE__{} = state, clause_item, subst, tracked_term_id) do
    relevant_subst =
      Map.filter(subst, fn {fvar_id, _rep} ->
        MapSet.member?(clause_item.fvar_ids, fvar_id)
      end)

    {arena, tracked_inst} = Arena.subst_fvar(state.arena, tracked_term_id, subst)
    state = %{state | arena: arena}

    if map_size(relevant_subst) == 0 do
      {state, clause_item, tracked_inst}
    else
      {state, sub_item} = emit_subst_step(state, clause_item, relevant_subst, clause_item.depth)
      {state, sub_item, tracked_inst}
    end
  end

  defp emit_subst_step(%__MODULE__{} = state, parent_item, subst_map, depth) do
    {arena, new_lits} =
      Enum.reduce(parent_item.lits, {state.arena, MapSet.new()}, fn {pol, id}, {ar, acc} ->
        {ar, id2} = Arena.subst_fvar(ar, id, subst_map)
        {ar, MapSet.put(acc, {pol, id2})}
      end)

    state = %{state | arena: arena}
    step = {:subst, state.next_step_id, parent_item.id, subst_map}
    add_step(state, step, new_lits, depth)
  end

  defp ensure_disjoint_fvars(%__MODULE__{} = state, c1, c2) do
    if MapSet.disjoint?(c1.fvar_ids, c2.fvar_ids) do
      {state, c2}
    else
      freshen_clause_item(state, c2)
    end
  end

  defp freshen_clause_item(%__MODULE__{} = state, clause_item) do
    if MapSet.size(clause_item.fvars) == 0 do
      {state, clause_item}
    else
      {arena, next_fv, subst} =
        Enum.reduce(clause_item.fvars, {state.arena, state.next_fvar_id, %{}}, fn {old_id, ty_id},
                                                                                  {ar, nf, sub} ->
          {ar, new_fv} = Arena.mk_fvar(ar, nf, ty_id)
          {ar, nf + 1, Map.put(sub, old_id, new_fv)}
        end)

      state = %{state | arena: arena, next_fvar_id: next_fv}
      emit_subst_step(state, clause_item, subst, clause_item.depth)
    end
  end

  defp add_step(%__MODULE__{} = state, step, lits, depth) do
    id = state.next_step_id
    item = clause_item(state, id, lits, depth)

    state = %{
      state
      | steps: Map.put(state.steps, id, step),
        next_step_id: id + 1
    }

    {state, item}
  end

  defp clause_item(%__MODULE__{} = state, id, lits, depth) do
    fvars =
      Enum.reduce(lits, MapSet.new(), fn {_pol, atom_id}, acc ->
        MapSet.union(acc, Arena.free_vars(state.arena, atom_id))
      end)

    fvar_ids = MapSet.new(fvars, &elem(&1, 0))

    lit_weights =
      Enum.map(lits, fn {_pol, atom_id} = lit ->
        {lit, elem(Arena.term_weight_and_vars(state.arena, atom_id), 0)}
      end)

    weight = lit_weights |> Enum.map(&elem(&1, 1)) |> Enum.sum()

    fv = clause_feature_vector(state.arena, lits)
    num_lits = MapSet.size(lits)
    num_fvars = MapSet.size(fvars)
    goal_bonus = if Enum.at(fv, 11) > 0, do: -6, else: 0

    score =
      case state.scoring_mode do
        :weight_first ->
          num_lits * 10 + weight * 2 + depth * 2

        :breadth_first ->
          depth * 20 + num_lits * 12 + weight

        :unit_focused ->
          unit_penalty = if num_lits == 1, do: 0, else: num_lits * 25
          unit_penalty + weight + num_fvars * 8 + depth * 2 + goal_bonus

        _ ->
          num_lits * 15 + weight + num_fvars * 6 + depth * 3 + goal_bonus
      end

    %{
      id: id,
      lits: lits,
      fvars: fvars,
      fvar_ids: fvar_ids,
      weight: weight,
      depth: depth,
      fv: fv,
      score: score,
      lits_by_weight: lit_weights |> Enum.sort_by(&(-elem(&1, 1))) |> Enum.map(&elem(&1, 0))
    }
    |> Map.put(:sfv, Subsumption.clause_fv(state.arena, lits))
  end

  # ---------------------------------------------------------------------------
  # Subsumption & Clause Signatures
  # ---------------------------------------------------------------------------

  defp clause_feature_vector(%Arena{} = arena, lits) do
    lit_fvs =
      Enum.map(lits, fn {_pol, atom_id} ->
        Arena.feature_vector(arena, atom_id)
      end)

    case lit_fvs do
      [] ->
        List.duplicate(0, 16)

      [first | rest] ->
        summed =
          Enum.reduce(rest, first, fn fv, acc ->
            Enum.zip_with(fv, acc, &+/2)
          end)

        List.replace_at(summed, 0, MapSet.size(lits))
    end
  end

  defp opposite(:pos), do: :neg
  defp opposite(:neg), do: :pos

  defp tautology_clause?(%Arena{} = arena, lits) do
    Enum.any?(lits, fn
      {:pos, id} ->
        MapSet.member?(lits, {:neg, id}) or
          match?({@tag_eq, _, _, s, s}, Arena.get_node(arena, id))

      _ ->
        false
    end)
  end

  # Variant signature: literals sorted by their variable-blind shape, then encoded
  # with variables numbered by first occurrence. Equal signatures imply variants
  # (the converse may fail when literals tie on shape, which only misses duplicates).
  defp canonical_clause_sig(%Arena{} = arena, lits) do
    lits
    |> Enum.sort_by(fn {pol, id} -> {pol, sig_bytes(arena, id, nil) |> elem(0)} end)
    |> Enum.map_reduce(%{}, fn {pol, id}, vars ->
      {bytes, vars} = sig_bytes(arena, id, vars)
      {{pol, bytes}, vars}
    end)
    |> elem(0)
  end

  # With `vars == nil` all variables look alike; with a map they are numbered.
  defp sig_bytes(%Arena{} = arena, term_id, vars) do
    {tag, _flags, ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_fvar when vars == nil ->
        {<<@tag_fvar, ty_id::16>>, vars}

      @tag_fvar ->
        n = Map.get(vars, left, map_size(vars))
        {<<@tag_fvar, ty_id::16, n::32>>, Map.put_new(vars, left, n)}

      @tag_const ->
        {<<@tag_const, ty_id::16, left::32>>, vars}

      @tag_bvar ->
        {<<@tag_bvar, ty_id::16, left::16>>, vars}

      @tag_skolem ->
        {<<@tag_skolem, ty_id::16, left::32>>, vars}

      @tag_comb ->
        {<<@tag_comb, ty_id::16, left::16>>, vars}

      @tag_not ->
        {inner, vars} = sig_bytes(arena, left, vars)
        {<<@tag_not, inner::binary>>, vars}

      t when t in [@tag_lam, @tag_forall] ->
        {body, vars} = sig_bytes(arena, right, vars)
        {<<t, left::16, body::binary>>, vars}

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        {l, vars} = sig_bytes(arena, left, vars)
        {r, vars} = sig_bytes(arena, right, vars)
        {<<t, l::binary, r::binary>>, vars}

      _ ->
        {<<tag, left::32>>, vars}
    end
  end

  # ---------------------------------------------------------------------------
  # Proof Extraction & LCF Verification
  # ---------------------------------------------------------------------------

  defp finalize_proof(%__MODULE__{} = state, empty_id) do
    proof_steps = extract_proof_dag(state.steps, empty_id)

    case ProofChecker.verify_refutation(state.arena, proof_steps) do
      :ok ->
        {:proved, proof_steps,
         state
         |> stats()
         |> Map.put(:proof_length, length(proof_steps))
         |> Map.put(:arena, state.arena)}

      {:error, reason} ->
        {:error, {:lcf_verification_failed, reason, proof_steps}}
    end
  end

  defp extract_proof_dag(steps_map, root_id) do
    visited = collect_ancestors(steps_map, [root_id], MapSet.new())

    visited
    |> MapSet.to_list()
    |> Enum.sort()
    |> Enum.map(&Map.fetch!(steps_map, &1))
  end

  defp collect_ancestors(_steps_map, [], visited), do: visited

  defp collect_ancestors(steps_map, [id | rest], visited) do
    if MapSet.member?(visited, id) do
      collect_ancestors(steps_map, rest, visited)
    else
      step = Map.fetch!(steps_map, id)
      parents = step_parents(step)
      collect_ancestors(steps_map, parents ++ rest, MapSet.put(visited, id))
    end
  end

  defp step_parents({:axiom, _id, _c}), do: []
  defp step_parents({:refl, _id, _t}), do: []
  defp step_parents({:symm, _id, p}), do: [p]
  defp step_parents({:trans, _id, p1, p2}), do: [p1, p2]
  defp step_parents({:subst, _id, p, _s}), do: [p]
  defp step_parents({:cong, _id, p, _eq, _arg}), do: [p]
  defp step_parents({:func_ext, _id, p, _fv, _ty}), do: [p]
  defp step_parents({:paramod, _id, p1, p2, _eq, _tl, _rl}), do: [p1, p2]
  defp step_parents({:resolve, _id, p1, p2, _lit}), do: [p1, p2]

  defp stats(%__MODULE__{} = state) do
    cutoffs = Map.get(state, :unification_cutoffs, 0)

    base = %{
      iterations: state.iterations,
      active_clauses: length(state.active),
      passive_clauses: PassiveQueue.size(state.passive),
      total_steps: state.next_step_id - 1,
      arena_nodes: map_size(state.arena.nodes),
      discarded_clauses: state.discarded_clauses,
      forward_subsumed: state.forward_subsumed,
      backward_subsumed: state.backward_subsumed,
      rewrites: state.rewrites,
      backward_rewritten: state.backward_rewritten,
      index_backend: state.active_index.backend,
      complete: state.discarded_clauses == 0 and not state.sine_filtered and cutoffs == 0
    }

    if state.cooperate == [],
      do: base,
      else: Map.put(base, :external_calls, Enum.reverse(state.coop_log))
  end

  # ---------------------------------------------------------------------------
  # External Prover Cooperation
  # ---------------------------------------------------------------------------

  defp normalize_external(name) when is_atom(name), do: {name, []}

  defp normalize_external({name, ext_opts}) when is_atom(name) and is_list(ext_opts),
    do: {name, ext_opts}

  defp cooperate(%__MODULE__{cooperate: []} = state), do: {:cont, state}

  defp cooperate(%__MODULE__{} = state) do
    state = maybe_dispatch_external(state)
    inflight = state.coop_inflight

    receive do
      {:astraea_external, ref, res} when is_map_key(inflight, ref) ->
        {call, inflight} = Map.pop(inflight, ref)
        File.rm(call.file)
        handle_external_answer(%{state | coop_inflight: inflight}, call, res)
    after
      0 -> {:cont, state}
    end
  end

  # One round of calls at a time: the next snapshot is only taken once every
  # prover of the previous round has answered.
  defp maybe_dispatch_external(%__MODULE__{} = state) do
    remaining = state.deadline_ms - System.monotonic_time(:millisecond)

    if map_size(state.coop_inflight) == 0 and
         state.iterations - state.coop_last_dispatch >= state.coop_interval and
         remaining >= @min_external_ms do
      items = coop_snapshot(state)
      clauses = Enum.map(items, & &1.lits)

      state.cooperate
      |> Enum.reduce(%{state | coop_last_dispatch: state.iterations}, fn {name, ext_opts}, st ->
        dispatch_external(st, name, ext_opts, items, clauses, remaining)
      end)
    else
      state
    end
  end

  defp coop_snapshot(%__MODULE__{} = state) do
    passive_budget = max(state.coop_max_clauses - length(state.active), 0)
    best_passive = PassiveQueue.take_best(state.passive, passive_budget)
    Enum.uniq_by(HeadIndex.values(state.units) ++ state.active ++ best_passive, & &1.id)
  end

  defp dispatch_external(%__MODULE__{} = state, name, ext_opts, items, clauses, remaining) do
    prover = Keyword.get(ext_opts, :spec, name)
    ext_opts = Keyword.update(ext_opts, :timeout_ms, remaining, &min(&1, remaining))

    written =
      try do
        External.write_clause_problem(prover, state.arena, clauses, ext_opts)
      rescue
        e in ArgumentError -> {:error, Exception.message(e)}
      end

    case written do
      {:ok, file} ->
        parent = self()
        ref = make_ref()

        # Linked, so killing this prover (e.g. by `Astraea.Portfolio`) also kills the call.
        pid =
          spawn_link(fn ->
            res =
              try do
                External.run(prover, file, ext_opts)
              rescue
                e -> {:error, e}
              end

            send(parent, {:astraea_external, ref, res})
          end)

        call = %{prover: name, pid: pid, file: file, items: List.to_tuple(items)}
        %{state | coop_inflight: Map.put(state.coop_inflight, ref, call)}

      {:error, reason} ->
        log_external(state, %{prover: name, iteration: state.iterations, error: reason})
    end
  end

  defp handle_external_answer(%__MODULE__{} = state, call, {:ok, %External.Result{} = res}) do
    entry = %{
      prover: call.prover,
      iteration: state.iterations,
      clauses_sent: tuple_size(call.items),
      szs_status: res.status,
      elapsed_ms: res.elapsed_ms
    }

    if External.SZS.classify(res.status) == :unsat do
      core_items =
        res.proof
        |> Reconstruct.core_names()
        |> Reconstruct.clause_indices()
        |> Enum.filter(&(&1 < tuple_size(call.items)))
        |> Enum.map(&elem(call.items, &1))

      reconstruct_core(state, res, core_items, Map.put(entry, :core_size, length(core_items)))
    else
      {:cont, log_external(state, entry)}
    end
  end

  defp handle_external_answer(%__MODULE__{} = state, call, {:error, reason}) do
    {:cont,
     log_external(state, %{prover: call.prover, iteration: state.iterations, error: reason})}
  end

  defp reconstruct_core(%__MODULE__{} = state, res, [], entry) do
    unverified_answer(state, res, Map.put(entry, :reconstructed, false))
  end

  defp reconstruct_core(%__MODULE__{} = state, res, core_items, entry) do
    remaining = max(state.deadline_ms - System.monotonic_time(:millisecond), 0)

    seed = %{
      steps: state.steps,
      ids: Enum.map(core_items, & &1.id),
      next_step_id: state.next_step_id,
      next_fvar_id: state.next_fvar_id
    }

    sub_opts =
      state.opts
      |> Keyword.drop([:cooperate, :seed])
      |> Keyword.merge(timeout_ms: remaining, seed: seed)

    case prove_clauses(state.arena, Enum.map(core_items, & &1.lits), sub_opts) do
      {:proved, steps, sub_stats} ->
        state = log_external(state, Map.put(entry, :reconstructed, true))

        result_stats =
          state
          |> stats()
          |> Map.merge(%{
            proof_length: sub_stats.proof_length,
            arena: sub_stats.arena,
            external_assist: Map.put(entry, :reconstructed, true)
          })

        {:done, {:proved, steps, result_stats}, state}

      other ->
        entry = Map.merge(entry, %{reconstructed: false, reconstruction: elem(other, 0)})
        unverified_answer(state, res, entry)
    end
  end

  defp unverified_answer(%__MODULE__{} = state, res, entry) do
    state = log_external(state, entry)

    if Keyword.get(state.opts, :trust_external, false) do
      result_stats =
        state
        |> stats()
        |> Map.merge(%{
          prover: entry.prover,
          input: :clauses,
          szs_status: res.status,
          proof: res.proof
        })

      {:done, {:proved_external, result_stats}, state}
    else
      {:cont, state}
    end
  end

  defp log_external(%__MODULE__{} = state, entry),
    do: %{state | coop_log: [entry | state.coop_log]}

  # Kills outstanding external calls (their MuonTrap ports close with them) and drops
  # answers that raced the kill.
  defp finish(%__MODULE__{coop_inflight: inflight}, result) do
    Enum.each(inflight, fn {ref, call} ->
      Process.unlink(call.pid)
      Process.exit(call.pid, :kill)
      File.rm(call.file)

      receive do
        {:astraea_external, ^ref, _res} -> :ok
      after
        0 -> :ok
      end
    end)

    result
  end
end
