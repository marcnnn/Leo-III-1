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

  alias Astraea.{Arena, Clausifier, Evaluator, External, ProofChecker, TptpCorpus, TptpLower}
  alias Astraea.Engine.{Demodulator, Fragment, FVIndex, HeadIndex, PassiveQueue, Subsumption}
  alias Astraea.External.Reconstruct
  alias Astraea.Input.Arith
  alias Astraea.Calculus.{ArgCong, Avatar, Choice, Cnf, EqFact, FingerprintIndex, FuncSpec, Ordering, PrimSubst, SpecialInstances, Terms, Unify}
  alias Astraea.Engine.CdclSat

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
            input_incomplete: [],
            discarded_clauses: 0,
            eval_simplify: false,
            start_reductions: nil,
            max_reductions: :infinity,
            forward_subsumed: 0,
            backward_subsumed: 0,
            rewrites: 0,
            backward_rewritten: 0,
            wide_equations: false,
            arith: false,
            higher_order: false,
            refuted: nil,
            deadline_ms: nil,
            opts: [],
            cooperate: [],
            coop_interval: 40,
            coop_max_clauses: 400,
            coop_last_dispatch: 0,
            coop_inflight: %{},
            coop_log: [],
            unification_cutoffs: 0,
            fp_index: nil,
            choice_done: MapSet.new(),
            choice_axioms: %{},
            avatar: false,
            sat_solver: nil,
            sat_atom_map: %{},
            sat_clauses: %{},
            next_sat_var: 1,
            avatar_splits: 0

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

    opts =
      opts
      |> Keyword.put(:sine_filtered, sine_filtered?(lowered, sine_limit))
      |> Keyword.put(:input_incomplete, input_incomplete(lowered))

    prove_clauses(arena, clauses, opts)
  end

  # Fragments whose clause sets are faithful in both directions, so that a model of
  # the clauses is a model of the problem (`$ite`/`$let` are definitional extensions
  # or substitutions, `$distinct` is axiomatized exactly). Proofs found through the
  # other fragments stay valid, but their saturations prove nothing: the modal
  # embedding need not match TPTP's intended semantics (SYO931^1), monomorphization
  # only covers some type instances, and arithmetic beyond ground evaluation, choice,
  # description and tuples are uninterpreted.
  @model_faithful_fragments [:thf, :tff, :fof, :cnf, :ite, :let, :distinct]

  defp input_incomplete(%TptpLower{} = lowered) do
    lowered.incomplete ++ Enum.reject(lowered.fragments, &(&1 in @model_faithful_fragments))
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
  `:max_clause_weight` counts as discarded and makes the run incomplete
  (`stats/1` reports `:complete` and `:incomplete_reasons`):
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
    * `:input_incomplete` - reasons why a model of the input clauses need not be a
      model of the problem (set by `prove_lowered/2`)
  """
  @spec prove_clauses(Arena.t(), [ProofChecker.clause()], keyword()) ::
          result() | {:proved_external, map()}
  def prove_clauses(%Arena{} = arena, input_clauses, opts \\ []) do
    {arena, _} = Arena.mk_const(arena, "$true", :o)
    {arena, _} = Arena.mk_const(arena, "$false", :o)

    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    deadline = System.monotonic_time(:millisecond) + timeout_ms
    index_opts = [backend: Keyword.get(opts, :index_backend, :auto)]

    state = %__MODULE__{
      arena: arena,
      active_index: FVIndex.new(index_opts),
      fp_index: new_fingerprints(opts),
      arith: arithmetic?(arena),
      higher_order: not Fragment.first_order?(arena, input_clauses),
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
      input_incomplete: Keyword.get(opts, :input_incomplete, []),
      eval_simplify: Keyword.get(opts, :eval_simplify, false),
      max_reductions: Keyword.get(opts, :max_reductions, :infinity),
      start_reductions: elem(Process.info(self(), :reductions), 1),
      deadline_ms: deadline,
      opts: opts,
      cooperate: opts |> Keyword.get(:cooperate, []) |> Enum.map(&normalize_external/1),
      coop_interval: Keyword.get(opts, :cooperate_interval, 40),
      coop_max_clauses: Keyword.get(opts, :cooperate_max_clauses, 400),
      avatar: Keyword.get(opts, :avatar, false),
      sat_solver: if(Keyword.get(opts, :avatar, false), do: CdclSat.new(), else: nil)
    }

    {state, seed_ids} =
      case Keyword.get(opts, :seed) do
        nil ->
          {state, nil}

        seed ->
          steps_map =
            if is_map(seed.steps),
              do: seed.steps,
              else: Map.new(seed.steps, fn s -> {elem(s, 1), s} end)

          {%{
             state
             | steps: steps_map,
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

        st =
          if calculus_opt(st, :choice, true) do
            case Choice.detect_axiom(st.arena, c_item.lits) do
              {:ok, info} ->
                info = Map.put(info, :ax_item, c_item)
                %{st | choice_axioms: Map.put(st.choice_axioms, info.choice_head, info)}

              :none ->
                st
            end
          else
            st
          end

        {add_unit(st, c_item), [c_item | acc]}
      end)

    axiom_items = Enum.reverse(axiom_items)

    # Pass 2: Condense, unit-simplify, and equality-resolve initial clauses
    Enum.reduce_while(axiom_items, {:cont, state}, fn c_item, {:cont, st} ->
      choice_ax? =
        calculus_opt(st, :choice, true) and
          Enum.any?(st.choice_axioms, fn {_head, info} -> info.ax_item.id == c_item.id end)

      if choice_ax? do
        {:cont, {:cont, st}}
      else
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
      end
    end)
  end

  defp saturation_loop(%__MODULE__{refuted: empty_id} = state) when empty_id != nil do
    finish(state, finalize_proof(state, empty_id))
  end

  defp saturation_loop(%__MODULE__{iterations: iters, max_iterations: max_iters} = state)
       when is_integer(max_iters) and iters >= max_iters do
    finish(state, {:resource_out, stats(state)})
  end


  defp saturation_loop(%__MODULE__{} = state) do
    cond do
      not is_nil(state.refuted) ->
        finish(state, finalize_proof(state, state.refuted))

      PassiveQueue.empty?(state.passive) ->
        finish(state, {:saturated, stats(state)})

      reductions_exceeded?(state) ->
        finish(state, {:resource_out, stats(state)})

      System.monotonic_time(:millisecond) >= state.deadline_ms ->
        finish(state, {:resource_out, stats(state)})

      true ->
        case cooperate(state) do
          {:done, result, state} -> finish(state, result)
          {:cont, state} -> given_clause_step(state)
        end
    end
  end

  defp reductions_exceeded?(%__MODULE__{max_reductions: max_reds, start_reductions: start_reds})
       when is_integer(max_reds) and is_integer(start_reds) do
    case Process.info(self(), :reductions) do
      {:reductions, r} -> r - start_reds >= max_reds
      _ -> false
    end
  end

  defp reductions_exceeded?(_state), do: false

  # One iteration of the given-clause loop (Leo-III `SeqLoop`): select, simplify
  # (condensation, unit simplification, demodulation), drop if redundant, else
  # simplify the processed set with it (backward subsumption and demodulation),
  # generate inferences and activate it. A clause with non-atomic literals is only
  # expanded by search-time clausification (`Calculus.Cnf`): its clauses replace it,
  # so it neither simplifies the processed set nor becomes active.
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

      {:dropped, state} ->
        saturation_loop(state)

      {:ok, state, given} ->
        cond do
          tautology_clause?(state.arena, given.lits) ->
            saturation_loop(state)

          forward_subsumed?(state, given) ->
            saturation_loop(%{state | forward_subsumed: state.forward_subsumed + 1})

          true ->
            atomic? = Cnf.atomic?(state.arena, given.lits)

            state =
              if atomic?,
                do: state |> backward_subsume(given) |> backward_demodulate(given),
                else: state

            if state.refuted do
              finish(state, finalize_proof(state, state.refuted))
            else
              case generate_inferences(state, given) do
                {:proved, state, empty_id} ->
                  finish(state, finalize_proof(state, empty_id))

                {:cont, state, new_items} ->
                  state
                  |> activate(given, atomic?)
                  |> enqueue_passive(new_items)
                  |> saturation_loop()
              end
            end
        end
    end
  end

  defp activate(%__MODULE__{} = state, _item, false = _atomic?), do: state

  defp activate(%__MODULE__{} = state, item, true = _atomic?) do
    state = %{
      state
      | active: [item | state.active],
        active_by_id: Map.put(state.active_by_id, item.id, item),
        active_index:
          FVIndex.insert(state.active_index, item.id, Subsumption.subsumption_fv(item))
    }

    state = state |> add_unit(item) |> fingerprint_activate(item) |> note_wide_equation(item)

    if state.demodulation,
      do: %{
        state
        | rules:
            Demodulator.add_rules(state.rules, state.arena, Demodulator.rules(state.arena, item, bool_rules: state.higher_order))
      },
      else: state
  end

  # Positive equations the calculus cannot fully use: `paramod_directed/3` only
  # paramodulates from clauses of at most two literals, and there is no equality
  # factoring for clauses with two positive equations.
  defp note_wide_equation(%__MODULE__{} = state, item) do
    pos_eqs =
      Enum.count(item.lits, fn {pol, atom} ->
        pol == :pos and match?({@tag_eq, _, _, _, _}, Arena.get_node(state.arena, atom))
      end)

    if pos_eqs >= 2 or (pos_eqs == 1 and MapSet.size(item.lits) > 2),
      do: %{state | wide_equations: true},
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
    |> fingerprint_remove(gone)
  end

  # Ground arithmetic evaluation of new clauses (Leo-III `GroundArithmeticEval`),
  # justified by `:arith_eval` steps. Only problems with an arithmetic sort can
  # contain interpreted symbols (search introduces none), so others skip it. A
  # clause evaluated to true is dropped; one evaluated to empty ends the search.
  defp arithmetic?(%Arena{} = arena) do
    Enum.any?(["$int", "$rat", "$real"], &Map.has_key?(arena.types, {:base, &1}))
  end

  defp arith_simplify(%__MODULE__{arith: false} = state, item), do: {state, item}

  defp arith_simplify(%__MODULE__{} = state, item) do
    case Arith.simplify_clause(state.arena, item.lits) do
      {arena, :unchanged} ->
        {%{state | arena: arena}, item}

      {arena, :tautology} ->
        {%{state | arena: arena}, :dropped}

      {arena, {:simplified, lits}} ->
        state = %{state | arena: arena}

        {state, evaluated} =
          add_step(state, {:arith_eval, state.next_step_id, item.id, lits}, lits, item.depth, item.guards)

        if MapSet.size(lits) == 0 do
          case handle_empty_clause(state, evaluated) do
            {:proved, state, empty_id} -> {%{state | refuted: empty_id}, :dropped}
            {:cont, state, _} -> {state, :dropped}
          end
        else
          {state, evaluated}
        end
    end
  end

  defp eval_simplify(%__MODULE__{} = state, :dropped), do: {state, :dropped}

  defp eval_simplify(%__MODULE__{} = state, item) do
    if state.eval_simplify or calculus_opt(state, :eval_simplify, false) do
      case Evaluator.simplify_clause(state.arena, item.lits) do
        {arena, :unchanged} ->
          {%{state | arena: arena}, item}

        {arena, :tautology} ->
          {%{state | arena: arena}, :dropped}

        {arena, {:simplified, lits}} ->
          state = %{state | arena: arena}

          {state, evaluated} =
            add_step(state, {:eval, state.next_step_id, item.id, lits}, lits, item.depth, item.guards)

          if MapSet.size(lits) == 0 do
            case handle_empty_clause(state, evaluated) do
              {:proved, state, empty_id} -> {%{state | refuted: empty_id}, :dropped}
              {:cont, state, _} -> {state, :dropped}
            end
          else
            {state, evaluated}
          end
      end
    else
      {state, item}
    end
  end

  defp simplify_forward(state, :dropped), do: {:dropped, state}

  defp simplify_forward(%__MODULE__{} = state, item) do
    case unit_simplify(state, item) do
      {:proved, st, empty_id} ->
        {:proved, st, empty_id}

      {:dropped, st} ->
        {:dropped, st}

      {:ok, st, item} ->
        if st.demodulation and map_size(st.rules) > 0 do
          case demodulate(st, item, 4) do
            {:proved, st2, empty_id} ->
              {:proved, st2, empty_id}

            {:dropped, st2} ->
              {:dropped, st2}

            {st2, rewritten, _fuel} ->
              if tautology_clause?(st2.arena, rewritten.lits),
                do: {:dropped, st2},
                else: {:ok, st2, rewritten}
          end
        else
          {:ok, st, item}
        end
    end
  end

  # ---------------------------------------------------------------------------
  # AVATAR Clause Splitting & Propositional Refutation
  # ---------------------------------------------------------------------------

  defp maybe_avatar_split(%__MODULE__{avatar: false} = state, item), do: {state, [item]}

  defp maybe_avatar_split(%__MODULE__{avatar: true} = state, item) do
    num_lits = MapSet.size(item.lits)

    if num_lits >= 2 and num_lits <= 8 and Avatar.splittable?(state.arena, item.lits) do
      comps = Avatar.components(state.arena, item.lits)

      if length(comps) >= 2 do
        do_avatar_split(state, item, comps)
      else
        {state, [item]}
      end
    else
      {state, [item]}
    end
  end

  defp do_avatar_split(%__MODULE__{} = state, item, comps) do
    # 1. Allocate a fresh SAT variable and Arena guard atom for each component
    {comp_data, state} =
      Enum.map_reduce(comps, state, fn comp_lits, st ->
        var_id = st.next_sat_var
        st = %{st | next_sat_var: var_id + 1}
        {arena, guard_atom} = Arena.mk_const(st.arena, "$avatar_g_" <> Integer.to_string(var_id), Arena.ty_o())
        st = %{st | arena: arena, sat_atom_map: Map.put(st.sat_atom_map, var_id, guard_atom)}
        {{var_id, guard_atom, comp_lits}, st}
      end)

    guard_atoms = Enum.map(comp_data, fn {_v, a, _c} -> a end)
    sat_vars = Enum.map(comp_data, fn {v, _a, _c} -> v end)

    # 2. Record the avatar split step: parent -> (g1 | g2 | ...)
    split_id = state.next_step_id
    split_step = {:avatar_split, split_id, item.id, guard_atoms}

    state = %{
      state
      | steps: Map.put(state.steps, split_id, split_step),
        next_step_id: split_id + 1,
        sat_clauses: Map.put(state.sat_clauses, sat_vars, split_id),
        avatar_splits: state.avatar_splits + 1
    }

    # 3. Add split clause to SAT solver
    {:ok, sat_solver} = CdclSat.add_clause(state.sat_solver, sat_vars)
    state = %{state | sat_solver: sat_solver}

    # 4. For each component, record {:avatar_comp, ...} and create guarded clause_item
    {comp_items, state} =
      Enum.map_reduce(comp_data, state, fn {var_id, guard_atom, comp_lits}, st ->
        comp_id = st.next_step_id
        comp_step = {:avatar_comp, comp_id, item.id, guard_atom, comp_lits}
        guards = MapSet.put(item.guards, var_id)
        comp_item = clause_item(st, comp_id, comp_lits, item.depth + 1, guards)

        st = %{
          st
          | steps: Map.put(st.steps, comp_id, comp_step),
            next_step_id: comp_id + 1
        }

        {comp_item, st}
      end)

    {state, comp_items}
  end

  defp handle_empty_clause(%__MODULE__{} = state, item) do
    if MapSet.size(item.guards) == 0 do
      {:proved, %{state | refuted: item.id}, item.id}
    else
      conflict_vars = Enum.map(item.guards, &(-&1))
      state = %{state | sat_clauses: Map.put(state.sat_clauses, conflict_vars, item.id)}

      case CdclSat.add_clause(state.sat_solver, conflict_vars) do
        {:unsat, sat_solver} ->
          state = %{state | sat_solver: sat_solver}

          case reconstruct_avatar_refutation(state) do
            {:ok, state, final_empty_id} ->
              {:proved, %{state | refuted: final_empty_id}, final_empty_id}

            :error ->
              {:cont, state, []}
          end

        {:ok, sat_solver} ->
          {:cont, %{state | sat_solver: sat_solver}, []}
      end
    end
  end

  defp reconstruct_avatar_refutation(%__MODULE__{} = state) do
    clauses_map =
      Map.new(state.sat_clauses, fn {sat_clause, step_id} ->
        clause_set =
          MapSet.new(sat_clause, fn lit ->
            var = abs(lit)
            atom_id = Map.fetch!(state.sat_atom_map, var)
            if lit > 0, do: {:pos, atom_id}, else: {:neg, atom_id}
          end)

        {step_id, clause_set}
      end)

    case Avatar.resolve_propositional_unsat(clauses_map, state.next_step_id) do
      {:ok, prop_steps, final_empty_id} ->
        state =
          Enum.reduce(prop_steps, state, fn step, st ->
            id = elem(step, 1)
            %{st | steps: Map.put(st.steps, id, step), next_step_id: max(st.next_step_id, id + 1)}
          end)

        all_steps = extract_proof_dag(state.steps, final_empty_id)

        case ProofChecker.derive_steps(state.arena, all_steps) do
          {:ok, _arena, derived} ->
            case Map.get(derived, final_empty_id) do
              empty_clause when is_struct(empty_clause, MapSet) and map_size(empty_clause.map) == 0 ->
                {:ok, state, final_empty_id}

              _other ->
                :error
            end

          {:error, _} ->
            :error
        end

      :error ->
        :error
    end
  end

  defp guards_falsified?(nil, _guards), do: false

  defp guards_falsified?(%CdclSat{} = solver, guards) do
    Enum.any?(guards, fn var ->
      Map.get(solver.values, var) == -1 and Map.get(solver.trail_levels, var) == 0
    end)
  end

  defp enqueue_passive(%__MODULE__{} = state, items) do
    {state, items} =
      if state.avatar do
        Enum.reduce(items, {state, []}, fn it, {st, acc} ->
          {st2, split_items} = maybe_avatar_split(st, it)
          {st2, acc ++ split_items}
        end)
      else
        {state, items}
      end

    {state, fresh} =
      Enum.reduce_while(items, {state, []}, fn item, {st, acc} ->
        if st.refuted do
          {:halt, {st, acc}}
        else
          if st.avatar and guards_falsified?(st.sat_solver, item.guards) do
            {:cont, {st, acc}}
          else
            {st, item} = arith_simplify(st, item)
            {st, item} = eval_simplify(st, item)

            case simplify_forward(st, item) do
              {:proved, st2, empty_id} ->
                {:halt, {%{st2 | refuted: empty_id}, acc}}

              {:dropped, st2} ->
                {:cont, {st2, acc}}

              {:ok, st2, item} ->
                num_lits = MapSet.size(item.lits)

                cond do
                  num_lits == 0 ->
                    case handle_empty_clause(st2, item) do
                      {:proved, st3, empty_id} ->
                        {:halt, {%{st3 | refuted: empty_id}, acc}}

                      {:cont, st3, _} ->
                        {:cont, {st3, acc}}
                    end

                  exceeds?(num_lits, st2.max_clause_lits) or
                      (exceeds?(item.weight, st2.max_clause_weight) and num_lits > 2) ->
                    {:cont, {%{st2 | discarded_clauses: st2.discarded_clauses + 1}, acc}}

                  tautology_clause?(st2.arena, item.lits) ->
                    {:cont, {st2, acc}}

                  true ->
                    sig = canonical_clause_sig(st2.arena, item.lits)
                    sig_key = if MapSet.size(item.guards) > 0, do: {sig, item.guards}, else: sig

                    if MapSet.member?(st2.seen_clauses, sig_key),
                      do: {:cont, {st2, acc}},
                      else: {:cont, {%{st2 | seen_clauses: MapSet.put(st2.seen_clauses, sig_key)}, [item | acc]}}
                end
            end
          end
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
        {:proved, state, empty_id} -> {:proved, state, empty_id}
        {:dropped, state} -> {:dropped, state}
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

        {state, rule_parent, eq_atom} =
          if redex.rule.eq != nil do
            {state, redex.rule.item, redex.rule.eq}
          else
            [{rule_pol, p}] = MapSet.to_list(redex.rule.item.lits)
            truth_name = if rule_pol == :pos, do: "$true", else: "$false"
            {ar, truth_const} = Arena.mk_const(state.arena, truth_name, :o)
            {ar, eq} = Arena.mk_eq(ar, p, truth_const)
            step = {:cnf, state.next_step_id, redex.rule.item.id, {rule_pol, p}, :lift_bool}
            {st, lifted} =
              add_step(%{state | arena: ar}, step, MapSet.new([{:pos, eq}]), redex.rule.item.depth, redex.rule.item.guards)

            {st, lifted, eq}
          end

        {state, rule_inst, eq_inst} =
          apply_subst_if_needed(state, rule_parent, redex.subst, eq_atom)

        {pol, atom} = lit = redex.lit
        {arena, replaced} = ProofChecker.replace_subterm(state.arena, atom, redex.from, redex.to)
        {arena, new_atom} = Arena.beta_eta_norm(arena, replaced)
        lits = item.lits |> MapSet.delete(lit) |> MapSet.put({pol, new_atom})
        state = %{state | arena: arena, rewrites: state.rewrites + 1}

        step =
          {:paramod, state.next_step_id, rule_inst.id, item.id, eq_inst, lit, {pol, new_atom}}

        guards = MapSet.union(item.guards, redex.rule.item.guards)
        {state, rewritten} = add_step(state, step, lits, item.depth, guards)
        {state, rewritten} = eliminate_truth_literals(state, rewritten)

        cond do
          MapSet.size(rewritten.lits) == 0 ->
            case handle_empty_clause(state, rewritten) do
              {:proved, st, empty_id} -> {:proved, st, empty_id}
              {:cont, st, _} -> {:dropped, st}
            end

          tautology_clause?(state.arena, rewritten.lits) ->
            {state, rewritten, 0}

          true ->
            demodulate(state, rewritten, fuel - 1, rules)
        end
    end
  end

  defp eliminate_truth_literals(state, item) do
    false_lit =
      Enum.find(item.lits, fn {pol, atom} ->
        (pol == :pos and Terms.const_named?(state.arena, atom, "$false")) or
          (pol == :neg and Terms.const_named?(state.arena, atom, "$true"))
      end)

    if false_lit do
      step = {:cnf, state.next_step_id, item.id, false_lit, :truth}
      new_lits = MapSet.delete(item.lits, false_lit)
      {state, next_item} = add_step(state, step, new_lits, item.depth, item.guards)
      eliminate_truth_literals(state, next_item)
    else
      {state, item}
    end
  end

  # Leo-III `SimplificationControl.rewritable`: active clauses the new rules of
  # `given` can rewrite leave the active set; their normal forms re-enter the
  # passive set. Candidates are prefiltered with each rule's left-hand side as a
  # feature-vector query (a redex instance is a subterm of the clause).
  defp backward_demodulate(%__MODULE__{demodulation: false} = state, _given), do: state

  defp backward_demodulate(%__MODULE__{} = state, given) do
    case Demodulator.rules(state.arena, given, bool_rules: state.higher_order) do
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
              {:proved, st, empty_id} ->
                {%{st | refuted: st.refuted || empty_id}, acc}

              {:dropped, st} ->
                {st, [{item.id, nil} | acc]}

              {st, ^item, _} ->
                {st, acc}

              {st, new_item, _} ->
                {st, [{item.id, new_item} | acc]}
            end
          end)

        state
        |> remove_active(Enum.map(rewritten, &elem(&1, 0)))
        |> Map.update!(:backward_rewritten, &(&1 + length(rewritten)))
        |> enqueue_passive(rewritten |> Enum.map(&elem(&1, 1)) |> Enum.reject(&is_nil/1))
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
            guards = MapSet.union(clause_item.guards, unit_c.guards)

            {st, res_item} =
              add_step(
                st,
                {:resolve, st.next_step_id, pos_inst.id, neg_inst.id, {:pos, resolve_atom}},
                resolvent,
                depth,
                guards
              )

            if MapSet.size(resolvent) == 0 do
              case handle_empty_clause(st, res_item) do
                {:proved, st2, empty_id} -> {:proved, st2, empty_id}
                {:cont, st2, _} -> {:dropped, st2}
              end
            else
              unit_simplify(st, res_item)
            end

          :error ->
            {:ok, state, clause_item}
        end
    end
  end

  # ---------------------------------------------------------------------------
  # Inference Generation over the higher-order calculus (`Astraea.Calculus.*`):
  # EqRes, Factoring, HO Instantiation, Resolution, Paramod, PrimSubst,
  # Extensionality, Choice, followed by search-time clausification.
  #
  # Strategy options (read from `state.opts`):
  #   :unify_depth (2), :unifier_count (2), :unify_steps (24) - pre-unification bounds
  #   :prim_subst (1, level 0-3), :prim_subst_depth (2) - primitive substitution
  #   :ext_inferences (true) - BoolExt / FuncExt on given clauses
  #   :choice (true) - Hilbert choice instances
  #   :ordered (false), :literal_selection (:none | :neg_max) - see `Calculus.Ordering`
  #   :fingerprints (true), :fingerprint_backend (:auto) - partner retrieval
  #   :paramod_flex (false) - also paramodulate into flex-headed subterms
  #   :flex_resolution (:ground | :all) - a flex-headed literal atom with arguments
  #     (never a pattern at the top level) is resolved and factored only against
  #     ground atoms or atoms containing one of its arguments under `:ground`, since
  #     by imitation it unifies with any atom
  # ---------------------------------------------------------------------------

  @eq_res_unifiers 2

  defp generate_inferences(%__MODULE__{} = state, given) do
    if Cnf.atomic?(state.arena, given.lits) do
      with {:cont, state, items0} <- try_func_ext_unit(state, given),
           {:cont, state, items1} <- try_immediate_eq_resolution(state, given),
           {:cont, state, items2} <- try_factoring(state, given),
           {:cont, state, items2b} <- try_eq_fact(state, given),
           {:cont, state, items3} <- try_ho_pred_instantiation(state, given),
           {:cont, state, items4} <- try_binary_resolution(state, given),
           {:cont, state, items5} <- try_superposition(state, given),
           {:cont, state, items5b} <- try_arg_cong(state, given),
           {:cont, state, items6} <- try_prim_subst(state, given),
           {:cont, state, items7} <- try_extensionality(state, given),
           {:cont, state, items8} <- try_func_spec(state, given),
           {:cont, state, items9} <- try_special_instances(state, given),
           {:cont, state, items10} <- try_choice(state, given) do
        clausify_items(
          state,
          items0 ++ items1 ++ items2 ++ items2b ++ items3 ++ items4 ++ items5 ++ items5b ++ items6 ++ items7 ++ items8 ++ items9 ++ items10
        )
      end
    else
      clausify_items(state, [given])
    end
  end

  defp calculus_opt(%__MODULE__{} = state, key, default),
    do: Keyword.get(state.opts, key, default)

  defp ordering(%__MODULE__{} = state), do: Ordering.opts(state.opts)

  defp cutoff(%__MODULE__{} = state, n \\ 1),
    do: %{state | unification_cutoffs: state.unification_cutoffs + n}

  # Threads `fun` over `enum`, collecting derived items until one call proves `$false`.
  defp each_inference(%__MODULE__{} = state, enum, fun) do
    Enum.reduce_while(enum, {:cont, state, []}, fn x, {:cont, st, acc} ->
      case fun.(st, x) do
        {:proved, _, _} = proved -> {:halt, proved}
        {:cont, st, items} -> {:cont, {:cont, st, items ++ acc}}
      end
    end)
  end

  # Pre-unifiers of `pairs` (`Calculus.Unify`), bounded by the strategy options.
  defp unifiers(%__MODULE__{} = state, pairs, opts \\ []) do
    bounds =
      Keyword.merge(
        [
          max_depth: calculus_opt(state, :unify_depth, 2),
          max_unifiers: calculus_opt(state, :unifier_count, 2),
          max_steps: calculus_opt(state, :unify_steps, 24)
        ],
        opts
      )

    {arena, next_fvar, substs, cut} =
      Unify.unifiers(state.arena, pairs, state.next_fvar_id, bounds)

    {cutoff(%{state | arena: arena, next_fvar_id: next_fvar}, cut), substs}
  end

  # Unifiers of two literal atoms, modulo the symmetry of a top-level equation.
  defp atom_unifiers(%__MODULE__{} = state, a1, a2) do
    problems =
      case {Arena.get_node(state.arena, a1), Arena.get_node(state.arena, a2)} do
        {{@tag_eq, _, _, l1, r1}, {@tag_eq, _, _, l2, r2}} ->
          [[{l1, l2}, {r1, r2}], [{l1, r2}, {r1, l2}]]

        _ ->
          [[{a1, a2}]]
      end

    {state, substs} =
      Enum.reduce(problems, {state, []}, fn pairs, {st, acc} ->
        {st, substs} = unifiers(st, pairs)
        {st, acc ++ substs}
      end)

    {state, Enum.uniq(substs)}
  end

  # Search-time clausification (`Calculus.Cnf`) of derived clauses via `:cnf` steps.
  defp clausify_items(%__MODULE__{} = state, items) do
    each_inference(state, items, &clausify_item(&1, &2, []))
  end

  defp clausify_item(%__MODULE__{} = state, item, opts) do
    if Cnf.atomic?(state.arena, item.lits, opts) do
      {:cont, state, [item]}
    else
      {arena, next_fvar, tree, cut} = Cnf.expand(state.arena, item.lits, state.next_fvar_id, opts)
      state = cutoff(%{state | arena: arena, next_fvar_id: next_fvar}, cut)
      replay_cnf(state, item, tree)
    end
  end

  defp replay_cnf(%__MODULE__{} = state, item, :atomic) do
    if MapSet.size(item.lits) == 0 do
      case handle_empty_clause(state, item) do
        {:proved, st, id} -> {:proved, st, id}
        {:cont, st, _} -> {:cont, st, []}
      end
    else
      {:cont, state, [item]}
    end
  end

  defp replay_cnf(%__MODULE__{} = state, _item, :tautology), do: {:cont, state, []}

  defp replay_cnf(%__MODULE__{} = state, item, {:expand, lit, branches}) do
    each_inference(state, branches, fn st, {rule, lits, sub} ->
      {st, child} = add_step(st, {:cnf, st.next_step_id, item.id, lit, rule}, lits, item.depth, item.guards)
      replay_cnf(st, child, sub)
    end)
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
      {st, ext_item} = add_step(st, step, MapSet.new([{:pos, new_eq}]), clause_item.depth + 1, clause_item.guards)
      {:cont, st, [ext_item]}
    else
      _ -> {:cont, state, []}
    end
  end

  # 1. Equality Resolution: `C \/ ~(s = t)` for every pre-unifier of `s` and `t`
  defp try_immediate_eq_resolution(%__MODULE__{} = state, clause_item) do
    neg_eqs =
      Enum.filter(clause_item.lits, fn
        {:neg, id} -> match?({@tag_eq, _, _, _, _}, Arena.get_node(state.arena, id))
        _ -> false
      end)

    each_inference(state, neg_eqs, fn st, {:neg, eq_id} ->
      {@tag_eq, _, _, lhs, rhs} = Arena.get_node(st.arena, eq_id)
      {st, substs} = unifiers(st, [{lhs, rhs}], max_unifiers: @eq_res_unifiers)
      each_inference(st, substs, &eq_resolve(&1, clause_item, lhs, &2))
    end)
  end

  defp eq_resolve(%__MODULE__{} = st, clause_item, lhs, subst) do
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
          clause_item.depth + 1,
          parent_item.guards
        )

      if MapSet.size(resolvent) == 0 do
        handle_empty_clause(st, res_item)
      else
        case try_immediate_eq_resolution(st, res_item) do
          {:proved, _, _} = proved -> proved
          {:cont, st2, more} -> {:cont, st2, [res_item | more]}
        end
      end
    else
      {:cont, st, []}
    end
  end

  # 2. Factoring: unify two literals of the same polarity in `given`, one of them eligible
  defp try_factoring(%__MODULE__{} = state, clause_item) do
    eligible = Ordering.eligible(state.arena, clause_item.lits, ordering(state))
    indexed = Enum.with_index(clause_item.lits)

    pairs =
      for {{pol1, a1} = l1, idx1} <- indexed,
          {{pol2, a2} = l2, idx2} <- indexed,
          idx1 < idx2 and pol1 == pol2,
          MapSet.member?(eligible, l1) or MapSet.member?(eligible, l2),
          atoms_compatible?(state, a1, a2),
          do: {a1, a2}

    {state, pairs} = flex_filter(state, pairs, & &1)

    each_inference(state, pairs, fn st, {a1, a2} ->
      {st, substs} = atom_unifiers(st, a1, a2)

      each_inference(st, Enum.filter(substs, &(map_size(&1) > 0)), fn st, subst ->
        {st, sub_item} = emit_subst_step(st, clause_item, subst, clause_item.depth + 1)

        case try_immediate_eq_resolution(st, sub_item) do
          {:proved, _, _} = proved ->
            proved

          {:cont, st2, eq_items} ->
            {st3, fresh_sub} = freshen_clause_item(st2, sub_item)
            {:cont, st3, [fresh_sub | eq_items]}
        end
      end)
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

    each_inference(state, candidates, fn st, {fvar_id, dom_ty, arg_id} ->
      {arena, arg_s} = Arena.shift(st.arena, arg_id, 1, 0)
      {arena, z0} = Arena.mk_bvar(arena, 0, dom_ty)
      {arena, eq_z_arg} = Arena.mk_eq(arena, z0, arg_s)
      {arena, lam_id} = Arena.mk_lam(arena, dom_ty, eq_z_arg)
      st = %{st | arena: arena}

      {st, sub_item} =
        emit_subst_step(st, clause_item, %{fvar_id => lam_id}, clause_item.depth + 1)

      case try_immediate_eq_resolution(st, sub_item) do
        {:proved, _, _} = proved -> proved
        {:cont, st2, eq_items} -> {:cont, st2, eq_items ++ [sub_item]}
      end
    end)
  end

  # 4. Binary Resolution between `given` and the fingerprint-retrieved `active` partners
  defp try_binary_resolution(%__MODULE__{} = state, given) do
    {state, partners} = resolution_partners(state, given)

    each_inference(
      state,
      Enum.filter(state.active, &partner?(partners, &1)),
      &resolve_clause_pair(&1, given, &2)
    )
  end

  defp resolve_clause_pair(%__MODULE__{} = state, c1, c2) do
    # Fingerprints are invariant under renaming: test before freshening `c2`.
    if resolvable_pairs(state, c1, c2) == [] do
      {:cont, state, []}
    else
      {state, c2_disjoint} = ensure_disjoint_fvars(state, c1, c2)

      {state, lit_pairs} =
        flex_filter(state, resolvable_pairs(state, c1, c2_disjoint), fn {_, a1, _, a2} ->
          {a1, a2}
        end)

      resolve_lit_pairs(state, lit_pairs)
    end
  end

  defp resolvable_pairs(%__MODULE__{} = state, c1, c2) do
    ord = ordering(state)

    for {pol1, a1} <- Ordering.eligible(state.arena, c1.lits, ord),
        {pol2, a2} <- Ordering.eligible(state.arena, c2.lits, ord),
        pol1 != pol2,
        atoms_compatible?(state, a1, a2) do
      if pol1 == :pos, do: {c1, a1, c2, a2}, else: {c2, a2, c1, a1}
    end
  end

  defp resolve_lit_pairs(%__MODULE__{} = state, lit_pairs) do
    each_inference(state, lit_pairs, fn st, {pos_c, pos_atom, neg_c, neg_atom} ->
      {st, substs} = unify_literals(st, pos_atom, neg_atom)
      each_inference(st, substs, &resolve_with(&1, pos_c, pos_atom, neg_c, neg_atom, &2))
    end)
  end

  defp resolve_with(%__MODULE__{} = st, pos_c, pos_atom, neg_c, neg_atom, subst) do
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

        guards = MapSet.union(pos_inst.guards, neg_inst.guards)

        {st, res_item} =
          add_step(
            st,
            {:resolve, st.next_step_id, pos_inst.id, neg_inst.id, {:pos, resolve_atom}},
            resolvent,
            depth,
            guards
          )

        if MapSet.size(resolvent) == 0 do
          handle_empty_clause(st, res_item)
        else
          case try_immediate_eq_resolution(st, res_item) do
            {:proved, _, _} = proved ->
              proved

            {:cont, st2, eq_items} ->
              {st3, res_fresh} = freshen_clause_item(st2, res_item)
              {:cont, st3, [res_fresh | eq_items]}
          end
        end

      :error ->
        {:cont, st, []}
    end
  end

  # Huet pre-unifiers of two complementary atoms (subsumes the former constant-predicate
  # abstraction `F @ a = q  ~>  F := ^ [_]: q`, which is an imitation).
  defp unify_literals(%__MODULE__{} = state, a1, a2), do: atom_unifiers(state, a1, a2)

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

  # 5. KBO-Oriented Superposition / Paramodulation with fingerprint-retrieved partners
  defp try_superposition(%__MODULE__{} = state, given) do
    {state, into_active, from_active} = paramod_partners(state, given)

    each_inference(state, state.active, fn st, active_c ->
      with {:cont, st, items1} <-
             maybe_paramod(st, partner?(into_active, active_c), given, active_c),
           {:cont, st, items2} <-
             maybe_paramod(st, partner?(from_active, active_c), active_c, given) do
        {:cont, st, items1 ++ items2}
      end
    end)
  end

  defp maybe_paramod(%__MODULE__{} = st, false, _eq_clause, _target_clause), do: {:cont, st, []}

  defp maybe_paramod(%__MODULE__{} = st, true, eq_clause, target_clause),
    do: paramod_directed(st, eq_clause, target_clause)

  defp paramod_directed(%__MODULE__{} = state, eq_clause, target_clause) do
    if MapSet.size(eq_clause.lits) > 2 or
         MapSet.size(eq_clause.lits) + MapSet.size(target_clause.lits) - 1 > state.max_clause_lits do
      {:cont, state, []}
    else
      ord = ordering(state)
      eq_eligible = Ordering.eligible(state.arena, eq_clause.lits, ord)
      sides = paramod_sides(state, eq_clause, eq_eligible)

      if sides == [] do
        {:cont, state, []}
      else
        {state, target_disjoint} = ensure_disjoint_fvars(state, eq_clause, target_clause)
        target_eligible = Ordering.eligible(state.arena, target_disjoint.lits, ord)
        state = cutoff(state, skipped_flex_targets(state, target_eligible))

        candidates =
          for {eq_id, from_term, to_term} <- sides,
              {pol, target_atom} <- target_eligible,
              subterm_id <- non_var_subterms(state, target_atom),
              Arena.type_of(state.arena, subterm_id) == Arena.type_of(state.arena, from_term),
              terms_compatible?(state, from_term, subterm_id) do
            {eq_id, from_term, to_term, pol, target_atom, subterm_id}
          end

        each_inference(state, candidates, fn st,
                                             {_eq, from_term, _to, _pol, _ta, subterm_id} = cand ->
          {st, substs} = unifiers(st, [{from_term, subterm_id}])
          each_inference(st, substs, &paramod_with(&1, eq_clause, target_disjoint, cand, &2))
        end)
      end
    end
  end

  defp paramod_with(%__MODULE__{} = st, eq_clause, target_disjoint, cand, subst) do
    {eq_id, from_term, to_term, pol, target_atom, _subterm_id} = cand
    depth = max(eq_clause.depth, target_disjoint.depth) + 1

    {st, eq_inst, eq_atom_inst} = apply_subst_if_needed(st, eq_clause, subst, eq_id)

    {st, target_inst, target_atom_inst} =
      apply_subst_if_needed(st, target_disjoint, subst, target_atom)

    {arena, from_inst} = Arena.subst_fvar(st.arena, from_term, subst)
    {arena, to_inst} = Arena.subst_fvar(arena, to_term, subst)
    {arena, rep_raw} = ProofChecker.replace_subterm(arena, target_atom_inst, from_inst, to_inst)
    {arena, rewritten_atom} = Arena.beta_eta_norm(arena, rep_raw)
    st = %{st | arena: arena}

    is_bool_eq = elem(Arena.get_node(st.arena, eq_atom_inst), 0) != 6

    {st, eq_parent_inst, eq_atom_for_paramod} =
      if is_bool_eq do
        {arena, true_const} = Arena.mk_const(st.arena, "$true", :o)
        {arena, eq} = Arena.mk_eq(arena, eq_atom_inst, true_const)
        step = {:cnf, st.next_step_id, eq_inst.id, {:pos, eq_atom_inst}, :lift_bool}
        {st, lifted} = add_step(%{st | arena: arena}, step, MapSet.new([{:pos, eq}]), eq_clause.depth, eq_inst.guards)
        {st, lifted, eq}
      else
        {st, eq_inst, eq_atom_inst}
      end

    if rewritten_atom != target_atom_inst and
         MapSet.member?(eq_parent_inst.lits, {:pos, eq_atom_for_paramod}) and
         MapSet.member?(target_inst.lits, {pol, target_atom_inst}) do
      new_lits =
        MapSet.union(
          MapSet.delete(eq_parent_inst.lits, {:pos, eq_atom_for_paramod}),
          MapSet.delete(target_inst.lits, {pol, target_atom_inst})
        )
        |> MapSet.put({pol, rewritten_atom})

      step =
        {:paramod, st.next_step_id, eq_parent_inst.id, target_inst.id, eq_atom_for_paramod,
         {pol, target_atom_inst}, {pol, rewritten_atom}}

      guards = MapSet.union(eq_parent_inst.guards, target_inst.guards)
      {st, para_item} = add_step(st, step, new_lits, depth, guards)
      {st, para_item} = eliminate_truth_literals(st, para_item)

      cond do
        MapSet.size(para_item.lits) == 0 ->
          handle_empty_clause(st, para_item)

        tautology_clause?(st.arena, para_item.lits) ->
          {:cont, st, []}

        true ->
          case try_immediate_eq_resolution(st, para_item) do
            {:proved, _, _} = proved ->
              proved

            {:cont, st2, eq_items} ->
              {st3, para_fresh} = freshen_clause_item(st2, para_item)
              {:cont, st3, [para_fresh | eq_items]}
          end
      end
    else
      {:cont, st, []}
    end
  end

  # Oriented rewrite sides `{eq_atom, from, to}` of the eligible positive equations.
  defp paramod_sides(%__MODULE__{} = state, eq_clause, eligible) do
    eq_sides =
      for {:pos, eq_id} = lit <- eq_clause.lits,
          MapSet.member?(eligible, lit),
          {@tag_eq, _, _, lhs, rhs} <- [Arena.get_node(state.arena, eq_id)],
          {from_term, to_term} <- orient_equation(state.arena, lhs, rhs),
          not fvar_node?(state.arena, from_term),
          do: {eq_id, from_term, to_term}

    bool_sides =
      if state.higher_order and MapSet.size(eq_clause.lits) == 1 do
        case hd(MapSet.to_list(eq_clause.lits)) do
          {:pos, atom_id} = lit ->
            if MapSet.member?(eligible, lit) and
                 Arena.type_of(state.arena, atom_id) == Arena.ty_o() and
                 elem(Arena.get_node(state.arena, atom_id), 0) != 6 and
                 not fvar_node?(state.arena, atom_id) do
              true_const = Arena.lookup_const(state.arena, "$true", :o)
              if true_const do
                [{atom_id, atom_id, true_const}]
              else
                []
              end
            else
              []
            end

          _ ->
            []
        end
      else
        []
      end

    eq_sides ++ bool_sides
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

  # Closed subterms with a rigid head (flex-headed ones only with `:paramod_flex`).
  defp non_var_subterms(%__MODULE__{} = state, term_id) do
    flex? = calculus_opt(state, :paramod_flex, false)

    state.arena
    |> collect_subterms(term_id, MapSet.new())
    |> Enum.filter(&(flex? or not Terms.flex?(state.arena, &1)))
  end

  # Flex-headed paramodulation targets left out without `:paramod_flex` (search cutoffs).
  defp skipped_flex_targets(%__MODULE__{} = state, lits) do
    if calculus_opt(state, :paramod_flex, false),
      do: 0,
      else:
        Enum.sum(
          for {_pol, a} <- lits,
              do:
                Enum.count(
                  collect_subterms(state.arena, a, MapSet.new()),
                  &Terms.flex?(state.arena, &1)
                )
        )
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

      @tag_lam ->
        collect_subterms(arena, right, acc)

      _ ->
        acc
    end
  end

  # 6. Primitive Substitution (Leo-III `PrimSubst`) on flexible literal heads
  defp try_prim_subst(%__MODULE__{} = state, given) do
    level = calculus_opt(state, :prim_subst, 1)

    cond do
      PrimSubst.head_vars(state.arena, given.lits) == [] ->
        {:cont, state, []}

      level == 0 or given.depth >= calculus_opt(state, :prim_subst_depth, 2) ->
        {:cont, cutoff(state), []}

      true ->
        {arena, next_fvar, substs} =
          PrimSubst.substitutions(state.arena, given.lits, state.next_fvar_id, level)

        state = %{state | arena: arena, next_fvar_id: next_fvar}

        substs =
          if calculus_opt(state, :prim_subst_filter, true) and state.units != nil do
            unit_items = HeadIndex.values(state.units)
            PrimSubst.filter_by_unit_examples(state.arena, substs, unit_items)
          else
            substs
          end

        each_inference(state, substs, fn st, subst ->
          {st, item} = emit_subst_step(st, given, subst, given.depth + 1)
          {:cont, st, [item]}
        end)
    end
  end

  # 7. Boolean and functional extensionality on the given clause (Leo-III `BoolExt`, `FuncExt`)
  defp try_extensionality(%__MODULE__{} = state, given) do
    opts = [bool_ext: true, func_ext: true]

    if calculus_opt(state, :ext_inferences, true) and
         not Cnf.atomic?(state.arena, given.lits, opts) do
      clausify_item(state, given, opts)
    else
      {:cont, state, []}
    end
  end

  # 8. Hilbert choice instances for `$choice @ P` or user choice `F @ P` occurring in the given clause
  defp try_choice(%__MODULE__{} = state, given) do
    choice_heads = Map.keys(state.choice_axioms)

    targets =
      if calculus_opt(state, :choice, true),
        do:
          state.arena
          |> Choice.predicates(given.lits, choice_heads)
          |> Enum.reject(&MapSet.member?(state.choice_done, &1)),
        else: []

    each_inference(state, targets, fn st, {op, pred} ->
      st = %{st | choice_done: MapSet.put(st.choice_done, {op, pred})}

      case op do
        :builtin ->
          fvar = st.next_fvar_id
          st = %{st | next_fvar_id: fvar + 1}

          case ProofChecker.choice_instance(st.arena, pred, fvar) do
            {:ok, arena, clause} ->
              {st, item} =
                add_step(
                  %{st | arena: arena},
                  {:choice, st.next_step_id, pred, fvar},
                  clause,
                  given.depth
                )

              {:cont, st, [item]}

            :error ->
              {:cont, st, []}
          end

        user_head ->
          case Map.fetch(st.choice_axioms, user_head) do
            {:ok, info} ->
              {arena, fresh_witness} = Arena.mk_fvar(st.arena, st.next_fvar_id, info.dom_ty)
              subst = %{info.pred_fvar_id => pred, info.witness_fvar_id => fresh_witness}
              st = %{st | arena: arena, next_fvar_id: st.next_fvar_id + 1}
              {st, item} = emit_subst_step(st, info.ax_item, subst, given.depth)
              {:cont, st, [item]}

            :error ->
              {:cont, st, []}
          end
      end
    end)
  end


  # 9. Function synthesis via choice (`Calculus.FuncSpec`)
  defp try_func_spec(%__MODULE__{} = state, given) do
    if calculus_opt(state, :funcspec, false) do
      choice_heads = Map.keys(state.choice_axioms)
      {arena, candidates} = FuncSpec.candidates(state.arena, given, choice_heads)
      state = %{state | arena: arena}

      each_inference(state, candidates, fn st, {var_id, synthesized_term} ->
        {st, item} = emit_subst_step(st, given, %{var_id => synthesized_term}, given.depth + 1)
        {:cont, st, [item]}
      end)
    else
      {:cont, state, []}
    end
  end

# 11. Higher-Order Superposition: Argument Congruence (`Calculus.ArgCong`)
  defp try_arg_cong(%__MODULE__{} = state, given) do
    if state.higher_order and given.depth <= calculus_opt(state, :arg_cong_depth, 2) do
      candidates = ArgCong.candidates(state.arena, given)

      each_inference(state, candidates, fn st, {eq_id, lhs, rhs, dom_ty} ->
        next_fvar = st.next_fvar_id
        {arena, x_var} = Arena.mk_fvar(st.arena, next_fvar, dom_ty)
        {arena, fa} = Arena.mk_app(arena, lhs, x_var)
        {arena, ga} = Arena.mk_app(arena, rhs, x_var)
        {arena, fa_norm} = Arena.beta_eta_norm(arena, fa)
        {arena, ga_norm} = Arena.beta_eta_norm(arena, ga)
        {arena, new_eq} = Arena.mk_eq(arena, fa_norm, ga_norm)

        new_lits =
          given.lits
          |> MapSet.delete({:pos, eq_id})
          |> MapSet.put({:pos, new_eq})

        st = %{st | arena: arena, next_fvar_id: next_fvar + 1}
        step = {:cong, st.next_step_id, given.id, eq_id, x_var}
        {st, item} = add_step(st, step, new_lits, given.depth + 1, given.guards)
        {st2, fresh_item} = freshen_clause_item(st, item)
        {:cont, st2, [fresh_item]}
      end)
    else
      {:cont, state, []}
    end
  end

  # 12. Higher-Order Superposition: Equality Factoring (`Calculus.EqFact`)
  defp try_eq_fact(%__MODULE__{} = state, given) do
    if MapSet.size(given.lits) >= 2 and given.depth <= calculus_opt(state, :eq_fact_depth, 3) do
      pairs = EqFact.candidate_pairs(state.arena, given)

      each_inference(state, pairs, fn st, {eq1_id, eq2_id, side1, side2, _rem1, _rem2} ->
        {st, substs} = unifiers(st, [{side1, side2}])

        each_inference(st, substs, fn s, subst ->
          {s, sub_item, {eq1_sub, eq2_sub}} =
            apply_subst_to_pair(s, given, subst, eq1_id, eq2_id)

          if eq1_sub != eq2_sub and MapSet.member?(sub_item.lits, {:pos, eq1_sub}) and MapSet.member?(sub_item.lits, {:pos, eq2_sub}) do
            {@tag_eq, _, _, l1, r1} = Arena.get_node(s.arena, eq1_sub)
            {@tag_eq, _, _, l2, r2} = Arena.get_node(s.arena, eq2_sub)

            case ProofChecker.match_eq_sides(l1, r1, l2, r2) do
            {_common, rem_a, rem_b} ->
              {arena, neg_eq} = Arena.mk_eq(s.arena, rem_a, rem_b)
              s = %{s | arena: arena}

              new_lits =
                sub_item.lits
                |> MapSet.delete({:pos, eq1_sub})
                |> MapSet.put({:neg, neg_eq})

              step = {:eq_fact, s.next_step_id, sub_item.id, eq1_sub, eq2_sub}
              {s, fact_item} = add_step(s, step, new_lits, sub_item.depth + 1, sub_item.guards)

              case try_immediate_eq_resolution(s, fact_item) do
                {:proved, _, _} = proved ->
                  proved

                {:cont, s2, eq_items} ->
                  {s3, fresh_item} = freshen_clause_item(s2, fact_item)
                  {:cont, s3, [fresh_item | eq_items]}
              end

            nil ->
                {:cont, s, []}
            end
          else
            {:cont, s, []}
          end
        end)
      end)
    else
      {:cont, state, []}
    end
  end

  defp apply_subst_to_pair(%__MODULE__{} = state, clause_item, subst, term1, term2) do
    relevant_subst =
      Map.filter(subst, fn {fvar_id, _rep} ->
        MapSet.member?(clause_item.fvar_ids, fvar_id)
      end)

    {arena, t1_inst} = Arena.subst_fvar(state.arena, term1, subst)
    {arena, t2_inst} = Arena.subst_fvar(arena, term2, subst)
    state = %{state | arena: arena}

    if map_size(relevant_subst) == 0 do
      {state, clause_item, {t1_inst, t2_inst}}
    else
      {state, sub_item} = emit_subst_step(state, clause_item, relevant_subst, clause_item.depth)
      {state, sub_item, {t1_inst, t2_inst}}
    end
  end

  # 10. Quantifier instantiation with canonical terms (`Calculus.SpecialInstances`)
  defp try_special_instances(%__MODULE__{} = state, given) do
    spec_opt = calculus_opt(state, :special_instances, false)
    enabled? = spec_opt == true or (is_integer(spec_opt) and spec_opt > 0)

    if enabled? and given.depth <= 2 do
      choice_heads = Map.keys(state.choice_axioms)
      {arena, candidates} = SpecialInstances.candidates(state.arena, given, choice_heads)
      state = %{state | arena: arena}

      each_inference(state, candidates, fn st, {var_id, terms} ->
        Enum.reduce_while(terms, {:cont, st, []}, fn term, {:cont, s, acc} ->
          {s, item} = emit_subst_step(s, given, %{var_id => term}, given.depth + 1)
          {:cont, {:cont, s, [item | acc]}}
        end)
      end)
    else
      {:cont, state, []}
    end
  end
  # ---------------------------------------------------------------------------
  # Fingerprint-Indexed Partner Retrieval (`Calculus.FingerprintIndex`)
  # ---------------------------------------------------------------------------

  # The three indexes (literal atoms, paramodulation targets, rewrite sides) follow
  # the active set: the loop indexes a clause when it becomes active
  # (`fingerprint_activate/2`) and tombstones it when redundancy elimination removes
  # it (`fingerprint_remove/2`).
  defp new_fingerprints(opts) do
    if Keyword.get(opts, :fingerprints, true) do
      %{
        atoms: FingerprintIndex.new(),
        subterms: FingerprintIndex.new(),
        sides: FingerprintIndex.new(),
        ids: MapSet.new()
      }
    end
  end

  defp fingerprint_activate(%__MODULE__{fp_index: nil} = state, _item), do: state

  defp fingerprint_activate(%__MODULE__{} = state, item),
    do: %{state | fp_index: index_clause(state, state.fp_index, item)}

  defp fingerprint_remove(%__MODULE__{fp_index: nil} = state, _ids), do: state

  defp fingerprint_remove(%__MODULE__{} = state, ids),
    do: %{state | fp_index: drop_indexed(state.fp_index, ids)}

  defp drop_indexed(fp, removed) do
    gone? = fn
      {id, _pol} -> MapSet.member?(removed, id)
      id -> MapSet.member?(removed, id)
    end

    %{
      fp
      | atoms: FingerprintIndex.delete_where(fp.atoms, gone?),
        subterms: FingerprintIndex.delete_where(fp.subterms, gone?),
        sides: FingerprintIndex.delete_where(fp.sides, gone?),
        ids: MapSet.difference(fp.ids, removed)
    }
  end

  defp index_clause(%__MODULE__{} = state, fp, item) do
    insert = fn index, term, payload ->
      elem(FingerprintIndex.insert(index, state.arena, term, payload), 0)
    end

    sides = if MapSet.size(item.lits) <= 2, do: paramod_sides(state, item, item.lits), else: []

    %{
      fp
      | atoms:
          Enum.reduce(item.lits, fp.atoms, fn {pol, a}, idx -> insert.(idx, a, {item.id, pol}) end),
        subterms:
          for(
            {_pol, a} <- item.lits,
            s <- non_var_subterms(state, a),
            reduce: fp.subterms,
            do: (idx -> insert.(idx, s, item.id))
          ),
        sides:
          Enum.reduce(sides, fp.sides, fn {_eq, from, _to}, idx -> insert.(idx, from, item.id) end),
        ids: MapSet.put(fp.ids, item.id)
    }
  end

  defp partner?(:all, _clause), do: true
  defp partner?(ids, clause), do: MapSet.member?(ids, clause.id)

  defp query_ids(%__MODULE__{} = state, index, terms) do
    fps = Enum.map(terms, &FingerprintIndex.fingerprint(state.arena, &1))
    opts = [backend: calculus_opt(state, :fingerprint_backend, :auto)]
    FingerprintIndex.query(index, fps, :unify, opts)
  end

  # Active clauses with a literal of opposite polarity whose atom may unify with a
  # literal of `given` (top-level equations are also queried swapped).
  defp resolution_partners(%__MODULE__{fp_index: nil} = state, _given), do: {state, :all}

  defp resolution_partners(%__MODULE__{} = state, given) do
    {queries, arena} =
      Enum.flat_map_reduce(given.lits, state.arena, fn {pol, atom}, ar ->
        case Arena.get_node(ar, atom) do
          {@tag_eq, _, _, l, r} ->
            {ar, swapped} = Arena.mk_eq(ar, r, l)
            {[{pol, atom}, {pol, swapped}], ar}

          _ ->
            {[{pol, atom}], ar}
        end
      end)

    state = %{state | arena: arena}
    rows = query_ids(state, state.fp_index.atoms, Enum.map(queries, &elem(&1, 1)))

    partners =
      for {{pol, _atom}, hits} <- Enum.zip(queries, rows),
          {id, other_pol} <- hits,
          other_pol != pol,
          into: MapSet.new(),
          do: id

    {state, partners}
  end

  # `{into_active, from_active}`: active clauses `given` can rewrite, and active clauses
  # whose rewrite sides may unify with a subterm of `given`.
  defp paramod_partners(%__MODULE__{fp_index: nil} = state, _given), do: {state, :all, :all}

  defp paramod_partners(%__MODULE__{} = state, given) do
    from_terms =
      if MapSet.size(given.lits) <= 2,
        do: for({_eq, from, _to} <- paramod_sides(state, given, given.lits), do: from),
        else: []

    subterms = for {_pol, a} <- given.lits, s <- non_var_subterms(state, a), uniq: true, do: s

    into =
      state |> query_ids(state.fp_index.subterms, from_terms) |> List.flatten() |> MapSet.new()

    from = state |> query_ids(state.fp_index.sides, subterms) |> List.flatten() |> MapSet.new()
    {state, into, from}
  end

  # `:flex_resolution` policy; skipped pairs are counted as search cutoffs.
  defp flex_filter(%__MODULE__{} = state, pairs, atoms_of) do
    {kept, skipped} =
      Enum.split_with(pairs, fn pair ->
        {a1, a2} = atoms_of.(pair)
        flex_policy?(state, a1, a2)
      end)

    {cutoff(state, length(skipped)), kept}
  end

  defp flex_policy?(%__MODULE__{} = state, a1, a2) do
    calculus_opt(state, :flex_resolution, :ground) == :all or
      (flex_ok?(state.arena, a1, a2) and flex_ok?(state.arena, a2, a1))
  end

  # `F @ args` may meet `other` if `other` is ground, contains one of the `args` (the
  # non-vacuous abstraction case of Entry 006) or has a head of the type of `F` applied
  # to as many arguments (first-order decomposition `F := h`).
  defp flex_ok?(arena, atom, other) do
    {head, args} = Terms.spine(arena, atom)
    {other_head, other_args} = Terms.spine(arena, other)

    args == [] or not Terms.fvar?(arena, head) or not Terms.has_fvar?(arena, other) or
      Enum.any?(args, &Terms.subterm?(arena, other, &1)) or
      (length(other_args) == length(args) and
         Arena.type_of(arena, other_head) == Arena.type_of(arena, head)) or
      (miller_pattern_args?(arena, args) and
         not Arena.occurs_fvar?(arena, other, elem(Arena.get_node(arena, head), 3)))
  end

  defp miller_pattern_args?(arena, args) do
    length(args) > 0 and
      Enum.all?(args, &(Terms.bvar?(arena, &1) or Terms.fvar?(arena, &1))) and
      length(Enum.uniq(args)) == length(args)
  end

  # Pairwise fingerprint pre-filter for literal atoms (modulo equation symmetry).
  defp atoms_compatible?(%__MODULE__{} = state, a1, a2) do
    case {Arena.get_node(state.arena, a1), Arena.get_node(state.arena, a2)} do
      {{@tag_eq, _, _, l1, r1}, {@tag_eq, _, _, l2, r2}} ->
        (terms_compatible?(state, l1, l2) and terms_compatible?(state, r1, r2)) or
          (terms_compatible?(state, l1, r2) and terms_compatible?(state, r1, l2))

      _ ->
        terms_compatible?(state, a1, a2)
    end
  end

  defp terms_compatible?(%__MODULE__{} = state, s, t) do
    not calculus_opt(state, :fingerprints, true) or
      FingerprintIndex.compatible?(
        :unify,
        FingerprintIndex.fingerprint(state.arena, s),
        FingerprintIndex.fingerprint(state.arena, t)
      )
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
    add_step(state, step, new_lits, depth, parent_item.guards)
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

  defp add_step(%__MODULE__{} = state, step, lits, depth, guards \\ MapSet.new()) do
    id = state.next_step_id
    item = clause_item(state, id, lits, depth, guards)

    state = %{
      state
      | steps: Map.put(state.steps, id, step),
        next_step_id: id + 1
    }

    {state, item}
  end

  defp clause_item(%__MODULE__{} = state, id, lits, depth, guards \\ MapSet.new()) do
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
      guards: guards,
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
          match?({@tag_eq, _, _, s, s}, Arena.get_node(arena, id)) or
          Terms.const_named?(arena, id, "$true")

      {:neg, id} ->
        Terms.const_named?(arena, id, "$false")
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
  defp step_parents(step), do: ProofChecker.step_parents(step)

  defp stats(%__MODULE__{} = state) do
    reasons = incomplete_reasons(state)

    reds =
      case Process.info(self(), :reductions) do
        {:reductions, r} ->
          if is_integer(state.start_reductions), do: r - state.start_reductions, else: r

        _ ->
          0
      end

    base = %{
      iterations: state.iterations,
      reductions: reds,
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
      unification_cutoffs: state.unification_cutoffs,
      complete: reasons == [],
      incomplete_reasons: reasons,
      avatar_splits: state.avatar_splits
    }

    if state.cooperate == [],
      do: base,
      else: Map.put(base, :external_calls, Enum.reverse(state.coop_log))
  end

  # Why a saturated run does not show satisfiability (empty: it does, relative to
  # the calculus). A finite `:max_clause_lits` also makes paramodulation skip
  # partners silently, so it counts even when nothing was discarded at enqueue;
  # so does an active equation the calculus cannot fully use (`note_wide_equation/2`),
  # and input outside the first-order fragment (`Engine.Fragment`). Subsumption,
  # condensation, unit simplification and tautology deletion only remove clauses an
  # instance of a kept clause covers, which every lifted inference of this calculus
  # preserves (blocked flex inferences count as unification cutoffs). Demodulation
  # relies on the ordered-superposition redundancy criterion this calculus does not
  # guarantee, so a rewrite makes the run incomplete.
  defp incomplete_reasons(%__MODULE__{} = state) do
    [
      discarded: state.discarded_clauses > 0,
      clause_lits_limit: state.max_clause_lits != :infinity,
      reductions_limit: state.max_reductions != :infinity,
      higher_order: state.higher_order,
      wide_equations: state.wide_equations,
      demodulation: state.rewrites > 0,
      sine: state.sine_filtered,
      input: state.input_incomplete != [],
      partial_input: Keyword.has_key?(state.opts, :seed),
      unification_cutoffs: state.unification_cutoffs > 0
    ]
    |> Enum.filter(&elem(&1, 1))
    |> Enum.map(&elem(&1, 0))
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
