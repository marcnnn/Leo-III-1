defmodule Astraea.Prover do
  @moduledoc """
  Higher-Order THF0 Given-Clause Micro-Prover & OTP Portfolio Runner.

  Implements a discount-style saturation loop over `Astraea.Arena` terms with:
  - Clause Condensation (`condense_clause/2` via `:subst`)
  - Eager Unit-Clause Subsumption Resolution (`unit_simplify/2` via `:subst` + `:resolve`)
  - Equality Resolution (`~(s = t)` via unification + `:refl` + `:resolve`)
  - Positive & Negative Factoring (`:subst`)
  - Positive Functional Extensionality (`:func_ext` xi-rule)
  - Binary Resolution with higher-order pattern/abstraction unification (`:subst` + `:resolve`)
  - KBO-oriented Superposition / Paramodulation (`:subst` + `:paramod`)
  - Higher-Order Predicate Reflexivity Instantiation (`P := ^ [Z]: (Z = u)`)
  - Feature-Vector (`FVIndex`) forward subsumption

  Every refutation (`SZS status Theorem`) constructs a minimal DAG of primitive inference
  steps and passes it through `Astraea.ProofChecker.verify_refutation/2` before returning.

  With `:cooperate`, the loop periodically hands its current clause set to external
  provers (Leo-III style cooperation, see `Astraea.External`). An external refutation
  is reconstructed by a seeded sub-search on its unsat core whose proof is spliced onto
  the existing derivations of the core clauses, so cooperation never weakens the LCF
  guarantee unless `:trust_external` is set.
  """

  alias Astraea.{Arena, Clausifier, External, ProofChecker, TptpCorpus, TptpLower}
  alias Astraea.External.Reconstruct
  alias Astraea.Calculus.{Choice, Cnf, FingerprintIndex, Ordering, PrimSubst, Terms, Unify}

  # Below this remaining budget an external call cannot finish in time.
  @min_external_ms 300

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
            passive: [],
            units: [],
            seen_clauses: MapSet.new(),
            iterations: 0,
            max_iterations: 450,
            max_clause_lits: 6,
            max_clause_weight: 45,
            scoring_mode: :goal_directed,
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
            choice_done: MapSet.new()

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

    prove_clauses(arena, clauses, opts)
  end

  @doc """
  Saturates `input_clauses`. Besides the strategy options (`:timeout_ms`,
  `:max_iterations`, `:max_clause_lits`, `:max_clause_weight`, `:scoring_mode`):
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
  """
  @spec prove_clauses(Arena.t(), [ProofChecker.clause()], keyword()) ::
          result() | {:proved_external, map()}
  def prove_clauses(%Arena{} = arena, input_clauses, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2_500)
    max_iters = Keyword.get(opts, :max_iterations, 450)
    max_lits = Keyword.get(opts, :max_clause_lits, 6)
    max_weight = Keyword.get(opts, :max_clause_weight, 45)
    scoring_mode = Keyword.get(opts, :scoring_mode, :goal_directed)
    deadline = System.monotonic_time(:millisecond) + timeout_ms

    state = %__MODULE__{
      arena: arena,
      max_iterations: max_iters,
      max_clause_lits: max_lits,
      max_clause_weight: max_weight,
      scoring_mode: scoring_mode,
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

        st =
          if MapSet.size(clause) == 1 and length(st.units) < 48 do
            %{st | units: [c_item | st.units]}
          else
            st
          end

        {st, [c_item | acc]}
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

  defp saturation_loop(%__MODULE__{passive: []} = state) do
    finish(state, {:saturated, stats(state)})
  end

  defp saturation_loop(%__MODULE__{iterations: iters, max_iterations: max_iters} = state)
       when iters >= max_iters do
    finish(state, {:resource_out, stats(state)})
  end

  defp saturation_loop(%__MODULE__{} = state) do
    if System.monotonic_time(:millisecond) >= state.deadline_ms do
      finish(state, {:resource_out, stats(state)})
    else
      case cooperate(state) do
        {:done, result, state} -> finish(state, result)
        {:cont, state} -> given_clause_step(state)
      end
    end
  end

  defp given_clause_step(%__MODULE__{} = state) do
    {given, rest_passive} = pop_best_passive(state.passive, state.iterations)
    state = %{state | passive: rest_passive, iterations: state.iterations + 1}
    {state, given} = condense_clause(state, given)

    case unit_simplify(state, given) do
      {:proved, state, empty_id} ->
        finish(state, finalize_proof(state, empty_id))

      {:ok, state, given} ->
        if forward_subsumed?(state.arena, state.active, given) do
          saturation_loop(state)
        else
          case generate_inferences(state, given) do
            {:proved, state, empty_id} ->
              finish(state, finalize_proof(state, empty_id))

            {:cont, state, new_items} ->
              units =
                if MapSet.size(given.lits) == 1 and length(state.units) < 48 do
                  [given | state.units]
                else
                  state.units
                end

              state = %{state | active: [given | state.active], units: units}
              state = enqueue_passive(state, new_items)
              saturation_loop(state)
          end
        end
    end
  end

  defp pop_best_passive([single], _iter), do: {single, []}

  defp pop_best_passive(passive, iter) do
    target =
      if rem(iter, 4) == 3 do
        Enum.min_by(passive, & &1.id)
      else
        Enum.min_by(passive, & &1.score)
      end

    {target, List.delete(passive, target)}
  end

  defp enqueue_passive(%__MODULE__{} = state, items) do
    Enum.reduce(items, state, fn item, st ->
      num_lits = MapSet.size(item.lits)

      cond do
        num_lits > st.max_clause_lits ->
          st

        item.weight > st.max_clause_weight and num_lits > 2 ->
          st

        tautology_clause?(st.arena, item.lits) ->
          st

        true ->
          sig = canonical_clause_sig(st.arena, item.lits)

          if MapSet.member?(st.seen_clauses, sig) or
               forward_subsumed?(st.arena, st.active, item) do
            st
          else
            %{
              st
              | passive: [item | st.passive],
                seen_clauses: MapSet.put(st.seen_clauses, sig)
            }
          end
      end
    end)
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
  defp unit_simplify(%__MODULE__{units: []} = state, clause_item),
    do: {:ok, state, clause_item}

  defp unit_simplify(%__MODULE__{} = state, clause_item) do
    match_res =
      Enum.find_value(clause_item.lits, fn {pol, target_atom} ->
        Enum.find_value(state.units, fn unit_c ->
          [{unit_pol, unit_atom}] = MapSet.to_list(unit_c.lits)

          if unit_pol != pol and unit_c.id != clause_item.id do
            case Arena.match_pattern(state.arena, unit_atom, target_atom) do
              {:ok, subst} -> {pol, target_atom, unit_c, unit_pol, unit_atom, subst}
              :error -> nil
            end
          else
            nil
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
      state = sync_fingerprints(state)

      with {:cont, state, items0} <- try_func_ext_unit(state, given),
           {:cont, state, items1} <- try_immediate_eq_resolution(state, given),
           {:cont, state, items2} <- try_factoring(state, given),
           {:cont, state, items3} <- try_ho_pred_instantiation(state, given),
           {:cont, state, items4} <- try_binary_resolution(state, given),
           {:cont, state, items5} <- try_superposition(state, given),
           {:cont, state, items6} <- try_prim_subst(state, given),
           {:cont, state, items7} <- try_extensionality(state, given),
           {:cont, state, items8} <- try_choice(state, given) do
        clausify_items(
          state,
          items0 ++ items1 ++ items2 ++ items3 ++ items4 ++ items5 ++ items6 ++ items7 ++ items8
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
    if MapSet.size(item.lits) == 0, do: {:proved, state, item.id}, else: {:cont, state, [item]}
  end

  defp replay_cnf(%__MODULE__{} = state, _item, :tautology), do: {:cont, state, []}

  defp replay_cnf(%__MODULE__{} = state, item, {:expand, lit, branches}) do
    each_inference(state, branches, fn st, {rule, lits, sub} ->
      {st, child} = add_step(st, {:cnf, st.next_step_id, item.id, lit, rule}, lits, item.depth)
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
      {st, ext_item} = add_step(st, step, MapSet.new([{:pos, new_eq}]), clause_item.depth + 1)
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
          clause_item.depth + 1
        )

      if MapSet.size(resolvent) == 0 do
        {:proved, st, res_item.id}
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
          proved

        {:cont, st2, eq_items} ->
          {st3, para_fresh} = freshen_clause_item(st2, para_item)
          {:cont, st3, [para_fresh | eq_items]}
      end
    else
      {:cont, st, []}
    end
  end

  # Oriented rewrite sides `{eq_atom, from, to}` of the eligible positive equations.
  defp paramod_sides(%__MODULE__{} = state, eq_clause, eligible) do
    for {:pos, eq_id} = lit <- eq_clause.lits,
        MapSet.member?(eligible, lit),
        {@tag_eq, _, _, lhs, rhs} <- [Arena.get_node(state.arena, eq_id)],
        {from_term, to_term} <- orient_equation(state.arena, lhs, rhs),
        not fvar_node?(state.arena, from_term),
        do: {eq_id, from_term, to_term}
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

  # 8. Hilbert choice instances for `$choice @ P` occurring in the given clause
  defp try_choice(%__MODULE__{} = state, given) do
    preds =
      if calculus_opt(state, :choice, true),
        do:
          state.arena
          |> Choice.predicates(given.lits)
          |> Enum.reject(&MapSet.member?(state.choice_done, &1)),
        else: []

    each_inference(state, preds, fn st, pred ->
      fvar = st.next_fvar_id
      st = %{st | next_fvar_id: fvar + 1, choice_done: MapSet.put(st.choice_done, pred)}

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
    end)
  end

  # ---------------------------------------------------------------------------
  # Fingerprint-Indexed Partner Retrieval (`Calculus.FingerprintIndex`)
  # ---------------------------------------------------------------------------

  # Brings the three indexes (literal atoms, paramodulation targets, rewrite sides) in
  # line with `state.active`: new active clauses are appended, dropped ones tombstoned.
  defp sync_fingerprints(%__MODULE__{} = state) do
    if calculus_opt(state, :fingerprints, true) do
      fp =
        state.fp_index ||
          %{
            atoms: FingerprintIndex.new(),
            subterms: FingerprintIndex.new(),
            sides: FingerprintIndex.new(),
            ids: MapSet.new()
          }

      removed = MapSet.difference(fp.ids, MapSet.new(state.active, & &1.id))
      fp = if MapSet.size(removed) == 0, do: fp, else: drop_indexed(fp, removed)

      fp =
        state.active
        |> Enum.reject(&MapSet.member?(fp.ids, &1.id))
        |> Enum.reduce(fp, &index_clause(state, &2, &1))

      %{state | fp_index: fp}
    else
      state
    end
  end

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
         Arena.type_of(arena, other_head) == Arena.type_of(arena, head))
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

    weight =
      Enum.reduce(lits, 0, fn {_pol, atom_id}, acc ->
        {w, _v} = Arena.term_weight_and_vars(state.arena, atom_id)
        acc + w
      end)

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
      score: score
    }
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

  defp forward_subsumed?(%Arena{} = _arena, active_list, cand) do
    Enum.any?(active_list, fn act ->
      MapSet.size(act.lits) <= MapSet.size(cand.lits) and
        Arena.fv_subsumes?(act.fv, cand.fv) and
        MapSet.size(act.fvars) == 0 and
        MapSet.subset?(act.lits, cand.lits)
    end)
  end

  defp tautology_clause?(%Arena{} = arena, lits) do
    Enum.any?(lits, fn
      {:pos, id} ->
        MapSet.member?(lits, {:neg, id}) or
          match?({@tag_eq, _, _, s, s}, Arena.get_node(arena, id))

      _ ->
        false
    end)
  end

  defp canonical_clause_sig(%Arena{} = arena, lits) do
    lits
    |> Enum.map(fn {pol, id} ->
      {pol, mask_fvars_bytes(arena, id)}
    end)
    |> Enum.sort()
  end

  defp mask_fvars_bytes(%Arena{} = arena, term_id) do
    {tag, _flags, ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_fvar ->
        <<@tag_fvar, ty_id::16>>

      @tag_const ->
        <<@tag_const, ty_id::16, left::32>>

      @tag_bvar ->
        <<@tag_bvar, ty_id::16, left::16>>

      @tag_skolem ->
        <<@tag_skolem, ty_id::16, left::32>>

      @tag_comb ->
        <<@tag_comb, ty_id::16, left::16>>

      @tag_not ->
        <<@tag_not, mask_fvars_bytes(arena, left)::binary>>

      t when t in [@tag_lam, @tag_forall] ->
        <<t, left::16, mask_fvars_bytes(arena, right)::binary>>

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        <<t, mask_fvars_bytes(arena, left)::binary, mask_fvars_bytes(arena, right)::binary>>

      _ ->
        <<tag, left::32>>
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
    base = %{
      iterations: state.iterations,
      active_clauses: length(state.active),
      passive_clauses: length(state.passive),
      total_steps: state.next_step_id - 1,
      arena_nodes: map_size(state.arena.nodes),
      unification_cutoffs: state.unification_cutoffs,
      step_counts: Enum.frequencies_by(Map.values(state.steps), &elem(&1, 0))
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
    best_passive = state.passive |> Enum.sort_by(& &1.score) |> Enum.take(passive_budget)
    Enum.uniq_by(state.units ++ state.active ++ best_passive, & &1.id)
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
