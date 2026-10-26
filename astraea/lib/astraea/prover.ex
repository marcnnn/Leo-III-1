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
  """

  alias Astraea.{Arena, Clausifier, ProofChecker, TptpCorpus, TptpLower}

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
            deadline_ms: nil

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

  @spec prove_clauses(Arena.t(), [ProofChecker.clause()], keyword()) :: result()
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
      deadline_ms: deadline
    }

    case init_clauses(state, input_clauses) do
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
      for {entry, {:proved, steps, st}, ms} <- results, is_map(entry) and entry.status == "Theorem" do
        {entry.problem, entry.domain, length(steps), st.iterations, ms}
      end

    csa_false_proofs =
      for {entry, {:proved, _steps, _st}, _ms} <- results,
          is_map(entry) and entry.status in ["CounterSatisfiable", "Satisfiable"] do
        entry.problem
      end

    lcf_failures =
      for {entry, {:error, {:lcf_verification_failed, reason, _}}, _ms} <- results, is_map(entry) do
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

  defp init_clauses(%__MODULE__{} = state, clauses) do
    # Pass 1: Register all initial clauses as `:axiom` steps in their original order
    {state, axiom_items} =
      Enum.reduce(clauses, {state, []}, fn clause, {st, acc} ->
        {st, c_item} = add_step(st, {:axiom, st.next_step_id, clause}, clause, 0)

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
    {:saturated, stats(state)}
  end

  defp saturation_loop(%__MODULE__{iterations: iters, max_iterations: max_iters} = state)
       when iters >= max_iters do
    {:resource_out, stats(state)}
  end

  defp saturation_loop(%__MODULE__{} = state) do
    if System.monotonic_time(:millisecond) >= state.deadline_ms do
      {:resource_out, stats(state)}
    else
      {given, rest_passive} = pop_best_passive(state.passive, state.iterations)
      state = %{state | passive: rest_passive, iterations: state.iterations + 1}
      {state, given} = condense_clause(state, given)

      case unit_simplify(state, given) do
        {:proved, state, empty_id} ->
          finalize_proof(state, empty_id)

        {:ok, state, given} ->
          if forward_subsumed?(state.arena, state.active, given) do
            saturation_loop(state)
          else
            case generate_inferences(state, given) do
              {:proved, state, empty_id} ->
                finalize_proof(state, empty_id)

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

    item = %{
      id: id,
      lits: lits,
      fvars: fvars,
      fvar_ids: fvar_ids,
      weight: weight,
      depth: depth,
      fv: fv,
      score: score
    }

    state = %{
      state
      | steps: Map.put(state.steps, id, step),
        next_step_id: id + 1
    }

    {state, item}
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

  defp stats(%__MODULE__{} = state) do
    %{
      iterations: state.iterations,
      active_clauses: length(state.active),
      passive_clauses: length(state.passive),
      total_steps: state.next_step_id - 1,
      arena_nodes: map_size(state.arena.nodes)
    }
  end
end
