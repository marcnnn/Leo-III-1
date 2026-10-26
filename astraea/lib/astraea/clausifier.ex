defmodule Astraea.Clausifier do
  @moduledoc """
  Higher-Order THF0 Clausifier & Premise Selector.

  Transforms a lowered `Astraea.TptpLower` problem into Conjunctive Normal Form (CNF)
  clauses over the `Astraea.Arena` DAG:
  1. Extracts & inlines constant/combinator definitions (`role == "definition"` and closed
     higher-order constant equations), followed by multi-pass beta-eta normalization.
  2. Recognizes & rewrites Leibniz equality (`! [Q: ty > $o]: (Q @ u => Q @ v)` -> `u = v`)
     and unfolded bi-implications (`(~A | B) & (~B | A)` -> `A = B`).
  3. Applies SInE (Sumo Inference Engine) symbol-rarity premise selection when `length(axioms) > sine_limit`.
  4. Expands higher-order positive congruence, negative functional extensionality (`FuncExt`),
     and Boolean extensionality (`BoolExt`) with shared-conjunct factoring during NNF +
     content-addressed Skolemization.
  5. Distributes to CNF clauses with tautology elimination and per-clause variable standardization.
  """

  alias Astraea.{Arena, ProofChecker, TptpLower}

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_bvar 2
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @max_cnf_clauses_per_formula 64
  @max_bool_quant_splits 4
  @max_ext_depth 3

  @doc """
  Clausifies a `%Astraea.TptpLower{}` state into `{arena, clauses}`, where each
  clause is a `MapSet.t({:pos | :neg, term_id})`.
  """
  @spec clausify(TptpLower.t(), keyword()) :: {Arena.t(), [ProofChecker.clause()]}
  def clausify(%TptpLower{} = lowered, opts \\ []) do
    arena = lowered.arena
    sine_limit = Keyword.get(opts, :sine_limit, 55)
    inline_bridges = Keyword.get(opts, :inline_bridges, false)

    # 1. Extract constant definitions `c = rhs` and inline across axioms & conjectures
    {arena, def_map, defined_names} = extract_definitions(arena, lowered.axioms)

    raw_axioms =
      lowered.axioms
      |> Enum.reject(fn {name, role, _id} ->
        role == "definition" and MapSet.member?(defined_names, name)
      end)

    # 2. Apply SInE filter if large theory (> sine_limit axioms) and conjectures exist
    selected_axioms =
      if is_integer(sine_limit) and length(raw_axioms) > sine_limit and lowered.conjectures != [] do
        sine_filter(arena, raw_axioms, lowered.conjectures, sine_limit)
      else
        raw_axioms
      end

    # Identify bridge predicates: quantified arrow definitions that are directly referenced
    # inside `$o`-typed lemma definitions (e.g., `func` and `singleton` in `SEU673^2`).
    o_def_bodies =
      for {k, v} <- def_map, Arena.type_of(arena, k) == 0, do: v

    syms_in_o_defs =
      Enum.reduce(o_def_bodies, MapSet.new(), fn body_id, acc ->
        collect_consts(arena, body_id, acc)
      end)

    bridge_def_map =
      if not inline_bridges and o_def_bodies != [] do
        Map.reject(def_map, fn {k, v} ->
          {@tag_const, _, _, sym_id, _} = Arena.get_node(arena, k)

          Arena.type_of(arena, k) != 0 and
            contains_forall?(arena, v) and
            MapSet.member?(syms_in_o_defs, sym_id)
        end)
      else
        def_map
      end

    # 3. Preprocess (multi-pass inline definitions -> beta-eta norm -> rewrite Leibniz equality)
    {arena, prep_axioms} =
      Enum.reduce(selected_axioms, {arena, []}, fn {_name, role, term_id}, {ar, acc} ->
        {ar, norm_id} = preprocess_formula(ar, term_id, def_map)
        {ar, [{role, norm_id} | acc]}
      end)

    {arena, prep_conjs} =
      Enum.reduce(lowered.conjectures, {arena, []}, fn {_name, term_id}, {ar, acc} ->
        {ar, norm_id} = preprocess_formula(ar, term_id, bridge_def_map)
        {ar, [norm_id | acc]}
      end)

    # 4. Convert axioms (:pos) and conjectures (:neg) to NNF -> CNF clauses
    {arena, next_fvar, ax_clauses} =
      Enum.reduce(Enum.reverse(prep_axioms), {arena, 1, []}, fn {_role, term_id},
                                                                {ar, fvar, acc} ->
        {ar, fvar, cls} = formula_to_clauses(ar, term_id, :pos, fvar)
        {ar, fvar, acc ++ cls}
      end)

    {arena, _next_fvar, all_clauses} =
      Enum.reduce(Enum.reverse(prep_conjs), {arena, next_fvar, ax_clauses}, fn term_id,
                                                                               {ar, fvar, acc} ->
        {ar, fvar, cls} = formula_to_clauses(ar, term_id, :neg, fvar)
        {ar, fvar, acc ++ cls}
      end)

    {arena, Enum.uniq(all_clauses)}
  end

  defp preprocess_formula(%Arena{} = arena, term_id, def_map) do
    {arena, t1} =
      Enum.reduce(1..4, {arena, term_id}, fn _pass, {ar, cur} ->
        {ar, inlined} = inline_defs(ar, cur, def_map, 6)
        Arena.beta_eta_norm(ar, inlined)
      end)

    {arena, t2} = rewrite_leibniz(arena, t1)
    Arena.beta_eta_norm(arena, t2)
  end

  defp contains_forall?(%Arena{} = arena, term_id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_forall ->
        true

      @tag_not ->
        contains_forall?(arena, left)

      @tag_lam ->
        contains_forall?(arena, right)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        contains_forall?(arena, left) or contains_forall?(arena, right)

      _ ->
        false
    end
  end

  # ---------------------------------------------------------------------------
  # 1. Definition Extraction & Inlining
  # ---------------------------------------------------------------------------

  defp extract_definitions(%Arena{} = arena, axioms) do
    Enum.reduce(axioms, {arena, %{}, MapSet.new()}, fn {name, role, term_id},
                                                       {ar, def_map, names} ->
      if role in ["definition", "axiom"] do
        case match_definition(ar, term_id, role, []) do
          {:ok, ar2, const_id, rhs_id} ->
            if Map.has_key?(def_map, const_id) or const_occurs?(ar2, rhs_id, const_id) do
              {ar2, def_map, names}
            else
              {ar2, Map.put(def_map, const_id, rhs_id), MapSet.put(names, name)}
            end

          :error ->
            {ar, def_map, names}
        end
      else
        {ar, def_map, names}
      end
    end)
  end

  defp match_definition(%Arena{} = arena, term_id, role, binder_tys) do
    case Arena.get_node(arena, term_id) do
      {@tag_forall, _, _, var_ty, body_id} ->
        match_definition(arena, body_id, role, [var_ty | binder_tys])

      {@tag_eq, _, _, lhs, rhs} ->
        case match_def_spine(arena, lhs, 0, length(binder_tys)) do
          {:ok, const_id} ->
            {arena, lam_rhs} =
              Enum.reduce(binder_tys, {arena, rhs}, fn var_ty, {ar, body} ->
                Arena.mk_lam(ar, var_ty, body)
              end)

            {arena, leib_rhs} = rewrite_leibniz(arena, lam_rhs)
            {arena, norm_rhs} = Arena.beta_eta_norm(arena, leib_rhs)
            {_tag, flags, ty_id, _l, _r} = Arena.get_node(arena, norm_rhs)
            const_ty_id = Arena.type_of(arena, const_id)
            const_ty = Map.get(arena.type_table, ty_id)

            if ty_id == const_ty_id and
                 not Arena.has_loose_bvar?(arena, norm_rhs, 0) and
                 Bitwise.band(flags, 2) == 0 and
                 (role == "definition" or match?({:arrow, _, _}, const_ty)) do
              {:ok, arena, const_id, norm_rhs}
            else
              :error
            end

          :error ->
            :error
        end

      _ ->
        :error
    end
  end

  defp match_def_spine(%Arena{} = arena, term_id, expected_bvar, total_binders)
       when expected_bvar == total_binders do
    case Arena.get_node(arena, term_id) do
      {@tag_const, _, _, sym_id, _} ->
        sym_name = Map.get(arena.symbol_names, sym_id, "")
        if sym_name in ["$true", "$false"], do: :error, else: {:ok, term_id}

      _ ->
        :error
    end
  end

  defp match_def_spine(%Arena{} = arena, term_id, expected_bvar, total_binders)
       when expected_bvar < total_binders do
    case Arena.get_node(arena, term_id) do
      {@tag_app, _, _, fun_id, arg_id} ->
        case Arena.get_node(arena, arg_id) do
          {@tag_bvar, _, _, ^expected_bvar, _} ->
            match_def_spine(arena, fun_id, expected_bvar + 1, total_binders)

          _ ->
            :error
        end

      _ ->
        :error
    end
  end

  defp const_occurs?(%Arena{} = arena, term_id, target_const_id) do
    if term_id == target_const_id do
      true
    else
      {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

      case tag do
        @tag_not ->
          const_occurs?(arena, left, target_const_id)

        t when t in [@tag_lam, @tag_forall] ->
          const_occurs?(arena, right, target_const_id)

        t when t in [@tag_app, @tag_eq, @tag_or] ->
          const_occurs?(arena, left, target_const_id) or
            const_occurs?(arena, right, target_const_id)

        _ ->
          false
      end
    end
  end

  defp inline_defs(%Arena{} = arena, term_id, def_map, _depth) when map_size(def_map) == 0,
    do: {arena, term_id}

  defp inline_defs(%Arena{} = arena, term_id, _def_map, 0), do: {arena, term_id}

  defp inline_defs(%Arena{} = arena, term_id, def_map, depth) do
    case Map.fetch(def_map, term_id) do
      {:ok, rhs_id} ->
        inline_defs(arena, rhs_id, def_map, depth - 1)

      :error ->
        {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

        case tag do
          @tag_app ->
            {arena, l2} = inline_defs(arena, left, def_map, depth)
            {arena, r2} = inline_defs(arena, right, def_map, depth)
            Arena.mk_app(arena, l2, r2)

          @tag_lam ->
            {arena, b2} = inline_defs(arena, right, def_map, depth)
            Arena.mk_lam(arena, left, b2)

          @tag_forall ->
            {arena, b2} = inline_defs(arena, right, def_map, depth)
            Arena.mk_forall(arena, left, b2)

          @tag_eq ->
            {arena, l2} = inline_defs(arena, left, def_map, depth)
            {arena, r2} = inline_defs(arena, right, def_map, depth)
            Arena.mk_eq(arena, l2, r2)

          @tag_or ->
            {arena, l2} = inline_defs(arena, left, def_map, depth)
            {arena, r2} = inline_defs(arena, right, def_map, depth)
            Arena.mk_or(arena, l2, r2)

          @tag_not ->
            {arena, l2} = inline_defs(arena, left, def_map, depth)
            Arena.mk_not(arena, l2)

          _ ->
            {arena, term_id}
        end
    end
  end

  # ---------------------------------------------------------------------------
  # 2. Leibniz Equality & Bi-Implication Recognition
  # ---------------------------------------------------------------------------

  @spec rewrite_leibniz(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def rewrite_leibniz(%Arena{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_forall ->
        {arena, body_rewritten} = rewrite_leibniz(arena, right)

        case match_leibniz_body(arena, left, body_rewritten) do
          {:ok, arena, u_id, v_id} ->
            Arena.mk_eq(arena, u_id, v_id)

          :error ->
            Arena.mk_forall(arena, left, body_rewritten)
        end

      @tag_lam ->
        {arena, b2} = rewrite_leibniz(arena, right)
        Arena.mk_lam(arena, left, b2)

      @tag_app ->
        {arena, l2} = rewrite_leibniz(arena, left)
        {arena, r2} = rewrite_leibniz(arena, right)
        Arena.mk_app(arena, l2, r2)

      @tag_eq ->
        {arena, l2} = rewrite_leibniz(arena, left)
        {arena, r2} = rewrite_leibniz(arena, right)
        Arena.mk_eq(arena, l2, r2)

      @tag_or ->
        {arena, l2} = rewrite_leibniz(arena, left)
        {arena, r2} = rewrite_leibniz(arena, right)
        Arena.mk_or(arena, l2, r2)

      @tag_not ->
        {arena, l2} = rewrite_leibniz(arena, left)

        case match_unfolded_iff(arena, l2) do
          {:ok, a_id, b_id} ->
            Arena.mk_eq(arena, a_id, b_id)

          :error ->
            Arena.mk_not(arena, l2)
        end

      _ ->
        {arena, term_id}
    end
  end

  # Matches `~( ~(~A | B) | ~(~B | A) )` (unfolded `mequiv` / `miff`) -> `A = B`
  defp match_unfolded_iff(%Arena{} = arena, inner_or_id) do
    with {@tag_or, _, _, left_neg, right_neg} <- Arena.get_node(arena, inner_or_id),
         {@tag_not, _, _, imp1, _} <- Arena.get_node(arena, left_neg),
         {@tag_not, _, _, imp2, _} <- Arena.get_node(arena, right_neg),
         {:ok, a1, b1} <- match_imp_clauses(arena, imp1),
         {:ok, b2, a2} <- match_imp_clauses(arena, imp2),
         true <- a1 == a2 and b1 == b2 do
      {:ok, a1, b1}
    else
      _ -> :error
    end
  end

  defp match_imp_clauses(%Arena{} = arena, or_id) do
    case Arena.get_node(arena, or_id) do
      {@tag_or, _, _, l_id, r_id} ->
        case Arena.get_node(arena, l_id) do
          {@tag_not, _, _, a_id, _} -> {:ok, a_id, r_id}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  defp match_leibniz_body(%Arena{} = arena, q_ty_id, body_id) do
    case Map.get(arena.type_table, q_ty_id) do
      {:arrow, dom_ty, 0} ->
        case Arena.get_node(arena, body_id) do
          {@tag_or, _, _, l_or, r_or} ->
            case extract_leibniz_imp(arena, dom_ty, l_or, r_or) do
              {:ok, arena, u, v} -> {:ok, arena, u, v}
              :error -> extract_leibniz_imp(arena, dom_ty, r_or, l_or)
            end

          {@tag_eq, _, _, l_eq, r_eq} ->
            with {:ok, u_raw} <- match_bvar0_app(arena, l_eq),
                 {:ok, v_raw} <- match_bvar0_app(arena, r_eq),
                 true <- Arena.type_of(arena, u_raw) == dom_ty,
                 true <- Arena.type_of(arena, v_raw) == dom_ty,
                 false <- Arena.occurs_bvar?(arena, u_raw, 0),
                 false <- Arena.occurs_bvar?(arena, v_raw, 0) do
              {arena, u} = Arena.shift(arena, u_raw, -1, 1)
              {arena, v} = Arena.shift(arena, v_raw, -1, 1)
              {:ok, arena, u, v}
            else
              _ -> :error
            end

          _ ->
            :error
        end

      _ ->
        :error
    end
  end

  defp extract_leibniz_imp(%Arena{} = arena, dom_ty, neg_side, pos_side) do
    with {@tag_not, _, _, neg_inner, _} <- Arena.get_node(arena, neg_side),
         {:ok, u_raw} <- match_bvar0_app(arena, neg_inner),
         {:ok, v_raw} <- match_bvar0_app(arena, pos_side),
         true <- Arena.type_of(arena, u_raw) == dom_ty,
         true <- Arena.type_of(arena, v_raw) == dom_ty,
         false <- Arena.occurs_bvar?(arena, u_raw, 0),
         false <- Arena.occurs_bvar?(arena, v_raw, 0) do
      {arena, u} = Arena.shift(arena, u_raw, -1, 1)
      {arena, v} = Arena.shift(arena, v_raw, -1, 1)
      {:ok, arena, u, v}
    else
      _ -> :error
    end
  end

  defp match_bvar0_app(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_app, _, _, fun_id, arg_id} ->
        case Arena.get_node(arena, fun_id) do
          {@tag_bvar, _, _, 0, _} -> {:ok, arg_id}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  # ---------------------------------------------------------------------------
  # 3. SInE Premise Selection for Large Axiom Theories
  # ---------------------------------------------------------------------------

  defp sine_filter(%Arena{} = arena, axioms, conjectures, limit) do
    ax_with_syms =
      Enum.map(axioms, fn {_name, role, term_id} = ax ->
        syms = collect_consts(arena, term_id, MapSet.new())
        {ax, role, syms}
      end)

    df =
      Enum.reduce(ax_with_syms, %{}, fn {_ax, _role, syms}, acc ->
        Enum.reduce(syms, acc, fn s, m -> Map.update(m, s, 1, &(&1 + 1)) end)
      end)

    seed_syms =
      Enum.reduce(conjectures, MapSet.new(), fn {_n, id}, acc ->
        collect_consts(arena, id, acc)
      end)

    seed_syms =
      Enum.reduce(ax_with_syms, seed_syms, fn {_ax, role, syms}, acc ->
        if role in ["hypothesis", "assumption", "negated_conjecture"] do
          MapSet.union(acc, syms)
        else
          acc
        end
      end)

    {selected, _frontier} =
      Enum.reduce(1..3, {[], seed_syms}, fn _step, {sel_acc, frontier} ->
        newly_triggered =
          ax_with_syms
          |> Enum.filter(fn {_ax, role, syms} ->
            role in ["hypothesis", "assumption", "negated_conjecture"] or
              triggers_axiom?(syms, frontier, df)
          end)

        new_frontier =
          Enum.reduce(newly_triggered, frontier, fn {_ax, _r, syms}, acc ->
            MapSet.union(acc, syms)
          end)

        {Enum.uniq(sel_acc ++ Enum.map(newly_triggered, &elem(&1, 0))), new_frontier}
      end)

    if selected == [] do
      Enum.take(axioms, limit)
    else
      selected
      |> Enum.sort_by(fn {_name, role, term_id} ->
        role_prio = if role in ["hypothesis", "assumption", "negated_conjecture"], do: 0, else: 1
        {w, _v} = Arena.term_weight_and_vars(arena, term_id)
        {role_prio, w}
      end)
      |> Enum.take(limit)
    end
  end

  defp triggers_axiom?(syms, frontier, df) do
    if MapSet.size(syms) == 0 do
      false
    else
      min_freq =
        syms
        |> Enum.map(&Map.get(df, &1, 1))
        |> Enum.min()

      threshold = max(3, trunc(min_freq * 2.2))

      Enum.any?(syms, fn s ->
        MapSet.member?(frontier, s) and (MapSet.size(syms) <= 3 or Map.get(df, s, 1) <= threshold)
      end)
    end
  end

  defp collect_consts(%Arena{} = arena, term_id, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_const ->
        name = Map.get(arena.symbol_names, left, "")
        if name in ["$true", "$false"], do: acc, else: MapSet.put(acc, left)

      @tag_not ->
        collect_consts(arena, left, acc)

      t when t in [@tag_lam, @tag_forall] ->
        collect_consts(arena, right, acc)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        acc = collect_consts(arena, left, acc)
        collect_consts(arena, right, acc)

      _ ->
        acc
    end
  end

  # ---------------------------------------------------------------------------
  # 4. NNF + Skolemization + Extensionality + CNF
  # ---------------------------------------------------------------------------

  defp formula_to_clauses(%Arena{} = arena, term_id, polarity, next_fvar) do
    ctx = %{univ_vars: [], next_fvar: next_fvar, bool_splits: 0, ext_depth: 0}
    {arena, nnf_tree, ctx} = to_nnf(arena, term_id, polarity, ctx)
    raw_clauses = nnf_to_cnf(nnf_tree)

    {arena, final_fvar, clean_clauses} =
      Enum.reduce(raw_clauses, {arena, ctx.next_fvar, []}, fn lits, {ar, fvar, acc} ->
        case normalize_and_filter_clause(ar, lits, fvar) do
          {:tautology, ar2, fvar2} ->
            {ar2, fvar2, acc}

          {:ok, ar2, fvar2, clause} ->
            {ar2, fvar2, [clause | acc]}
        end
      end)

    {arena, final_fvar, Enum.reverse(clean_clauses)}
  end

  defp to_nnf(%Arena{} = arena, raw_term_id, polarity, ctx) do
    {arena, term_id} = Arena.beta_eta_norm(arena, raw_term_id)
    {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_const ->
        case Map.get(arena.symbol_names, left) do
          "$true" ->
            {arena, if(polarity == :pos, do: :top, else: :bot), ctx}

          "$false" ->
            {arena, if(polarity == :pos, do: :bot, else: :top), ctx}

          _ ->
            {arena, {:lit, polarity, term_id}, ctx}
        end

      @tag_not ->
        to_nnf(arena, left, flip_pol(polarity), ctx)

      @tag_or ->
        {arena, t_l, ctx} = to_nnf(arena, left, polarity, ctx)
        {arena, t_r, ctx} = to_nnf(arena, right, polarity, ctx)

        if polarity == :pos do
          {arena, mk_nnf_or(t_l, t_r), ctx}
        else
          {arena, mk_nnf_and(t_l, t_r), ctx}
        end

      @tag_forall ->
        var_ty = left
        body_id = right

        cond do
          var_ty == 0 and ctx.bool_splits < @max_bool_quant_splits ->
            {arena, true_id} = Arena.mk_const(arena, "$true", :o)
            {arena, false_id} = Arena.mk_const(arena, "$false", :o)
            {arena, body_t} = Arena.subst_bvar(arena, body_id, 0, true_id)
            {arena, body_f} = Arena.subst_bvar(arena, body_id, 0, false_id)
            ctx = %{ctx | bool_splits: ctx.bool_splits + 1}
            {arena, tree_t, ctx} = to_nnf(arena, body_t, polarity, ctx)
            {arena, tree_f, ctx} = to_nnf(arena, body_f, polarity, ctx)

            if polarity == :pos do
              {arena, mk_nnf_and(tree_t, tree_f), ctx}
            else
              {arena, mk_nnf_or(tree_t, tree_f), ctx}
            end

          polarity == :pos ->
            fvar_id = ctx.next_fvar
            {arena, fv_node} = Arena.mk_fvar(arena, fvar_id, var_ty)
            {arena, body_inst} = Arena.subst_bvar(arena, body_id, 0, fv_node)

            ctx2 = %{
              ctx
              | next_fvar: fvar_id + 1,
                univ_vars: ctx.univ_vars ++ [{fvar_id, var_ty, fv_node}]
            }

            {arena, tree_fv, ctx3} = to_nnf(arena, body_inst, :pos, ctx2)
            ctx_restored = %{ctx3 | univ_vars: ctx.univ_vars}

            # If quantifying positively over a unary predicate `P : dom_ty -> $o`,
            # also instantiate with `^ [Z: dom_ty]: $false` (e.g., `vacuousDall` in `SEU820^2`).
            case Map.get(arena.type_table, var_ty) do
              {:arrow, dom_ty, 0} when ctx_restored.bool_splits < 2 ->
                {arena, false_id} = Arena.mk_const(arena, "$false", :o)
                {arena, lam_false} = Arena.mk_lam(arena, dom_ty, false_id)
                {arena, body_false} = Arena.subst_bvar(arena, body_id, 0, lam_false)
                ctx_b = %{ctx_restored | bool_splits: ctx_restored.bool_splits + 1}
                {arena, tree_false, ctx_after} = to_nnf(arena, body_false, :pos, ctx_b)
                {arena, mk_nnf_and(tree_fv, tree_false), ctx_after}

              _ ->
                {arena, tree_fv, ctx_restored}
            end

          polarity == :neg ->
            body_fvars = Arena.free_vars(arena, body_id)

            active_univ =
              Enum.filter(ctx.univ_vars, fn {fv_id, fv_ty, _node} ->
                MapSet.member?(body_fvars, {fv_id, fv_ty})
              end)

            {arena, sk_ty} =
              Enum.reduce(Enum.reverse(active_univ), {arena, var_ty}, fn {_id, u_ty, _n},
                                                                         {ar, acc_ty} ->
                Arena.intern_type(ar, {:arrow, u_ty, acc_ty})
              end)

            {arena, sk_sym} = Arena.mk_skolem(arena, term_id, sk_ty)

            {arena, sk_term} =
              Enum.reduce(active_univ, {arena, sk_sym}, fn {_id, _u_ty, fv_node}, {ar, acc} ->
                Arena.mk_app(ar, acc, fv_node)
              end)

            {arena, body_inst} = Arena.subst_bvar(arena, body_id, 0, sk_term)
            to_nnf(arena, body_inst, :neg, ctx)
        end

      @tag_eq ->
        lhs_ty_id = Arena.type_of(arena, left)
        lhs_ty = Map.get(arena.type_table, lhs_ty_id)

        cond do
          lhs_ty == :o ->
            to_nnf_bool_eq(arena, left, right, polarity, ctx)

          match?({:arrow, _, _}, lhs_ty) and ctx.ext_depth < @max_ext_depth ->
            {:arrow, dom_ty, _cod_ty} = lhs_ty
            {arena, eq_id} = canonical_eq(arena, left, right)

            if left == right do
              if polarity == :pos do
                {arena, :top, ctx}
              else
                {arena, {:lit, :neg, eq_id}, ctx}
              end
            else
              {arena, f_s} = Arena.shift(arena, left, 1, 0)
              {arena, g_s} = Arena.shift(arena, right, 1, 0)
              {arena, x0} = Arena.mk_bvar(arena, 0, dom_ty)
              {arena, fx} = Arena.mk_app(arena, f_s, x0)
              {arena, gx} = Arena.mk_app(arena, g_s, x0)
              {arena, eq_fx_gx} = Arena.mk_eq(arena, fx, gx)
              {arena, forall_ext} = Arena.mk_forall(arena, dom_ty, eq_fx_gx)

              ctx_ext = %{ctx | ext_depth: ctx.ext_depth + 1}
              {arena, ext_tree, ctx_after} = to_nnf(arena, forall_ext, polarity, ctx_ext)
              ctx_final = %{ctx_after | ext_depth: ctx.ext_depth}

              {arena, mk_nnf_and({:lit, polarity, eq_id}, ext_tree), ctx_final}
            end

          true ->
            {arena, eq_id} = canonical_eq(arena, left, right)

            if left == right and polarity == :pos do
              {arena, :top, ctx}
            else
              {arena, {:lit, polarity, eq_id}, ctx}
            end
        end

      _ ->
        {arena, {:lit, polarity, term_id}, ctx}
    end
  end

  # Factors out shared conjuncts or disjuncts before expanding `A <=> B` (`(A & S) <=> (B & S)`)
  defp to_nnf_bool_eq(%Arena{} = arena, left, right, polarity, ctx) do
    {arena, l_conjs} = collect_conjuncts(arena, left)
    {arena, r_conjs} = collect_conjuncts(arena, right)
    shared_conjs = MapSet.intersection(MapSet.new(l_conjs), MapSet.new(r_conjs))

    if MapSet.size(shared_conjs) > 0 do
      rem_l = Enum.reject(l_conjs, &MapSet.member?(shared_conjs, &1))
      rem_r = Enum.reject(r_conjs, &MapSet.member?(shared_conjs, &1))
      {arena, shared_term} = build_conjunction(arena, MapSet.to_list(shared_conjs))
      {arena, rem_l_term} = build_conjunction(arena, rem_l)
      {arena, rem_r_term} = build_conjunction(arena, rem_r)
      {arena, rem_eq} = Arena.mk_eq(arena, rem_l_term, rem_r_term)
      {arena, imp_term} = Arena.mk_imp(arena, shared_term, rem_eq)
      to_nnf(arena, imp_term, polarity, ctx)
    else
      l_disjs = collect_disjuncts(arena, left)
      r_disjs = collect_disjuncts(arena, right)
      shared_disjs = MapSet.intersection(MapSet.new(l_disjs), MapSet.new(r_disjs))

      if MapSet.size(shared_disjs) > 0 do
        rem_l = Enum.reject(l_disjs, &MapSet.member?(shared_disjs, &1))
        rem_r = Enum.reject(r_disjs, &MapSet.member?(shared_disjs, &1))
        {arena, shared_term} = build_disjunction(arena, MapSet.to_list(shared_disjs))
        {arena, neg_shared} = Arena.mk_not(arena, shared_term)
        {arena, rem_l_term} = build_disjunction(arena, rem_l)
        {arena, rem_r_term} = build_disjunction(arena, rem_r)
        {arena, rem_eq} = Arena.mk_eq(arena, rem_l_term, rem_r_term)
        {arena, imp_term} = Arena.mk_imp(arena, neg_shared, rem_eq)
        to_nnf(arena, imp_term, polarity, ctx)
      else
        if polarity == :pos do
          {arena, neg_a1, ctx} = to_nnf(arena, left, :neg, ctx)
          {arena, pos_b1, ctx} = to_nnf(arena, right, :pos, ctx)
          {arena, neg_b2, ctx} = to_nnf(arena, right, :neg, ctx)
          {arena, pos_a2, ctx} = to_nnf(arena, left, :pos, ctx)
          {arena, mk_nnf_and(mk_nnf_or(neg_a1, pos_b1), mk_nnf_or(neg_b2, pos_a2)), ctx}
        else
          {arena, pos_a1, ctx} = to_nnf(arena, left, :pos, ctx)
          {arena, pos_b1, ctx} = to_nnf(arena, right, :pos, ctx)
          {arena, neg_a2, ctx} = to_nnf(arena, left, :neg, ctx)
          {arena, neg_b2, ctx} = to_nnf(arena, right, :neg, ctx)
          {arena, mk_nnf_and(mk_nnf_or(pos_a1, pos_b1), mk_nnf_or(neg_a2, neg_b2)), ctx}
        end
      end
    end
  end

  defp collect_conjuncts(%Arena{} = arena, term_id) do
    # In Arena, n-ary `C1 & C2 & ... & Cn` after double-negation elimination is `~(D1 | D2 | ... | Dn)`
    # where each `Di` is `~Ci` (or `Ci` was a negation `~X` so `Di` is `X`).
    with {@tag_not, _, _, or_id, _} <- Arena.get_node(arena, term_id),
         {@tag_or, _, _, _, _} <- Arena.get_node(arena, or_id) do
      disjs = collect_disjuncts(arena, or_id)

      Enum.reduce(disjs, {arena, []}, fn d_id, {ar, acc} ->
        case Arena.get_node(ar, d_id) do
          {@tag_not, _, _, c_id, _} ->
            {ar2, sub_conjs} = collect_conjuncts(ar, c_id)
            {ar2, acc ++ sub_conjs}

          _ ->
            {ar2, neg_d} = Arena.mk_not(ar, d_id)
            {ar3, norm_d} = Arena.beta_eta_norm(ar2, neg_d)
            {ar3, acc ++ [norm_d]}
        end
      end)
    else
      _ -> {arena, [term_id]}
    end
  end

  defp collect_disjuncts(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_or, _, _, l_id, r_id} ->
        collect_disjuncts(arena, l_id) ++ collect_disjuncts(arena, r_id)

      _ ->
        [term_id]
    end
  end

  defp build_conjunction(%Arena{} = arena, []), do: Arena.mk_const(arena, "$true", :o)
  defp build_conjunction(%Arena{} = arena, [single]), do: {arena, single}

  defp build_conjunction(%Arena{} = arena, [first | rest]) do
    Enum.reduce(rest, {arena, first}, fn item, {ar, acc} ->
      Arena.mk_and(ar, acc, item)
    end)
  end

  defp build_disjunction(%Arena{} = arena, []), do: Arena.mk_const(arena, "$false", :o)
  defp build_disjunction(%Arena{} = arena, [single]), do: {arena, single}

  defp build_disjunction(%Arena{} = arena, [first | rest]) do
    Enum.reduce(rest, {arena, first}, fn item, {ar, acc} ->
      Arena.mk_or(ar, acc, item)
    end)
  end

  defp canonical_eq(%Arena{} = arena, lhs, rhs) do
    case Arena.kbo_compare(arena, lhs, rhs) do
      :lt -> Arena.mk_eq(arena, rhs, lhs)
      _ -> Arena.mk_eq(arena, lhs, rhs)
    end
  end

  defp flip_pol(:pos), do: :neg
  defp flip_pol(:neg), do: :pos

  defp mk_nnf_and(:top, r), do: r
  defp mk_nnf_and(l, :top), do: l
  defp mk_nnf_and(:bot, _r), do: :bot
  defp mk_nnf_and(_l, :bot), do: :bot
  defp mk_nnf_and(l, r), do: {:and, l, r}

  defp mk_nnf_or(:top, _r), do: :top
  defp mk_nnf_or(_l, :top), do: :top
  defp mk_nnf_or(:bot, r), do: r
  defp mk_nnf_or(l, :bot), do: l
  defp mk_nnf_or(l, r), do: {:or, l, r}

  defp nnf_to_cnf(:top), do: []
  defp nnf_to_cnf(:bot), do: [[]]
  defp nnf_to_cnf({:lit, pol, id}), do: [[{pol, id}]]

  defp nnf_to_cnf({:and, l, r}) do
    (nnf_to_cnf(l) ++ nnf_to_cnf(r))
    |> Enum.take(@max_cnf_clauses_per_formula)
  end

  defp nnf_to_cnf({:or, l, r}) do
    cls_l = nnf_to_cnf(l)
    cls_r = nnf_to_cnf(r)

    cond do
      cls_l == [] or cls_r == [] ->
        []

      length(cls_l) * length(cls_r) <= @max_cnf_clauses_per_formula ->
        for c1 <- cls_l, c2 <- cls_r, do: c1 ++ c2

      true ->
        for(c1 <- Enum.take(cls_l, 8), c2 <- Enum.take(cls_r, 8), do: c1 ++ c2)
    end
  end

  defp normalize_and_filter_clause(%Arena{} = arena, [], next_fvar) do
    {arena, true_id} = Arena.mk_const(arena, "$true", :o)
    {arena, eq_tt} = Arena.mk_eq(arena, true_id, true_id)
    {:ok, arena, next_fvar, MapSet.new([{:neg, eq_tt}])}
  end

  defp normalize_and_filter_clause(%Arena{} = arena, lits, next_fvar) do
    clause_set = MapSet.new(lits)

    is_taut =
      Enum.any?(clause_set, fn
        {:pos, id} ->
          MapSet.member?(clause_set, {:neg, id}) or
            match?({@tag_eq, _, _, s, s}, Arena.get_node(arena, id))

        _ ->
          false
      end)

    if is_taut do
      {:tautology, arena, next_fvar}
    else
      fvars =
        Enum.reduce(clause_set, MapSet.new(), fn {_pol, id}, acc ->
          MapSet.union(acc, Arena.free_vars(arena, id))
        end)

      if MapSet.size(fvars) == 0 do
        {:ok, arena, next_fvar, clause_set}
      else
        {arena, fvar_after, subst} =
          Enum.reduce(fvars, {arena, next_fvar, %{}}, fn {old_id, ty_id}, {ar, nf, sub} ->
            {ar, new_fv} = Arena.mk_fvar(ar, nf, ty_id)
            {ar, nf + 1, Map.put(sub, old_id, new_fv)}
          end)

        {arena, renamed_clause} =
          Enum.reduce(clause_set, {arena, MapSet.new()}, fn {pol, id}, {ar, acc} ->
            {ar, id2} = Arena.subst_fvar(ar, id, subst)
            {ar, MapSet.put(acc, {pol, id2})}
          end)

        {:ok, arena, fvar_after, renamed_clause}
      end
    end
  end
end
