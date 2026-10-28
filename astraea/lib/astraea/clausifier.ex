defmodule Astraea.Clausifier do
  @moduledoc """
  Higher-Order THF0 Clausifier & Premise Selector.

  Transforms a lowered `Astraea.TptpLower` problem into Conjunctive Normal Form (CNF)
  clauses over the `Astraea.Arena` DAG:
  1. Extracts & inlines constant/combinator definitions (`role == "definition"` and closed
     higher-order constant equations), followed by multi-pass beta-eta normalization.
  2. Recognizes & rewrites Leibniz equality (`! [Q: ty > $o]: (Q @ u => Q @ v)` -> `u = v`),
     Andrews equality (`! [Q: ty > ty > $o]: ((! [X]: Q @ X @ X) => Q @ u @ v)` -> `u = v`,
     option `:andrews_eq`) and unfolded bi-implications (`(~A | B) & (~B | A)` -> `A = B`).
  3. Applies SInE (Sumo Inference Engine) symbol-rarity premise selection when
     `length(axioms) > sine_limit`, or Leo-III's relevance filter
     (`Astraea.RelevanceFilter`, option `:relevance_filter`) or Leo-III's SInE
     (`Astraea.Sine`, option `:sine`) instead.
  4. Expands higher-order positive congruence, negative functional extensionality (`FuncExt`),
     and Boolean extensionality (`BoolExt`) with shared-conjunct factoring during NNF +
     content-addressed Skolemization.
  5. Optionally renames subformulas whose distribution would blow up (definitional CNF,
     Leo-III `RenameCNF`, option `:renaming`), then distributes to CNF clauses with
     tautology elimination and per-clause variable standardization.
  6. Adds clause-level Andrews instances (Leo-III `ReplaceAndrewsEq`).

  The clauses enter `Astraea.ProofChecker` as trusted `{:axiom, ...}` steps, and model
  answers are read off saturated clause sets, so each step below must preserve
  satisfiability in both directions (Henkin semantics with primitive equality):
  - Andrews rewrite: `! [Q]: ((! [X]: Q @ X @ X) => Q @ u @ v)` is equivalent to `u = v`.
    From left to right instantiate `Q := ^ [Y, Z]: Y = Z`, a closed term that denotes in
    every Henkin model; from right to left `Q @ u @ v` is `Q @ u @ u`. Equivalent
    subformulas are replaced in any context.
  - Clause-level Andrews: for a clause `C` with a literal `~(X @ t @ t)` the instance
    `C[X := ^ [Y, Z]: Y = Z]` (minus the false literals `~(t = t)`) is a consequence of
    `C` and is added next to it, so the clause set is equivalent to the old one.
    Leo-III replaces `C`, which is only satisfiability-preserving one way.
  - Renaming: a subformula `S` with free variables `X1, ..., Xn` at a positive position
    of an NNF tree `T[S]` (every position of an NNF tree is positive) is replaced by
    `d @ X1 @ ... @ Xn` and the definition `! [X1, ..., Xn]: (~d @ X1 @ ... @ Xn | S)`
    is added (Leo-III's polarity-aware one-directional definition). A model of `T[S]`
    extends to the new symbol by `d := ^ [X1, ..., Xn]: S`, which satisfies both
    formulas. Conversely, in a model of `T[d @ X1 @ ... @ Xn]` and the definition,
    `d @ X1 @ ... @ Xn` implies `S`, so `T[S]` holds by monotonicity of positive
    positions; that direction keeps model answers valid. The name of `d` is a hash of
    `^ [X1, ..., Xn]: S` (variables in order of first occurrence), so equal
    subformulas share one symbol, all definitions of `d` agree with the single
    interpretation `^ [X1, ..., Xn]: S`, and lemmas exchanged between portfolio
    workers mean the same in every worker (a counter would not; see Entry 001 of
    `Notes/thesis_work_log.md`). The definition is emitted once per symbol.
    A 64-bit hash collision, or a user symbol named `def_<16 hex digits>`, would break
    freshness; both are treated as impossible, as for `Arena.mk_skolem/3`.
  - Set instantiation (`:instantiate_sets`) adds instances `P[X := c]` of axioms
    `! [X]: P`, which are consequences of the kept axiom.
  - Premise selection drops axioms and `@max_cnf_clauses_per_formula` drops clauses:
    both keep refutations sound but lose models, so `clausify_with_info/2` reports them
    (`:axioms_dropped`, `:cnf_truncated`) for the caller to mark the run incomplete.
    Renaming keeps CNFs small and so mostly avoids the truncation.

  Leo-III's `PolaritySwitch` (`[~s]^p -> [s]^~p`, `[~s = ~t]^p -> [s = t]^p`) and
  `LiftEq` (a predicate literal `[s = t]^p` becomes an equational literal) have no
  counterpart here: NNF already moves every negation into the literal polarity and
  expands Boolean equations, and an equation atom `Arena.mk_eq/3` under a polarity
  already is an equational literal.
  """

  alias Astraea.{Arena, ProblemStatistics, ProofChecker, RelevanceFilter, Sine, TptpLower}

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

  @max_cnf_clauses_per_formula 64
  @max_bool_quant_splits 4
  @max_ext_depth 3

  # Leo-III `Configuration.RENAMING_THRESHHOLD` default (`CNFControl.cnf2` passes 0)
  @default_renaming_threshold 0

  @typedoc """
  What `clausify_with_info/2` did besides the plain translation:
    * `:axioms_dropped` - axioms removed by SInE (either variant) or the relevance
      filter
    * `:cnf_truncated` - formulas whose CNF exceeded `@max_cnf_clauses_per_formula`
      and lost clauses
    * `:definitions` - renaming definitions introduced
    * `:andrews_instances` - clauses added by the clause-level Andrews rewrite
  `:axioms_dropped > 0` or `:cnf_truncated > 0` means that a model of the clauses
  need not be a model of the problem.
  """
  @type info :: %{
          axioms_dropped: non_neg_integer(),
          cnf_truncated: non_neg_integer(),
          definitions: non_neg_integer(),
          andrews_instances: non_neg_integer()
        }

  @doc """
  Clausifies a `%Astraea.TptpLower{}` state into `{arena, clauses}`, where each
  clause is a `MapSet.t({:pos | :neg, term_id})`. Options:
    * `:sine_limit` - SInE premise selection above this many axioms (default 55,
      `nil` disables it)
    * `:inline_bridges` - also inline bridge definitions into conjectures (default `false`)
    * `:renaming` - definitional CNF (Leo-III `--renaming`, `RunStrategy.renaming`;
      default `false`)
    * `:renaming_threshold` - rename a disjunct only if the CNF shrinks by more than
      this many clauses (Leo-III `RenameCNF` `THRESHHOLD`, default 0)
    * `:leibniz_eq` - rewrite Leibniz equality (Leo-III default; `--nleq` disables
      it, default `true`)
    * `:andrews_eq` - rewrite Andrews equality (Leo-III default; `--naeq` disables
      it, default `true`)
    * `:instantiate_sets` - add instances of axioms quantifying over sets of functions
      or properties (Leo-III `--instantiate-sets`, default `false`)
    * `:relevance_filter` - `nil` (default), `:auto` or `%{passmark: p, aging: a}`:
      Leo-III's relevance filter (`--relevance-passmark`, `--relevance-aging`, see
      `Astraea.RelevanceFilter`) instead of SInE
    * `:sine` - `nil` (default), `:auto`, `%{threshold: t, max_size: n, max_depth: d}`
      or a `"t;n;d"` string: Leo-III's SInE (`--sine`, see `Astraea.Sine`) instead
      of Astraea's SInE and the relevance filter. `:auto`, and a string Leo-III
      cannot parse, guess the configuration from the axiom counts
    * `:standard_sine` - guess Leo-III's `defaultConfig` instead of a table entry
      (Leo-III `--standard-sine`, default `false`)
    * `:axiom_counts` - `{internal, external}` or an `Astraea.ProblemStatistics`:
      `axiom`/`hypothesis` formulas of the problem file and of its includes, for
      the guess (default: every such formula counts as internal)
  """
  @spec clausify(TptpLower.t(), keyword()) :: {Arena.t(), [ProofChecker.clause()]}
  def clausify(%TptpLower{} = lowered, opts \\ []) do
    {arena, clauses, _info} = clausify_with_info(lowered, opts)
    {arena, clauses}
  end

  @doc "`clausify/2` that also returns an `t:info/0` map."
  @spec clausify_with_info(TptpLower.t(), keyword()) ::
          {Arena.t(), [ProofChecker.clause()], info()}
  def clausify_with_info(%TptpLower{} = lowered, opts \\ []) do
    arena = lowered.arena
    sine_limit = Keyword.get(opts, :sine_limit, 55)
    inline_bridges = Keyword.get(opts, :inline_bridges, false)
    andrews_eq = Keyword.get(opts, :andrews_eq, true)
    relevance_filter = Keyword.get(opts, :relevance_filter)
    sine = Keyword.get(opts, :sine)

    # 1. Extract constant definitions `c = rhs` and inline across axioms & conjectures
    {arena, def_map, defined_names} = extract_definitions(arena, lowered.axioms)

    raw_axioms =
      lowered.axioms
      |> Enum.reject(fn {name, role, _id} ->
        role == "definition" and MapSet.member?(defined_names, name)
      end)

    # 2. Apply Leo-III's SInE or the relevance filter if requested (in that order,
    #    as Leo-III's `--sine` wins), else SInE if large theory (> sine_limit
    #    axioms) and conjectures exist
    selected_axioms =
      cond do
        sine != nil ->
          Sine.select(
            arena,
            raw_axioms,
            lowered.conjectures,
            def_map,
            sine_config(sine, lowered, opts)
          )

        relevance_filter != nil ->
          RelevanceFilter.select(
            arena,
            raw_axioms,
            lowered.conjectures,
            def_map,
            relevance_filter
          )

        is_integer(sine_limit) and length(raw_axioms) > sine_limit and lowered.conjectures != [] ->
          sine_filter(arena, raw_axioms, lowered.conjectures, sine_limit)

        true ->
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
    eqs = {Keyword.get(opts, :leibniz_eq, true), andrews_eq}

    {arena, prep_axioms} =
      Enum.reduce(selected_axioms, {arena, []}, fn {_name, role, term_id}, {ar, acc} ->
        {ar, norm_id} = preprocess_formula(ar, term_id, def_map, eqs)
        {ar, [{role, norm_id} | acc]}
      end)

    {arena, prep_conjs} =
      Enum.reduce(lowered.conjectures, {arena, []}, fn {_name, term_id}, {ar, acc} ->
        {ar, norm_id} = preprocess_formula(ar, term_id, bridge_def_map, eqs)
        {ar, [norm_id | acc]}
      end)

    {arena, prep_axioms} =
      if Keyword.get(opts, :instantiate_sets, false),
        do: instantiate_sets(arena, prep_axioms, prep_conjs),
        else: {arena, prep_axioms}

    # 4. Convert axioms (:pos) and conjectures (:neg) to NNF -> CNF clauses
    st = %{
      renaming: Keyword.get(opts, :renaming, false),
      threshold: Keyword.get(opts, :renaming_threshold, @default_renaming_threshold),
      defined: MapSet.new(),
      definitions: 0,
      cnf_truncated: 0
    }

    {arena, next_fvar, ax_clauses, st} =
      Enum.reduce(Enum.reverse(prep_axioms), {arena, 1, [], st}, fn {_role, term_id},
                                                                    {ar, fvar, acc, st} ->
        {ar, fvar, cls, st} = formula_to_clauses(ar, term_id, :pos, fvar, st)
        {ar, fvar, acc ++ cls, st}
      end)

    {arena, next_fvar, all_clauses, st} =
      Enum.reduce(Enum.reverse(prep_conjs), {arena, next_fvar, ax_clauses, st}, fn term_id,
                                                                                   {ar, fvar, acc,
                                                                                    st} ->
        {ar, fvar, cls, st} = formula_to_clauses(ar, term_id, :neg, fvar, st)
        {ar, fvar, acc ++ cls, st}
      end)

    # 5. Clause-level Andrews equality (`ReplaceAndrewsEq`), as extra instances
    {arena, extra, st} =
      if andrews_eq,
        do: andrews_instances(arena, all_clauses, next_fvar, st),
        else: {arena, [], st}

    info = %{
      axioms_dropped: length(raw_axioms) - length(selected_axioms),
      cnf_truncated: st.cnf_truncated,
      definitions: st.definitions,
      andrews_instances: length(extra)
    }

    {arena, Enum.uniq(all_clauses ++ extra), info}
  end

  # Leo-III `getBestFilterConfig` with the problem's axiom counts. Leo-III counts
  # the `axiom` and `hypothesis` formulas, before and after the included ones.
  defp sine_config(sine, %TptpLower{} = lowered, opts) do
    {internal, external} =
      case Keyword.get(opts, :axiom_counts) do
        %ProblemStatistics{} = stats ->
          {stats.local_axioms, stats.included_axioms}

        {internal, external} ->
          {internal, external}

        nil ->
          {Enum.count(lowered.axioms, fn {_n, role, _id} ->
             Astraea.Input.Elaborator.base_role(role) in ["axiom", "hypothesis"]
           end), 0}
      end

    Sine.config(sine,
      internal: internal,
      external: external,
      standard: Keyword.get(opts, :standard_sine, false)
    )
  end

  defp preprocess_formula(%Arena{} = arena, term_id, def_map, {leibniz_eq, andrews_eq}) do
    {arena, t1} =
      Enum.reduce(1..4, {arena, term_id}, fn _pass, {ar, cur} ->
        {ar, inlined} = inline_defs(ar, cur, def_map, 6)
        Arena.beta_eta_norm(ar, inlined)
      end)

    {arena, t2} = if leibniz_eq, do: rewrite_leibniz(arena, t1), else: {arena, t1}
    {arena, t2} = if andrews_eq, do: rewrite_andrews(arena, t2), else: {arena, t2}
    Arena.beta_eta_norm(arena, t2)
  end

  # Leo-III `instantiateSetAxioms` (`--instantiate-sets`): an axiom
  # `! [X: (A > B) > ... > C]: P` over sets of functions or properties gets the
  # instances `P[X := c]` for every symbol `c` of that type occurring in the problem,
  # plus the empty set `^ [...]: $false` when `C` is `$o`, recursively for nested
  # quantifiers. Leo-III replaces the axiom by its instances; here they are added next
  # to it, so the clause set stays equivalent and model answers remain valid.
  defp instantiate_sets(%Arena{} = arena, prep_axioms, prep_conjs) do
    terms = Enum.map(prep_axioms, &elem(&1, 1)) ++ prep_conjs
    consts = Enum.reduce(terms, MapSet.new(), &collect_const_nodes(arena, &1, &2))

    Enum.reduce(prep_axioms, {arena, prep_axioms}, fn
      {"axiom", term_id}, {ar, acc} ->
        {ar, insts} = set_instances(ar, term_id, consts)

        Enum.reduce(insts, {ar, acc}, fn inst, {ar, acc} ->
          {ar, inst} = Arena.beta_eta_norm(ar, inst)
          {ar, [{"plain", inst} | acc]}
        end)

      _, st ->
        st
    end)
  end

  defp set_instances(%Arena{} = arena, term_id, consts) do
    case Arena.get_node(arena, term_id) do
      {@tag_forall, _, _, var_ty, body} ->
        {arena, kept} = set_instances(arena, body, consts)

        {arena, kept} =
          Enum.reduce(kept, {arena, []}, fn b, {ar, acc} ->
            {ar, f} = Arena.mk_forall(ar, var_ty, b)
            {ar, [f | acc]}
          end)

        {arena, cands} = set_candidates(arena, var_ty, consts)

        Enum.reduce(cands, {arena, Enum.reverse(kept)}, fn c, {ar, acc} ->
          {ar, here} = Arena.subst_bvar(ar, body, 0, c)
          {ar, here} = Arena.beta_eta_norm(ar, here)
          {ar, deeper} = set_instances(ar, here, consts)
          {ar, acc ++ [here | deeper]}
        end)

      _ ->
        {arena, []}
    end
  end

  defp set_candidates(%Arena{} = arena, ty, consts) do
    with {:arrow, dom, _cod} <- Map.get(arena.type_table, ty),
         {:arrow, _, _} <- Map.get(arena.type_table, dom),
         [_ | _] = cs <- consts |> Enum.filter(&(Arena.type_of(arena, &1) == ty)) |> Enum.sort() do
      {arena, empty} = empty_set(arena, ty)
      {arena, if(empty, do: cs ++ [empty], else: cs)}
    else
      _ -> {arena, []}
    end
  end

  # `^ [X1, ..., Xn]: $false` for a type `T1 > ... > Tn > $o`, `nil` for other types.
  defp empty_set(%Arena{} = arena, ty) do
    case Map.get(arena.type_table, ty) do
      {:arrow, dom, cod} ->
        case empty_set(arena, cod) do
          {arena, nil} -> {arena, nil}
          {arena, body} -> Arena.mk_lam(arena, dom, body)
        end

      _ ->
        if ty == Arena.ty_o(), do: Arena.mk_const(arena, "$false", :o), else: {arena, nil}
    end
  end

  defp collect_const_nodes(%Arena{} = arena, term_id, acc) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_const ->
        if String.starts_with?(Map.get(arena.symbol_names, left, "$"), "$"),
          do: acc,
          else: MapSet.put(acc, term_id)

      @tag_not ->
        collect_const_nodes(arena, left, acc)

      t when t in [@tag_lam, @tag_forall] ->
        collect_const_nodes(arena, right, acc)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        collect_const_nodes(arena, right, collect_const_nodes(arena, left, acc))

      _ ->
        acc
    end
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
  # 2b. Andrews Equality (Leo-III `ReplaceAndrewsEq`)
  # ---------------------------------------------------------------------------

  @doc """
  Rewrites Andrews equality `! [Q: ty > ty > $o]: ((! [X: ty]: Q @ X @ X) => Q @ u @ v)`
  (`Q` not free in `u`, `v`) to `u = v`, everywhere in `term_id`. Either disjunct
  order of the implication is recognized.
  """
  @spec rewrite_andrews(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def rewrite_andrews(%Arena{} = arena, term_id) do
    {tag, _flags, _ty_id, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_forall ->
        {arena, body} = rewrite_andrews(arena, right)

        case match_andrews_body(arena, left, body) do
          {:ok, arena, u, v} -> Arena.mk_eq(arena, u, v)
          :error -> Arena.mk_forall(arena, left, body)
        end

      @tag_lam ->
        {arena, b2} = rewrite_andrews(arena, right)
        Arena.mk_lam(arena, left, b2)

      @tag_app ->
        {arena, l2} = rewrite_andrews(arena, left)
        {arena, r2} = rewrite_andrews(arena, right)
        Arena.mk_app(arena, l2, r2)

      @tag_eq ->
        {arena, l2} = rewrite_andrews(arena, left)
        {arena, r2} = rewrite_andrews(arena, right)
        Arena.mk_eq(arena, l2, r2)

      @tag_or ->
        {arena, l2} = rewrite_andrews(arena, left)
        {arena, r2} = rewrite_andrews(arena, right)
        Arena.mk_or(arena, l2, r2)

      @tag_not ->
        {arena, l2} = rewrite_andrews(arena, left)
        Arena.mk_not(arena, l2)

      _ ->
        {arena, term_id}
    end
  end

  # Body of `! [Q]`: `~(! [X]: Q @ X @ X) | Q @ u @ v` with `Q` = BVar 0
  defp match_andrews_body(%Arena{} = arena, q_ty_id, body_id) do
    with {:arrow, dom_ty, rel_ty} <- Map.get(arena.type_table, q_ty_id),
         {:arrow, ^dom_ty, 0} <- Map.get(arena.type_table, rel_ty),
         {@tag_or, _, _, l_or, r_or} <- Arena.get_node(arena, body_id) do
      case andrews_disjuncts(arena, dom_ty, l_or, r_or) do
        {:ok, _, _, _} = ok -> ok
        :error -> andrews_disjuncts(arena, dom_ty, r_or, l_or)
      end
    else
      _ -> :error
    end
  end

  defp andrews_disjuncts(arena, dom_ty, neg_side, pos_side) do
    with {@tag_not, _, _, refl, _} <- Arena.get_node(arena, neg_side),
         {@tag_forall, _, _, ^dom_ty, refl_body} <- Arena.get_node(arena, refl),
         {:ok, x1, x2} <- match_bvar_app2(arena, refl_body, 1),
         {@tag_bvar, _, _, 0, _} <- Arena.get_node(arena, x1),
         true <- x1 == x2,
         {:ok, u_raw, v_raw} <- match_bvar_app2(arena, pos_side, 0),
         false <- Arena.occurs_bvar?(arena, u_raw, 0),
         false <- Arena.occurs_bvar?(arena, v_raw, 0) do
      {arena, u} = Arena.shift(arena, u_raw, -1, 1)
      {arena, v} = Arena.shift(arena, v_raw, -1, 1)
      {:ok, arena, u, v}
    else
      _ -> :error
    end
  end

  # `BVar(idx) @ a @ b` -> `{:ok, a, b}`
  defp match_bvar_app2(%Arena{} = arena, term_id, idx) do
    with {@tag_app, _, _, fa, b} <- Arena.get_node(arena, term_id),
         {@tag_app, _, _, f, a} <- Arena.get_node(arena, fa),
         {@tag_bvar, _, _, ^idx, _} <- Arena.get_node(arena, f) do
      {:ok, a, b}
    else
      _ -> :error
    end
  end

  # Clause-level `ReplaceAndrewsEq`: a clause with a negative literal `~(X @ t @ t)`,
  # `X` a free variable, gets the instance `X := ^ [Y, Z]: Y = Z` (literals
  # `~(t = t)` dropped) as an extra clause. Leo-III replaces the clause; the instance
  # alone is not equisatisfiable with it (`! [X]: X @ c @ c => X @ d @ d` with
  # `c != d` is unsatisfiable, the instance `d = d` is valid), so the original stays.
  defp andrews_instances(%Arena{} = arena, clauses, next_fvar, st) do
    {arena, _fvar, extra, st} =
      Enum.reduce(clauses, {arena, next_fvar, [], st}, fn clause, {ar, fvar, acc, st} ->
        case andrews_vars(ar, clause) do
          vars when map_size(vars) == 0 ->
            {ar, fvar, acc, st}

          vars ->
            {ar, subst} =
              Enum.reduce(vars, {ar, %{}}, fn {x, ty}, {ar, sub} ->
                {ar, y} = Arena.mk_bvar(ar, 1, ty)
                {ar, z} = Arena.mk_bvar(ar, 0, ty)
                {ar, eq} = Arena.mk_eq(ar, y, z)
                {ar, inner} = Arena.mk_lam(ar, ty, eq)
                {ar, rel} = Arena.mk_lam(ar, ty, inner)
                {ar, Map.put(sub, x, rel)}
              end)

            {ar, disj} = instance_formula(ar, clause, subst)
            univ = disj |> then(&Arena.free_vars(ar, &1)) |> Enum.sort()
            {ar, fvar, cls, st} = formula_to_clauses(ar, disj, :pos, fvar, st, univ)
            {ar, fvar, acc ++ Enum.reject(cls, &(&1 == clause)), st}
        end
      end)

    {arena, extra, st}
  end

  defp andrews_vars(%Arena{} = arena, clause) do
    Enum.reduce(clause, %{}, fn
      {:neg, atom}, acc ->
        with {:ok, x, ty, t1, t2} <- match_fvar_app2(arena, atom), true <- t1 == t2 do
          Map.put(acc, x, ty)
        else
          _ -> acc
        end

      _, acc ->
        acc
    end)
  end

  defp match_fvar_app2(%Arena{} = arena, term_id) do
    with {@tag_app, _, _, fa, b} <- Arena.get_node(arena, term_id),
         {@tag_app, _, _, f, a} <- Arena.get_node(arena, fa),
         {@tag_fvar, _, _, x, _} <- Arena.get_node(arena, f) do
      {:ok, x, Arena.type_of(arena, a), a, b}
    else
      _ -> :error
    end
  end

  # The instantiated clause as a disjunction, without the literals `~(t = t)`
  defp instance_formula(%Arena{} = arena, clause, subst) do
    {arena, lits} =
      clause
      |> Enum.sort()
      |> Enum.reduce({arena, []}, fn {pol, atom}, {ar, acc} ->
        {ar, inst} = Arena.subst_fvar(ar, atom, subst)

        case {pol, Arena.get_node(ar, inst)} do
          {:neg, {@tag_eq, _, _, s, s}} ->
            {ar, acc}

          {:neg, _} ->
            {ar, lit} = Arena.mk_not(ar, inst)
            {ar, [lit | acc]}

          {:pos, _} ->
            {ar, [inst | acc]}
        end
      end)

    build_disjunction(arena, Enum.reverse(lits))
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

  # `univ` lists the free variables `{fvar_id, ty_id}` of `term_id` that Skolem
  # functions must depend on (empty for closed input formulas).
  defp formula_to_clauses(%Arena{} = arena, term_id, polarity, next_fvar, st, univ \\ []) do
    {arena, univ_vars} =
      Enum.reduce(univ, {arena, []}, fn {id, ty}, {ar, acc} ->
        {ar, node} = Arena.mk_fvar(ar, id, ty)
        {ar, acc ++ [{id, ty, node}]}
      end)

    next_fvar = Enum.reduce(univ, next_fvar, fn {id, _ty}, nf -> max(nf, id + 1) end)
    ctx = %{univ_vars: univ_vars, next_fvar: next_fvar, bool_splits: 0, ext_depth: 0}
    {arena, nnf_tree, ctx} = to_nnf(arena, term_id, polarity, ctx)

    {arena, trees, st} =
      if st.renaming, do: rename_formula(arena, nnf_tree, st), else: {arena, [nnf_tree], st}

    {raw_clauses, st} =
      Enum.reduce(trees, {[], st}, fn tree, {acc, st} ->
        {cls, truncated} = nnf_to_cnf(tree)
        {acc ++ cls, if(truncated, do: %{st | cnf_truncated: st.cnf_truncated + 1}, else: st)}
      end)

    {arena, final_fvar, clean_clauses} =
      Enum.reduce(raw_clauses, {arena, ctx.next_fvar, []}, fn lits, {ar, fvar, acc} ->
        case normalize_and_filter_clause(ar, lits, fvar) do
          {:tautology, ar2, fvar2} ->
            {ar2, fvar2, acc}

          {:ok, ar2, fvar2, clause} ->
            {ar2, fvar2, [clause | acc]}
        end
      end)

    {arena, final_fvar, Enum.reverse(clean_clauses), st}
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

  # `A <=> A` is valid. Without this clause, factoring the shared conjunct `A` would rewrite
  # it to `A => ($true <=> $true)`, and `$true <=> $true` into itself forever.
  defp to_nnf_bool_eq(%Arena{} = arena, same, same, polarity, ctx) do
    {arena, if(polarity == :pos, do: :top, else: :bot), ctx}
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

  # Returns `{clauses, truncated?}`: beyond `@max_cnf_clauses_per_formula` clauses
  # are dropped, which keeps refutations sound but loses models.
  defp nnf_to_cnf(:top), do: {[], false}
  defp nnf_to_cnf(:bot), do: {[[]], false}
  defp nnf_to_cnf({:lit, pol, id}), do: {[[{pol, id}]], false}

  defp nnf_to_cnf({:and, l, r}) do
    {cls_l, t_l} = nnf_to_cnf(l)
    {cls_r, t_r} = nnf_to_cnf(r)
    all = cls_l ++ cls_r
    kept = Enum.take(all, @max_cnf_clauses_per_formula)
    {kept, t_l or t_r or length(kept) < length(all)}
  end

  defp nnf_to_cnf({:or, l, r}) do
    {cls_l, t_l} = nnf_to_cnf(l)
    {cls_r, t_r} = nnf_to_cnf(r)

    cond do
      cls_l == [] or cls_r == [] ->
        {[], false}

      length(cls_l) * length(cls_r) <= @max_cnf_clauses_per_formula ->
        {for(c1 <- cls_l, c2 <- cls_r, do: c1 ++ c2), t_l or t_r}

      true ->
        {for(c1 <- Enum.take(cls_l, 8), c2 <- Enum.take(cls_r, 8), do: c1 ++ c2), true}
    end
  end

  # ---------------------------------------------------------------------------
  # 4b. Formula Renaming (Leo-III `FormulaRenaming`, `RenameCNF`)
  # ---------------------------------------------------------------------------

  # Renames the NNF tree; returns the main tree followed by the definition trees
  # `~d(X1, ..., Xn) | S` that were introduced (already renamed themselves).
  defp rename_formula(%Arena{} = arena, tree, st) do
    {arena, tree, st, defs} = rename(arena, tree, st, [])
    {arena, [tree | Enum.reverse(defs)], st}
  end

  # `FormulaRenaming.canApply` on a positive disjunction `a | b`: rename `b` iff
  # `size(a) * size(b) > size(a) + size(b) + threshold`. Following
  # `FormulaRenaming.apply`, an already defined `a` is reused instead. Renaming a
  # literal gains nothing, which also keeps negative thresholds terminating.
  defp rename(arena, {:or, a, b}, st, defs) do
    sa = cnf_size(a)
    sb = cnf_size(b)

    if sa * sb > sa + sb + st.threshold and (renamable?(a) or renamable?(b)) do
      {arena, a_def} = if renamable?(a), do: def_atom(arena, a), else: {arena, nil}

      {arena, tree, st, defs} =
        cond do
          a_def != nil and MapSet.member?(st.defined, elem(a_def, 0)) ->
            {arena, {:or, {:lit, :pos, elem(a_def, 1)}, b}, st, defs}

          renamable?(b) ->
            {arena, lit, st, defs} = define(arena, b, st, defs)
            {arena, {:or, a, lit}, st, defs}

          true ->
            {arena, lit, st, defs} = define(arena, a, st, defs)
            {arena, {:or, lit, b}, st, defs}
        end

      rename(arena, tree, st, defs)
    else
      {arena, a2, st, defs} = rename(arena, a, st, defs)
      {arena, b2, st, defs} = rename(arena, b, st, defs)
      {arena, {:or, a2, b2}, st, defs}
    end
  end

  defp rename(arena, {:and, a, b}, st, defs) do
    {arena, a2, st, defs} = rename(arena, a, st, defs)
    {arena, b2, st, defs} = rename(arena, b, st, defs)
    {arena, {:and, a2, b2}, st, defs}
  end

  defp rename(arena, tree, st, defs), do: {arena, tree, st, defs}

  defp renamable?({:and, _, _}), do: true
  defp renamable?({:or, _, _}), do: true
  defp renamable?(_), do: false

  # Number of CNF clauses of an NNF tree (`FormulaRenaming.size`)
  defp cnf_size({:and, l, r}), do: cnf_size(l) + cnf_size(r)
  defp cnf_size({:or, l, r}), do: cnf_size(l) * cnf_size(r)
  defp cnf_size(:top), do: 0
  defp cnf_size(_), do: 1

  # Replaces `sub` by its definition atom; the definition `~d(X1, ..., Xn) | sub`
  # is emitted once per symbol (`renamingCash`), renamed in turn.
  defp define(arena, sub, st, defs) do
    {arena, {name, atom}} = def_atom(arena, sub)

    if MapSet.member?(st.defined, name) do
      {arena, {:lit, :pos, atom}, st, defs}
    else
      st = %{st | defined: MapSet.put(st.defined, name), definitions: st.definitions + 1}
      {arena, def_tree, st, defs} = rename(arena, {:or, {:lit, :neg, atom}, sub}, st, defs)
      {arena, {:lit, :pos, atom}, st, [def_tree | defs]}
    end
  end

  # Content-addressed definition symbol: `d = def_<hash>` with
  # `hash = sha256(^ [X1, ..., Xn]: S)` over `Arena.canonical_bytes/2`, where `S` is
  # the subformula as a term and `X1, ..., Xn` its free variables in order of first
  # occurrence. Returns `{name, d @ X1 @ ... @ Xn}`.
  defp def_atom(arena, sub) do
    {arena, body} = tree_to_term(arena, sub)
    fvars = ordered_fvars(arena, body, [])

    {arena, closed} =
      Enum.reduce(Enum.reverse(fvars), {arena, body}, fn fv, {ar, acc} ->
        {ar, abs} = Arena.abstract_subterm(ar, acc, fv)
        Arena.mk_lam(ar, Arena.type_of(ar, fv), abs)
      end)

    <<hash::64, _::binary>> = :crypto.hash(:sha256, ["def", Arena.canonical_bytes(arena, closed)])
    name = "def_" <> String.downcase(String.pad_leading(Integer.to_string(hash, 16), 16, "0"))
    {arena, d} = Arena.mk_const(arena, name, Arena.type_of(arena, closed))

    {arena, atom} =
      Enum.reduce(fvars, {arena, d}, fn fv, {ar, acc} -> Arena.mk_app(ar, acc, fv) end)

    {arena, {name, atom}}
  end

  defp tree_to_term(arena, {:lit, :pos, id}), do: {arena, id}
  defp tree_to_term(arena, {:lit, :neg, id}), do: Arena.mk_not(arena, id)
  defp tree_to_term(arena, :top), do: Arena.mk_const(arena, "$true", :o)
  defp tree_to_term(arena, :bot), do: Arena.mk_const(arena, "$false", :o)

  defp tree_to_term(arena, {op, l, r}) do
    {arena, lt} = tree_to_term(arena, l)
    {arena, rt} = tree_to_term(arena, r)
    if op == :and, do: Arena.mk_and(arena, lt, rt), else: Arena.mk_or(arena, lt, rt)
  end

  # Free variable nodes of `term_id` in order of first occurrence (left to right)
  defp ordered_fvars(arena, term_id, acc) do
    {tag, flags, _ty, left, right} = Arena.get_node(arena, term_id)

    cond do
      Bitwise.band(flags, 2) == 0 ->
        acc

      tag == @tag_fvar ->
        if term_id in acc, do: acc, else: acc ++ [term_id]

      tag == @tag_not ->
        ordered_fvars(arena, left, acc)

      tag in [@tag_lam, @tag_forall] ->
        ordered_fvars(arena, right, acc)

      tag in [@tag_app, @tag_eq, @tag_or] ->
        ordered_fvars(arena, right, ordered_fvars(arena, left, acc))

      true ->
        acc
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
