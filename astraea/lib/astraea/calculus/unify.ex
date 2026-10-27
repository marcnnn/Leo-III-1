defmodule Astraea.Calculus.Unify do
  @moduledoc """
  Huet-style higher-order pre-unification over `Astraea.Arena` (Leo-III `PreUni`,
  `PatternUni` and `FlexFlexUni`, `leo.modules.calculus.Unification`).

  A unification problem is a list of pairs `{s, t, k}` under `k` common binders
  (loose de Bruijn indices `< k`). The deterministic rules are applied exhaustively:

    * *delete* `s = s`, *eta* (pairs of arrow type are compared under a new binder),
    * *decompose* rigid-rigid pairs with equal heads (a head clash fails),
    * *bind* / pattern fast path: `F xs = t` where `xs` are distinct bound variables,
      `F` does not occur in `t` and the loose bound variables of `t` are among `xs`
      is solved by the most general binding `F := ^ [xs]: t`; if `F` occurs on a
      rigid path of `t` the pair has no unifier,
    * flex-rigid pairs that are not solved this way and flex-flex pairs are postponed.

  When only postponed pairs remain, the first flex-rigid pair is solved
  nondeterministically by *imitation* of the rigid head and by every type-correct
  *projection*. The search tree is explored breadth-first, so unifiers come out in
  order of increasing search depth.

  Flex-flex pairs are never enumerated (pre-unification). They are closed off when a
  unifier is reported: pattern pairs by their most general unifier (`F xs = F ys`
  and `F xs = G ys`), other pairs by the trivial binding of both heads to the same
  fresh constant function. All bindings are instances, so every reported unifier is
  sound for the `:subst` kernel rule; only completeness is lost.

  The search is bounded by `:max_depth` (imitation/projection steps per branch),
  `:max_unifiers` and `:max_steps` (expanded configurations). Every cut-off branch,
  truncated search and trivially closed flex-flex pair is counted in `cutoffs` so the
  prover can tell an exhausted search from a saturated one.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @default_opts [max_depth: 2, max_unifiers: 2, max_steps: 24]

  @type pair :: {Arena.term_id(), Arena.term_id()}
  @type result :: {Arena.t(), non_neg_integer(), [Arena.subst()], non_neg_integer()}

  @doc """
  Returns up to `:max_unifiers` pre-unifiers of all `pairs` (closed terms), each
  restricted to the free variables of the problem and fully resolved (no binding
  refers to another bound variable of the same unifier).

  `next_fvar` is the first free-variable id the search may use for fresh variables;
  the returned counter is past every fresh variable used in a returned unifier.
  """
  @spec unifiers(Arena.t(), [pair()], non_neg_integer(), keyword()) :: result()
  def unifiers(%Arena{} = arena, pairs, next_fvar, opts \\ []) do
    opts = Map.new(Keyword.merge(@default_opts, opts))

    domain =
      Enum.reduce(pairs, MapSet.new(), fn {s, t}, acc ->
        acc |> MapSet.union(Arena.free_vars(arena, s)) |> MapSet.union(Arena.free_vars(arena, t))
      end)

    root = %{
      todo: Enum.map(pairs, fn {s, t} -> {s, t, 0} end),
      flex_rigid: [],
      flex_flex: [],
      subst: %{},
      depth: 0
    }

    ctx = %{arena: arena, next_fvar: next_fvar, cutoffs: 0}
    {ctx, substs} = search(:queue.from_list([root]), ctx, [], opts.max_steps, opts)
    {unifiers, ctx} = Enum.map_reduce(substs, ctx, &restrict(&2, &1, domain))
    {ctx.arena, ctx.next_fvar, Enum.uniq(unifiers), ctx.cutoffs}
  end

  @doc """
  Returns the first pre-unifier of `s` and `t`, or `:error` (convenience for tests).
  """
  @spec unify(Arena.t(), Arena.term_id(), Arena.term_id(), non_neg_integer(), keyword()) ::
          {:ok, Arena.t(), Arena.subst()} | :error
  def unify(%Arena{} = arena, s, t, next_fvar, opts \\ []) do
    case unifiers(arena, [{s, t}], next_fvar, Keyword.put(opts, :max_unifiers, 1)) do
      {arena, _nf, [subst | _], _cut} -> {:ok, arena, subst}
      _ -> :error
    end
  end

  # ---------------------------------------------------------------------------
  # Breadth-first search over configurations
  # ---------------------------------------------------------------------------

  defp search(queue, ctx, found, steps, opts) do
    cond do
      :queue.is_empty(queue) ->
        {ctx, Enum.reverse(found)}

      length(found) >= opts.max_unifiers or steps == 0 ->
        {cut(ctx), Enum.reverse(found)}

      true ->
        {{:value, conf}, rest} = :queue.out(queue)

        case exhaust(ctx, conf) do
          {ctx, :fail} ->
            search(rest, ctx, found, steps - 1, opts)

          {ctx, {:solved, subst}} ->
            search(rest, ctx, [subst | found], steps - 1, opts)

          {ctx, {:branch, _pair, %{depth: d}}} when d >= opts.max_depth ->
            search(rest, cut(ctx), found, steps - 1, opts)

          {ctx, {:branch, pair, conf}} ->
            {ctx, children} = branch(ctx, pair, conf)
            queue = Enum.reduce(children, rest, &:queue.in/2)
            search(queue, ctx, found, steps - 1, opts)
        end
    end
  end

  defp cut(ctx), do: %{ctx | cutoffs: ctx.cutoffs + 1}

  # ---------------------------------------------------------------------------
  # Deterministic rules (Leo-III `detExhaust`)
  # ---------------------------------------------------------------------------

  defp exhaust(ctx, %{todo: [pair | rest]} = conf), do: step(ctx, pair, %{conf | todo: rest})

  defp exhaust(ctx, %{flex_rigid: [pair | rest]} = conf),
    do: {ctx, {:branch, pair, %{conf | flex_rigid: rest}}}

  defp exhaust(ctx, %{flex_flex: []} = conf), do: {ctx, {:solved, conf.subst}}

  defp exhaust(ctx, %{flex_flex: [pair | rest]} = conf),
    do: close_flex_flex(ctx, pair, %{conf | flex_flex: rest})

  defp step(ctx, {s0, t0, k}, conf) do
    cond do
      s0 == t0 ->
        exhaust(ctx, conf)

      Arena.type_of(ctx.arena, s0) != Arena.type_of(ctx.arena, t0) ->
        {ctx, :fail}

      true ->
        {arena, s} = deref_head(ctx.arena, s0, conf.subst)
        {arena, t} = deref_head(arena, t0, conf.subst)
        ctx = %{ctx | arena: arena}

        cond do
          s == t ->
            exhaust(ctx, conf)

          Arena.type_of(arena, s) != Arena.type_of(arena, t) ->
            {ctx, :fail}

          # Two rigid eta-short terms of arrow type decompose like their eta-expansions.
          Terms.arrow_domain(arena, Arena.type_of(arena, s)) != nil and
              not (rigid?(arena, s) and rigid?(arena, t)) ->
            {arena, s1} = Terms.eta_body(arena, s)
            {arena, t1} = Terms.eta_body(arena, t)
            exhaust(%{ctx | arena: arena}, push(conf, [{s1, t1, k + 1}]))

          true ->
            dispatch(ctx, {s, t, k}, Terms.view(arena, s), Terms.view(arena, t), conf)
        end
    end
  end

  defp deref_head(arena, term_id, subst) do
    if map_size(subst) == 0 or not Terms.has_fvar?(arena, term_id) do
      {arena, term_id}
    else
      case Terms.view(arena, term_id) do
        {:flex, f, args} ->
          var = var_id(arena, f)

          case Map.fetch(subst, var) do
            {:ok, rep} ->
              {arena, app} =
                if args == [] do
                  {arena, rep}
                else
                  {arena, ap} = Terms.mk_apps(arena, rep, args)
                  Arena.beta_eta_norm(arena, ap)
                end

              deref_head(arena, app, subst)

            :error ->
              {arena, term_id}
          end

        _ ->
          {arena, term_id}
      end
    end
  end

  defp rigid?(arena, t), do: match?({:rigid, _, _}, Terms.view(arena, t))

  defp dispatch(ctx, {_s, _t, k}, {:rigid, h, cs}, {:rigid, h, ds}, conf)
       when length(cs) == length(ds) do
    pairs = Enum.zip_with(cs, ds, fn {c, shift}, {d, shift} -> {c, d, k + shift} end)
    exhaust(ctx, push(conf, pairs))
  end

  defp dispatch(ctx, _pair, {:rigid, _, _}, {:rigid, _, _}, _conf), do: {ctx, :fail}

  defp dispatch(ctx, {s, t, k} = pair, {:flex, f, as}, {:flex, g, bs}, conf) do
    with :postpone <- try_bind(ctx, f, as, t, k, conf.subst),
         :postpone <- try_bind(ctx, g, bs, s, k, conf.subst) do
      exhaust(ctx, %{conf | flex_flex: [pair | conf.flex_flex]})
    else
      result -> continue_bind(ctx, result, conf)
    end
  end

  defp dispatch(ctx, {s, t, k}, {:rigid, _, _} = rv, {:flex, _, _} = fv, conf),
    do: dispatch(ctx, {t, s, k}, fv, rv, conf)

  defp dispatch(ctx, {_s, t, k} = pair, {:flex, f, as}, {:rigid, _, _}, conf) do
    case try_bind(ctx, f, as, t, k, conf.subst) do
      :postpone -> exhaust(ctx, %{conf | flex_rigid: conf.flex_rigid ++ [pair]})
      result -> continue_bind(ctx, result, conf)
    end
  end

  defp continue_bind(ctx, :fail, _conf), do: {ctx, :fail}

  defp continue_bind(_ctx, {:bind, ctx, var, binding}, conf),
    do: exhaust(ctx, rebind(conf, var, binding))

  # Adds `var := binding` and moves postponed pairs back to the work list, since
  # they may have become decomposable.
  defp rebind(conf, var, binding) do
    %{
      conf
      | subst: Map.put(conf.subst, var, binding),
        todo: conf.todo ++ conf.flex_rigid ++ conf.flex_flex,
        flex_rigid: [],
        flex_flex: []
    }
  end

  defp push(conf, pairs), do: %{conf | todo: pairs ++ conf.todo}

  # Pattern fast path (Leo-III `BindRule` generalised to Miller patterns).
  defp try_bind(ctx, f, args, t0, k, subst) do
    arena = ctx.arena
    var = var_id(arena, f)

    case pattern_indices(arena, args, k) do
      {:ok, idxs} ->
        {arena, t} = Terms.instantiate(arena, t0, subst)
        ctx = %{ctx | arena: arena}

        cond do
          not Arena.occurs_fvar?(arena, t, var) ->
            abstract(ctx, var, args, idxs, t)

          rigid_occurs?(arena, var, t) ->
            :fail

          true ->
            :postpone
        end

      :error ->
        :postpone
    end
  end

  defp abstract(ctx, var, args, idxs, t) do
    n = length(idxs)
    renaming = idxs |> Enum.with_index() |> Map.new(fn {i, j} -> {i, n - 1 - j} end)

    case Terms.rename_loose(ctx.arena, t, renaming) do
      {:ok, arena, body} ->
        {arena, binding} = Terms.mk_lams(arena, Enum.map(args, &Arena.type_of(arena, &1)), body)
        {:bind, %{ctx | arena: arena}, var, binding}

      :error ->
        if not Terms.has_fvar?(ctx.arena, t) or rigid_bvar_escape?(ctx.arena, t, renaming, 0) do
          :fail
        else
          :postpone
        end
    end
  end

  defp rigid_bvar_escape?(arena, term_id, renaming, depth) do
    case Terms.view(arena, term_id) do
      {:flex, _f, _args} ->
        false

      {:rigid, _head, args} ->
        case Arena.get_node(arena, term_id) do
          {1, _, _, idx, _} ->
            not Map.has_key?(renaming, idx - depth)

          _ ->
            Enum.any?(args, fn {arg, _shift} ->
              rigid_bvar_escape?(arena, arg, renaming, depth)
            end)
        end

      {:lam, _dom, body} ->
        rigid_bvar_escape?(arena, body, renaming, depth + 1)
    end
  end

  # Distinct bound variables, all bound inside the `k` common binders.
  defp pattern_indices(arena, args, k) do
    idxs = Enum.map(args, &(Terms.bvar?(arena, &1) && Terms.bvar_index(arena, &1)))

    if Enum.all?(idxs, &(is_integer(&1) and &1 < k)) and Enum.uniq(idxs) == idxs,
      do: {:ok, idxs},
      else: :error
  end

  # `F` occurs below a path of rigid heads of `t`: no unifier exists when `F` is a pattern.
  defp rigid_occurs?(arena, var, t) do
    case Terms.view(arena, t) do
      {:flex, _g, _args} -> false
      {:rigid, _h, cs} -> Enum.any?(cs, fn {c, _} -> on_rigid_path?(arena, var, c) end)
      {:lam, _dom, body} -> rigid_occurs?(arena, var, body)
    end
  end

  defp on_rigid_path?(arena, var, t) do
    case Terms.view(arena, t) do
      {:flex, g, _args} -> var_id(arena, g) == var
      _ -> rigid_occurs?(arena, var, t)
    end
  end

  defp var_id(arena, fvar_node), do: elem(Arena.get_node(arena, fvar_node), 3)

  # ---------------------------------------------------------------------------
  # Nondeterministic rules: imitation and projection
  # ---------------------------------------------------------------------------

  defp branch(ctx, {s, t, _k} = pair, conf) do
    {flex, rigid} = if Terms.flex?(ctx.arena, s), do: {s, t}, else: {t, s}
    {f, _args} = Terms.spine(ctx.arena, flex)
    {taus, beta} = Terms.arrow_types(ctx.arena, Arena.type_of(ctx.arena, f))
    {:rigid, head, _} = Terms.view(ctx.arena, rigid)

    {ctx, imitation} = imitation(ctx, taus, head)
    {ctx, projections} = projections(ctx, taus, beta)

    children =
      for binding <- imitation ++ projections do
        conf
        |> Map.put(:todo, [pair])
        |> rebind(var_id(ctx.arena, f), binding)
        |> Map.update!(:depth, &(&1 + 1))
      end

    {ctx, children}
  end

  # A bound variable of the common binder prefix cannot be imitated (it would escape).
  defp imitation(ctx, taus, {:sym, h}) do
    if Terms.bvar?(ctx.arena, h), do: {ctx, []}, else: wrap(build(ctx, taus, {:sym, h}))
  end

  defp imitation(ctx, taus, head), do: wrap(build(ctx, taus, head))

  defp projections(ctx, taus, beta) do
    taus
    |> Enum.with_index()
    |> Enum.filter(fn {tau, _j} -> elem(Terms.arrow_types(ctx.arena, tau), 1) == beta end)
    |> Enum.map_reduce(ctx, fn {_tau, j}, ctx -> swap(build(ctx, taus, {:project, j})) end)
    |> swap()
  end

  defp wrap({ctx, binding}), do: {ctx, [binding]}

  @doc """
  Huet's partial binding for a variable of type `taus > b`: `^ [xs]: h @ (H1 @ xs) ...
  @ (Hm @ xs)` with fresh `Hi`, where `h` is a symbol (`{:sym, id}`), a connective
  (`{:eq, ty}`, `:not`, `:or`, `{:forall, ty}`) or the projection `{:project, j}`
  onto the `j`-th bound variable. Shared with primitive substitution.
  """
  @spec partial_binding(
          Arena.t(),
          non_neg_integer(),
          [Arena.type_id()],
          Terms.head() | {:project, non_neg_integer()}
        ) ::
          {Arena.t(), non_neg_integer(), Arena.term_id()}
  def partial_binding(%Arena{} = arena, next_fvar, taus, head) do
    {ctx, binding} = build(%{arena: arena, next_fvar: next_fvar, cutoffs: 0}, taus, head)
    {ctx.arena, ctx.next_fvar, binding}
  end

  defp build(ctx, taus, {:sym, h}) do
    {sigmas, _} = Terms.arrow_types(ctx.arena, Arena.type_of(ctx.arena, h))
    {ctx, args} = fresh_apps(ctx, taus, sigmas)
    lam(ctx, taus, &Terms.mk_apps(&1, h, args))
  end

  defp build(ctx, taus, {:project, j}) do
    tau = Enum.at(taus, j)
    {rhos, _} = Terms.arrow_types(ctx.arena, tau)
    {ctx, args} = fresh_apps(ctx, taus, rhos)
    {arena, xj} = Arena.mk_bvar(ctx.arena, length(taus) - 1 - j, tau)
    lam(%{ctx | arena: arena}, taus, &Terms.mk_apps(&1, xj, args))
  end

  defp build(ctx, taus, {:eq, ty}) do
    {ctx, [l, r]} = fresh_apps(ctx, taus, [ty, ty])
    lam(ctx, taus, &Arena.mk_eq(&1, l, r))
  end

  defp build(ctx, taus, :not) do
    {ctx, [a]} = fresh_apps(ctx, taus, [Arena.ty_o()])
    lam(ctx, taus, &Arena.mk_not(&1, a))
  end

  defp build(ctx, taus, :or) do
    {ctx, [l, r]} = fresh_apps(ctx, taus, [Arena.ty_o(), Arena.ty_o()])
    lam(ctx, taus, &Arena.mk_or(&1, l, r))
  end

  defp build(ctx, taus, {:forall, dom}) do
    # Inside the quantifier the prefix `xs` is shifted by one and `Y` is `BVar(0)`.
    {ctx, body} = fresh_app(ctx, taus ++ [dom], Arena.ty_o())
    lam(ctx, taus, &Arena.mk_forall(&1, dom, body))
  end

  defp lam(ctx, taus, mk_body) do
    {arena, body} = mk_body.(ctx.arena)
    {arena, binding} = Terms.mk_lams(arena, taus, body)
    {%{ctx | arena: arena}, binding}
  end

  defp fresh_apps(ctx, taus, sigmas) do
    {apps, ctx} =
      Enum.map_reduce(sigmas, ctx, fn sigma, ctx -> swap(fresh_app(ctx, taus, sigma)) end)

    {ctx, apps}
  end

  # `H @ X1 @ ... @ Xn` for a fresh `H: taus > sigma` and the binder prefix `taus`.
  defp fresh_app(ctx, taus, sigma) do
    {arena, h} = fresh_var(ctx.arena, ctx.next_fvar, taus, sigma)
    {arena, xs} = Terms.bound_args(arena, taus)
    {arena, app} = Terms.mk_apps(arena, h, xs)
    {%{ctx | arena: arena, next_fvar: ctx.next_fvar + 1}, app}
  end

  defp fresh_var(arena, id, taus, sigma) do
    {arena, ty} = Terms.mk_arrows(arena, taus, sigma)
    Arena.mk_fvar(arena, id, ty)
  end

  defp swap({a, b}), do: {b, a}

  # ---------------------------------------------------------------------------
  # Closing flex-flex constraints (Leo-III `FlexFlexUni` / `PatternUni.flexflex`)
  # ---------------------------------------------------------------------------

  defp close_flex_flex(ctx, {s0, t0, k}, conf) do
    {arena, s} = Terms.instantiate(ctx.arena, s0, conf.subst)
    {arena, t} = Terms.instantiate(arena, t0, conf.subst)
    ctx = %{ctx | arena: arena}

    if s == t do
      exhaust(ctx, conf)
    else
      {f, as} = Terms.spine(arena, s)
      {g, bs} = Terms.spine(arena, t)

      {ctx, bindings, pairs} =
        with {:ok, ia} <- pattern_indices(arena, as, k),
             {:ok, ib} <- pattern_indices(arena, bs, k) do
          {ctx, bindings} = pattern_flex_flex(ctx, {f, ia}, {g, ib})
          {ctx, bindings, [{s0, t0, k}]}
        else
          :error -> non_pattern_flex_flex(cut(ctx), {f, as}, {g, bs}, {s0, t0, k})
        end

      conf = Enum.reduce(bindings, conf, fn {var, b}, cf -> rebind(cf, var, b) end)
      exhaust(ctx, %{conf | todo: pairs ++ conf.todo})
    end
  end

  # Outside the pattern fragment: decompose `F as = G bs` into `F := G` and `as = bs`
  # (a unifier, not a most general one) unless two arguments clash rigidly, else bind
  # both heads to the same fresh constant function.
  defp non_pattern_flex_flex(ctx, {f, as}, {g, bs}, {_s, _t, k} = pair) do
    arena = ctx.arena

    decomposable? =
      Arena.type_of(arena, f) == Arena.type_of(arena, g) and length(as) == length(bs) and
        not Enum.any?(Enum.zip(as, bs), fn {a, b} -> clash?(arena, a, b) end)

    if decomposable? do
      bindings = if f == g, do: [], else: [{var_id(arena, f), g}]
      {ctx, bindings, Enum.zip_with(as, bs, &{&1, &2, k})}
    else
      {ctx, bindings} = trivial_flex_flex(ctx, f, g)
      {ctx, bindings, [pair]}
    end
  end

  defp clash?(arena, a, b) do
    case {Terms.view(arena, a), Terms.view(arena, b)} do
      {{:rigid, h1, _}, {:rigid, h2, _}} -> h1 != h2
      _ -> false
    end
  end

  # `F xs = F ys`: keep the arguments where `xs` and `ys` agree.
  defp pattern_flex_flex(ctx, {f, ia}, {f, ib}) do
    keep = for {{x, y}, j} <- Enum.with_index(Enum.zip(ia, ib)), x == y, do: j
    {ctx, binding} = restricted_binding(ctx, f, keep)
    {ctx, [{var_id(ctx.arena, f), binding}]}
  end

  # `F xs = G ys`: both become `H` applied to the bound variables they share.
  defp pattern_flex_flex(ctx, {f, ia}, {g, ib}) do
    common = Enum.filter(ia, &(&1 in ib))
    positions = fn idxs -> Enum.map(common, fn i -> Enum.find_index(idxs, &(&1 == i)) end) end
    {ctx, h} = shared_head(ctx, f, positions.(ia))
    {ctx, bf} = binding_with_head(ctx, f, positions.(ia), h)
    {ctx, bg} = binding_with_head(ctx, g, positions.(ib), h)
    {ctx, [{var_id(ctx.arena, f), bf}, {var_id(ctx.arena, g), bg}]}
  end

  defp trivial_flex_flex(ctx, f, g) do
    {ctx, h} = shared_head(ctx, f, [])
    {ctx, bf} = binding_with_head(ctx, f, [], h)
    {ctx, bg} = binding_with_head(ctx, g, [], h)
    {ctx, Enum.uniq_by([{var_id(ctx.arena, f), bf}, {var_id(ctx.arena, g), bg}], &elem(&1, 0))}
  end

  defp restricted_binding(ctx, f, keep) do
    {ctx, h} = shared_head(ctx, f, keep)
    binding_with_head(ctx, f, keep, h)
  end

  # Fresh `H` whose arguments are the `keep` positions of `f`'s argument types.
  defp shared_head(ctx, f, keep) do
    {taus, beta} = Terms.arrow_types(ctx.arena, Arena.type_of(ctx.arena, f))
    {arena, h} = fresh_var(ctx.arena, ctx.next_fvar, Enum.map(keep, &Enum.at(taus, &1)), beta)
    {%{ctx | arena: arena, next_fvar: ctx.next_fvar + 1}, h}
  end

  # `^ [xs]: H @ x_p1 @ ... @ x_pm` for the positions `p` of `f`'s binder prefix.
  defp binding_with_head(ctx, f, positions, h) do
    {taus, _beta} = Terms.arrow_types(ctx.arena, Arena.type_of(ctx.arena, f))
    {arena, xs} = Terms.bound_args(ctx.arena, taus)
    {arena, body} = Terms.mk_apps(arena, h, Enum.map(positions, &Enum.at(xs, &1)))
    {arena, binding} = Terms.mk_lams(arena, taus, body)
    {%{ctx | arena: arena}, binding}
  end

  # ---------------------------------------------------------------------------
  # Solved form
  # ---------------------------------------------------------------------------

  defp restrict(ctx, subst, domain) do
    Enum.reduce(domain, {%{}, ctx}, fn {var, ty}, {acc, ctx} ->
      if Map.has_key?(subst, var) do
        {arena, fv} = Arena.mk_fvar(ctx.arena, var, ty)
        {arena, value} = Arena.subst_fvar(arena, fv, subst)
        {Map.put(acc, var, value), %{ctx | arena: arena}}
      else
        {acc, ctx}
      end
    end)
  end
end
