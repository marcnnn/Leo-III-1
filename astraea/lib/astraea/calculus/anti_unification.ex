defmodule Astraea.Calculus.AntiUnification do
  @moduledoc """
  Higher-order pattern anti-unification over `Astraea.Arena` (Leo-III
  `PatternAntiUnification`, `leo.modules.calculus.AntiUnification`), after
  Baumgartner, Kutsia, Levy and Villaret, "Higher-Order Pattern Anti-Unification in
  Linear Time" (JAR 2017).

  `generalize/4` returns the least general higher-order pattern generalization `r`
  of two terms `s` and `t` of the same type, with substitutions `sigma` and `rho`
  such that `r sigma = s` and `r rho = t` (up to beta-eta). It is the library
  half of macro-rule learning (`Notes/thesis_work_log.md`, Entry 001).

  The rules of the paper work on anti-unification problems `X(xs): s = t`, where
  `xs` are the bound variables in scope; the generalization is built directly
  instead of composing the approximating substitutions of Leo-III:

    * *abstraction*: at arrow type both sides are compared under a new binder
      (eta-expanding an eta-short side, as Leo-III's `etaExpand`),
    * *decomposition*: equal rigid heads (a constant, Skolem, combinator, bound
      variable or connective) with equal argument count are kept and their
      arguments generalized,
    * *solve*: otherwise the pair becomes `Y(ys)`, `Y` fresh and `ys` the bound
      variables that occur in `s` or `t`, ordered by first occurrence,
    * *merge*: a pair equal to an earlier one up to a bijective renaming of the
      bound variables reuses its variable, so `f(a, g(a))` and `f(b, g(b))`
      generalize to `f(X, g(X))`. With `ys` in first-occurrence order the renaming
      is the identity on argument positions.

  Free variables of the inputs are treated as constants (decomposed when they head
  both sides), so shared variables survive in the generalization; Leo-III
  generalizes them like a head clash. Fresh variables are numbered from
  `next_fvar`.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_bvar 2
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @type result :: {Arena.term_id(), Arena.subst(), Arena.subst()}

  @doc """
  The least general pattern generalization `{r, sigma, rho}` of the beta-eta normal
  terms `s` and `t`; `sigma` and `rho` bind exactly the fresh variables of `r`.
  `next_fvar` defaults to one past the largest free variable of `s` and `t`.
  Returns `:error` if the types differ.
  """
  @spec generalize(Arena.t(), Arena.term_id(), Arena.term_id(), non_neg_integer() | nil) ::
          {:ok, Arena.t(), non_neg_integer(), result()} | :error
  def generalize(arena, s, t, next_fvar \\ nil)

  def generalize(%Arena{} = arena, s, t, next_fvar) do
    if Arena.type_of(arena, s) != Arena.type_of(arena, t) do
      :error
    else
      next = next_fvar || first_free_id(arena, [s, t])
      ctx = %{arena: arena, next: next, store: %{}, left: %{}, right: %{}}
      {ctx, r} = gen(ctx, s, t)
      {arena, r} = Arena.beta_eta_norm(ctx.arena, r)
      {:ok, arena, ctx.next, {r, ctx.left, ctx.right}}
    end
  end

  defp first_free_id(arena, terms) do
    terms
    |> Enum.flat_map(&(arena |> Arena.free_vars(&1) |> Enum.map(fn {id, _ty} -> id end)))
    |> Enum.max(fn -> -1 end)
    |> Kernel.+(1)
  end

  # ---------------------------------------------------------------------------
  # Abstraction and decomposition (Leo-III `phase1`)
  # ---------------------------------------------------------------------------

  defp gen(ctx, s, s), do: {ctx, s}

  defp gen(ctx, s, t) do
    ty = Arena.type_of(ctx.arena, s)

    case Terms.arrow_domain(ctx.arena, ty) do
      nil ->
        decompose(ctx, s, t)

      dom ->
        {arena, s_body} = Terms.eta_body(ctx.arena, s)
        {arena, t_body} = Terms.eta_body(arena, t)
        {ctx, r_body} = gen(%{ctx | arena: arena}, s_body, t_body)
        {arena, r} = Arena.mk_lam(ctx.arena, dom, r_body)
        {%{ctx | arena: arena}, r}
    end
  end

  defp decompose(ctx, s, t) do
    case {Terms.view(ctx.arena, s), Terms.view(ctx.arena, t)} do
      {{:rigid, head, s_args}, {:rigid, head, t_args}} when length(s_args) == length(t_args) ->
        {ctx, args} = gen_args(ctx, s_args, t_args)
        rebuild(ctx, head, args)

      {{:flex, head, s_args}, {:flex, head, t_args}} when length(s_args) == length(t_args) ->
        {ctx, args} = gen_args(ctx, Enum.map(s_args, &{&1, 0}), Enum.map(t_args, &{&1, 0}))
        {arena, r} = Terms.mk_apps(ctx.arena, head, args)
        {%{ctx | arena: arena}, r}

      _ ->
        solve(ctx, s, t)
    end
  end

  # Arguments are `{term, binders}`; only the body of `forall` sits below a binder,
  # and generalizing it there is the abstraction rule.
  defp gen_args(ctx, s_args, t_args) do
    s_args
    |> Enum.zip(t_args)
    |> Enum.map_reduce(ctx, fn {{s, _}, {t, _}}, ctx ->
      {ctx, r} = gen(ctx, s, t)
      {r, ctx}
    end)
    |> then(fn {args, ctx} -> {ctx, args} end)
  end

  defp rebuild(ctx, head, args) do
    {arena, r} =
      case {head, args} do
        {{:sym, h}, _} -> Terms.mk_apps(ctx.arena, h, args)
        {{:eq, _ty}, [l, r]} -> Arena.mk_eq(ctx.arena, l, r)
        {:not, [a]} -> Arena.mk_not(ctx.arena, a)
        {:or, [l, r]} -> Arena.mk_or(ctx.arena, l, r)
        {{:forall, dom}, [body]} -> Arena.mk_forall(ctx.arena, dom, body)
      end

    {%{ctx | arena: arena}, r}
  end

  # ---------------------------------------------------------------------------
  # Solve and merge (Leo-III `phase2`, `phase3`)
  # ---------------------------------------------------------------------------

  # `Y(ys)` for the pair `s = t`, where `ys` are the loose bound variables of `s`
  # and `t` in first-occurrence order. The pair, renamed to the binders of
  # `^ [ys]: _`, is the merge key, and its sides are the bodies of the bindings.
  defp solve(ctx, s, t) do
    ys =
      loose_bvars(ctx.arena, s, 0, [])
      |> then(&loose_bvars(ctx.arena, t, 0, &1))
      |> Enum.reverse()

    n = length(ys)
    renaming = ys |> Enum.with_index() |> Map.new(fn {{idx, _ty}, j} -> {idx, n - 1 - j} end)
    {:ok, arena, s_body} = Terms.rename_loose(ctx.arena, s, renaming)
    {:ok, arena, t_body} = Terms.rename_loose(arena, t, renaming)
    ctx = %{ctx | arena: arena}

    {ctx, var} =
      case Map.fetch(ctx.store, {s_body, t_body}) do
        {:ok, var} -> {ctx, var}
        :error -> fresh(ctx, ys, s, s_body, t_body)
      end

    {args, arena} =
      Enum.map_reduce(ys, ctx.arena, fn {idx, ty}, ar ->
        {ar, bv} = Arena.mk_bvar(ar, idx, ty)
        {bv, ar}
      end)

    {arena, r} = Terms.mk_apps(arena, var, args)
    {%{ctx | arena: arena}, r}
  end

  defp fresh(ctx, ys, s, s_body, t_body) do
    tys = Enum.map(ys, &elem(&1, 1))
    {arena, var_ty} = Terms.mk_arrows(ctx.arena, tys, Arena.type_of(ctx.arena, s))
    {arena, var} = Arena.mk_fvar(arena, ctx.next, var_ty)
    {arena, left} = binding(arena, tys, s_body)
    {arena, right} = binding(arena, tys, t_body)

    ctx = %{
      ctx
      | arena: arena,
        next: ctx.next + 1,
        store: Map.put(ctx.store, {s_body, t_body}, var),
        left: Map.put(ctx.left, ctx.next, left),
        right: Map.put(ctx.right, ctx.next, right)
    }

    {ctx, var}
  end

  defp binding(arena, tys, body) do
    {arena, lam} = Terms.mk_lams(arena, tys, body)
    Arena.beta_eta_norm(arena, lam)
  end

  # Loose bound variables `{index, type}` of `term_id` (indices relative to its
  # top), prepended to `acc` in order of first occurrence and without repetitions.
  defp loose_bvars(arena, term_id, depth, acc) do
    if Arena.has_loose_bvar?(arena, term_id, depth) do
      case Arena.get_node(arena, term_id) do
        {@tag_bvar, _, ty, idx, _} ->
          if List.keymember?(acc, idx - depth, 0), do: acc, else: [{idx - depth, ty} | acc]

        {tag, _, _, l, r} when tag in [@tag_app, @tag_eq, @tag_or] ->
          acc = loose_bvars(arena, l, depth, acc)
          loose_bvars(arena, r, depth, acc)

        {@tag_not, _, _, a, _} ->
          loose_bvars(arena, a, depth, acc)

        {tag, _, _, _, body} when tag in [@tag_lam, @tag_forall] ->
          loose_bvars(arena, body, depth + 1, acc)
      end
    else
      acc
    end
  end
end
