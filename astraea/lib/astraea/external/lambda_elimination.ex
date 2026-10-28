defmodule Astraea.External.LambdaElimination do
  @moduledoc """
  Lambda and Boolean elimination for `Astraea.External.FolEncoding`, ported from
  Leo-III's `leo.modules.encoding.LambdaElimination`.

  Works on an intermediate representation of higher-order terms with named
  variables, built by `Astraea.External.FolEncoding` from arena nodes:

    * `{:sym, key, type}` - constant; `key` is `{:user, name}`, `{:skolem, hash}`,
      `{:lift, k}`, `{:comb, :s | :k | :i | :b | :c}` or `{:proxy, op}`
    * `{:var, name, type}` - clause variable `{:v, id}`, binder `{:b, depth}`, or
      axiom variable `{:a, n}`
    * `{:app, fun, arg, type}`, `{:lam, name, domain, body, type}`
    * `{:bool, formula}` - a formula in term position (Boolean lifting only)

  and formulas `true`, `false`, `{:atom, term}`, `{:not, f}`, `{:or, f, g}`,
  `{:iff, f, g}`, `{:eq, s, t}` (term equality; at type `$o` an equation between
  `astraea_bool` terms) and `{:forall, name, type, f}`.

  Strategies (the `:lambda` encoding option):
    * `:lambda_lifting` - Leo-III's `LambdaElim_LambdaLifting`: a maximal lambda
      prefix `^[X1..Xn]: t` with free variables `Y1..Ym` becomes `f(Y1..Ym)` for a
      fresh `f`, defined by `! [Ys, Xs]: f(Ys) @ X1 ... @ Xn = t'`. Identical
      abstractions share one symbol, and eta redexes `^[X]: u @ X` are contracted
      to `u` instead of being lifted (a TODO in Leo-III).
    * `:ski` - Leo-III's `LambdaElim_SKI`: bottom-up bracket abstraction with eta
      contraction and Turner's `B`/`C` optimizations; each combinator is a constant
      per type instance with its defining equation (Leo-III `axiomOf`).

  With `booleans: :lift`, each `{:bool, formula}` leaf becomes a fresh symbol `f`
  over its free variables, defined by `! [Ys]: (astraea_holds(f(Ys)) <=> formula)`.
  """

  alias Astraea.Arena

  @comb_arity %{i: 1, k: 2, s: 3, b: 3, c: 3}

  @doc false
  def new(%Arena{} = arena, enc) do
    %{arena: arena, enc: enc, cache: %{}, defs: [], lift_arity: %{}, next_lift: 0}
  end

  @doc false
  def definitions(st), do: {Enum.reverse(st.defs), st}

  # ---------------------------------------------------------------------------
  # Term helpers
  # ---------------------------------------------------------------------------

  @doc false
  def type_of({:sym, _key, ty}), do: ty
  def type_of({:var, _x, ty}), do: ty
  def type_of({:app, _f, _a, ty}), do: ty
  def type_of({:lam, _x, _dom, _body, ty}), do: ty
  def type_of({:bool, _f}), do: Arena.ty_o()

  @doc "Splits a term into its head and argument list."
  def spine(t), do: spine(t, [])

  defp spine({:app, f, a, _ty}, args), do: spine(f, [a | args])
  defp spine(head, args), do: {head, args}

  @doc false
  def arrow(st, doms, cod) do
    {arena, ty} =
      List.foldr(doms, {st.arena, cod}, fn dom, {arena, acc} ->
        Arena.intern_type(arena, {:arrow, dom, acc})
      end)

    {ty, %{st | arena: arena}}
  end

  @doc false
  def apply_args(st, fun, args) do
    t =
      Enum.reduce(args, fun, fn arg, f ->
        {:arrow, _dom, cod} = Map.fetch!(st.arena.type_table, type_of(f))
        {:app, f, arg, cod}
      end)

    {t, st}
  end

  @doc false
  def proxy(st, op) do
    o = Arena.ty_o()

    {ty, st} =
      case op do
        b when is_boolean(b) -> {o, st}
        :not -> arrow(st, [o], o)
        :or -> arrow(st, [o, o], o)
        {:eq, ty} -> arrow(st, [ty, ty], o)
        {:forall, ty} -> arrow(st, [ty], o) |> then(fn {p, st} -> arrow(st, [p], o) end)
      end

    {{:sym, {:proxy, op}, ty}, st}
  end

  defp free_vars(t) do
    case t do
      {:var, x, ty} -> MapSet.new([{x, ty}])
      {:sym, _, _} -> MapSet.new()
      {:app, f, a, _} -> MapSet.union(free_vars(f), free_vars(a))
      {:lam, x, dom, body, _} -> MapSet.delete(free_vars(body), {x, dom})
      {:bool, f} -> formula_free_vars(f)
    end
  end

  defp formula_free_vars(f) do
    case f do
      b when is_boolean(b) -> MapSet.new()
      {:atom, t} -> free_vars(t)
      {:not, g} -> formula_free_vars(g)
      {:forall, x, ty, g} -> MapSet.delete(formula_free_vars(g), {x, ty})
      {:eq, l, r} -> MapSet.union(free_vars(l), free_vars(r))
      {_op, l, r} -> MapSet.union(formula_free_vars(l), formula_free_vars(r))
    end
  end

  defp occurs?(x, t) do
    case t do
      {:var, y, _} -> x == y
      {:sym, _, _} -> false
      {:app, f, a, _} -> occurs?(x, f) or occurs?(x, a)
    end
  end

  defp close(vars, body) do
    List.foldr(vars, body, fn {x, ty}, acc -> {:forall, x, ty, acc} end)
  end

  defp vars(vs), do: Enum.map(vs, fn {x, ty} -> {:var, x, ty} end)

  # ---------------------------------------------------------------------------
  # Elimination
  # ---------------------------------------------------------------------------

  @doc "Eliminates lambdas and Boolean terms in a formula."
  def eliminate_formula(st, f) do
    case f do
      b when is_boolean(b) ->
        {b, st}

      {:atom, t} ->
        {t, st} = eliminate(st, t)
        {{:atom, t}, st}

      {:eq, l, r} ->
        {l, st} = eliminate(st, l)
        {r, st} = eliminate(st, r)
        {{:eq, l, r}, st}

      {:not, g} ->
        {g, st} = eliminate_formula(st, g)
        {{:not, g}, st}

      {:forall, x, ty, g} ->
        {g, st} = eliminate_formula(st, g)
        {{:forall, x, ty, g}, st}

      {op, l, r} ->
        {l, st} = eliminate_formula(st, l)
        {r, st} = eliminate_formula(st, r)
        {{op, l, r}, st}
    end
  end

  @doc "Eliminates lambdas and Boolean terms in a term."
  def eliminate(st, t) do
    case t do
      {:app, f, a, ty} ->
        {f, st} = eliminate(st, f)
        {a, st} = eliminate(st, a)
        {{:app, f, a, ty}, st}

      {:lam, x, dom, body, _ty} ->
        cond do
          st.enc[:lambda] == :ski ->
            {body, st} = eliminate(st, body)
            abstract(st, {x, dom}, body)

          eta_redex?(t) ->
            {:app, u, _x, _} = body
            eliminate(st, u)

          true ->
            cached(st, t, &lift_lambda/2)
        end

      {:bool, _f} ->
        cached(st, t, &lift_boolean/2)

      _sym_or_var ->
        {t, st}
    end
  end

  # ^[X]: u @ X with X not free in u (Henkin models are extensional, so this is u).
  defp eta_redex?({:lam, x, _dom, {:app, u, {:var, x, _}, _}, _ty}),
    do: not Enum.any?(free_vars(u), &(elem(&1, 0) == x))

  defp eta_redex?(_lam), do: false

  defp cached(st, t, fun) do
    case Map.fetch(st.cache, t) do
      {:ok, replacement} ->
        {replacement, st}

      :error ->
        {replacement, st} = fun.(st, t)
        {replacement, %{st | cache: Map.put(st.cache, t, replacement)}}
    end
  end

  # ^[X1..Xn]: body  ~>  f(Ys), with ! [Ys, Xs]: f(Ys) @ X1 ... @ Xn = body'
  defp lift_lambda(st, lam) do
    {xs, body} = collect_lambdas(lam, [])
    fvs = lam |> free_vars() |> Enum.sort()
    {head, st} = fresh_symbol(st, fvs, type_of(lam))
    {lhs, st} = apply_args(st, head, vars(xs))

    {eq, st} =
      case body do
        {:bool, f} ->
          {f, st} = eliminate_formula(st, f)
          {{:iff, {:atom, lhs}, f}, st}

        _ ->
          {rhs, st} = eliminate(st, body)

          if type_of(rhs) == Arena.ty_o() and st.enc[:booleans] == :lift,
            do: {{:iff, {:atom, lhs}, {:atom, rhs}}, st},
            else: {{:eq, lhs, rhs}, st}
      end

    {head, %{st | defs: [close(fvs ++ xs, eq) | st.defs]}}
  end

  defp collect_lambdas({:lam, x, dom, body, _ty}, acc),
    do: collect_lambdas(body, [{x, dom} | acc])

  defp collect_lambdas(body, acc), do: {Enum.reverse(acc), body}

  # formula in term position  ~>  f(Ys), with ! [Ys]: (astraea_holds(f(Ys)) <=> formula')
  defp lift_boolean(st, {:bool, f} = t) do
    fvs = t |> free_vars() |> Enum.sort()
    {head, st} = fresh_symbol(st, fvs, Arena.ty_o())
    {f, st} = eliminate_formula(st, f)
    {head, %{st | defs: [close(fvs, {:iff, {:atom, head}, f}) | st.defs]}}
  end

  # A fresh symbol `astraea_lift_<k>` of type `fv types > ty`, applied to the free variables.
  defp fresh_symbol(st, fvs, ty) do
    k = st.next_lift
    {full_ty, st} = arrow(st, Enum.map(fvs, &elem(&1, 1)), ty)
    key = {:lift, k}

    st = %{
      st
      | next_lift: k + 1,
        lift_arity: Map.put(st.lift_arity, key, {full_ty, length(fvs)})
    }

    apply_args(st, {:sym, key, full_ty}, vars(fvs))
  end

  # Bracket abstraction [x]t of a lambda-free term `t` (Leo-III `eliminateLambdaNewShallow`).
  defp abstract(st, {x, x_ty}, t) do
    cond do
      match?({:var, ^x, _}, t) ->
        comb(st, :i, [x_ty], x_ty, [])

      not occurs?(x, t) ->
        comb(st, :k, [type_of(t), x_ty], type_of(t), [t])

      true ->
        {:app, u, v, c} = t
        b = type_of(v)

        cond do
          not occurs?(x, u) and match?({:var, ^x, _}, v) ->
            {u, st}

          not occurs?(x, u) ->
            # B u [x]v : (b > c) > (a > b) > a > c
            {u_ty, st} = arrow(st, [b], c)
            {xv_ty, st} = arrow(st, [x_ty], b)
            {xv, st} = abstract(st, {x, x_ty}, v)
            comb(st, :b, [u_ty, xv_ty, x_ty], c, [u, xv])

          not occurs?(x, v) ->
            # C [x]u v : (a > b > c) > b > a > c
            {xu, st} = abstract(st, {x, x_ty}, u)
            comb(st, :c, [type_of(xu), b, x_ty], c, [xu, v])

          true ->
            # S [x]u [x]v : (a > b > c) > (a > b) > a > c
            {xu, st} = abstract(st, {x, x_ty}, u)
            {xv, st} = abstract(st, {x, x_ty}, v)
            comb(st, :s, [type_of(xu), type_of(xv), x_ty], c, [xu, xv])
        end
    end
  end

  defp comb(st, c, param_tys, res_ty, args) do
    {ty, st} = arrow(st, param_tys, res_ty)
    apply_args(st, {:sym, {:comb, c}, ty}, args)
  end

  # ---------------------------------------------------------------------------
  # Auxiliary axioms
  # ---------------------------------------------------------------------------

  @doc """
  Returns the defining axioms of the combinator and proxy symbols occurring in
  `formulas` (Leo-III `axiomOf` and `proxyAxiomOf`).
  """
  def symbol_axioms(st, formulas) do
    syms =
      formulas
      |> Enum.reduce(MapSet.new(), &formula_syms/2)
      |> Enum.filter(fn {key, _ty} -> match?({:comb, _}, key) or match?({:proxy, _}, key) end)
      |> Enum.sort()

    Enum.map_reduce(syms, st, fn {key, ty}, st -> axiom(st, key, ty) end)
  end

  defp formula_syms(f, acc) do
    case f do
      b when is_boolean(b) -> acc
      {:atom, t} -> term_syms(t, acc)
      {:eq, l, r} -> term_syms(r, term_syms(l, acc))
      {:not, g} -> formula_syms(g, acc)
      {:forall, _x, _ty, g} -> formula_syms(g, acc)
      {_op, l, r} -> formula_syms(r, formula_syms(l, acc))
    end
  end

  defp term_syms(t, acc) do
    case t do
      {:sym, key, ty} -> MapSet.put(acc, {key, ty})
      {:app, f, a, _} -> term_syms(a, term_syms(f, acc))
      _ -> acc
    end
  end

  defp axiom(st, {:comb, c} = key, ty) do
    n = Map.fetch!(@comb_arity, c)
    xs = axiom_vars(st, ty, n)
    {lhs, st} = apply_args(st, {:sym, key, ty}, vars(xs))
    [x, y, z] = vars(xs) ++ List.duplicate(nil, 3 - n)

    {rhs, st} =
      case c do
        i_or_k when i_or_k in [:i, :k] ->
          {x, st}

        :s ->
          {xz, st} = apply_args(st, x, [z])
          {yz, st} = apply_args(st, y, [z])
          apply_args(st, xz, [yz])

        :b ->
          {yz, st} = apply_args(st, y, [z])
          apply_args(st, x, [yz])

        :c ->
          apply_args(st, x, [z, y])
      end

    {close(xs, {:eq, lhs, rhs}), st}
  end

  defp axiom(st, {:proxy, op} = key, ty) do
    o = Arena.ty_o()
    sym = {:sym, key, ty}

    case op do
      true ->
        {{:atom, sym}, st}

      false ->
        {{:not, {:atom, sym}}, st}

      :not ->
        [a] = xs = [{{:a, 0}, o}]
        {lhs, st} = apply_args(st, sym, vars(xs))
        {close(xs, {:iff, {:atom, lhs}, {:not, atom_of(a)}}), st}

      :or ->
        [a, b] = xs = [{{:a, 0}, o}, {{:a, 1}, o}]
        {lhs, st} = apply_args(st, sym, vars(xs))
        {close(xs, {:iff, {:atom, lhs}, {:or, atom_of(a), atom_of(b)}}), st}

      {:eq, arg_ty} ->
        [a, b] = xs = [{{:a, 0}, arg_ty}, {{:a, 1}, arg_ty}]
        {lhs, st} = apply_args(st, sym, vars(xs))

        rhs =
          if arg_ty == o,
            do: {:iff, atom_of(a), atom_of(b)},
            else: {:eq, {:var, {:a, 0}, arg_ty}, {:var, {:a, 1}, arg_ty}}

        {close(xs, {:iff, {:atom, lhs}, rhs}), st}

      {:forall, arg_ty} ->
        {p_ty, st} = arrow(st, [arg_ty], o)
        p = {:var, {:a, 0}, p_ty}
        {lhs, st} = apply_args(st, sym, [p])
        {px, st} = apply_args(st, p, [{:var, {:a, 1}, arg_ty}])
        rhs = {:forall, {:a, 1}, arg_ty, {:atom, px}}
        {close([{{:a, 0}, p_ty}], {:iff, {:atom, lhs}, rhs}), st}
    end
  end

  defp atom_of({x, ty}), do: {:atom, {:var, x, ty}}

  defp axiom_vars(st, ty, n) do
    {vs, _ty} =
      Enum.map_reduce(0..(n - 1), ty, fn i, ty ->
        {:arrow, dom, cod} = Map.fetch!(st.arena.type_table, ty)
        {{{:a, i}, dom}, cod}
      end)

    vs
  end
end
