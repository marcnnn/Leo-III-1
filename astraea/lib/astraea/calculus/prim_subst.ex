defmodule Astraea.Calculus.PrimSubst do
  @moduledoc """
  Primitive substitution (Leo-III `PrimSubst` / `PrimSubstControl`): guesses the
  logical structure of a predicate variable in flexible head position of a literal.

  For a head variable `P: t1 > ... > tn > $o` the partial bindings of
  `Astraea.Calculus.Unify.partial_binding/4` are used as templates, by level:

    1. `^ [xs]: ~(H xs)`, `^ [xs]: (H1 xs) | (H2 xs)`, `^ [xs]: $true`, `^ [xs]: $false`
       (Leo-III's standard bindings),
    2. in addition `^ [xs]: ! [Y: t]: H xs Y` and `^ [xs]: (H1 xs) = (H2 xs)` at `t`
       for every argument type `t` of `P` and `$i`, and the projections onto
       arguments of result type `$o`,
    3. in addition `^ [x, y]: x = y` and `^ [x, y]: ~(x = y)` for two arguments of the
       same type (Leo-III `eqBindings`).

  Every result is a substitution `%{var => binding}`; applying it is an ordinary
  `:subst` kernel step and the non-atomic literals it creates are clausified by
  `Astraea.Calculus.Cnf`.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.{Terms, Unify}

  @doc """
  The flexible head variables `{var_id, type_id}` of the literals of `lits` whose
  result type is `$o`.
  """
  @spec head_vars(Arena.t(), Astraea.ProofChecker.clause()) :: [
          {non_neg_integer(), Arena.type_id()}
        ]
  def head_vars(%Arena{} = arena, lits) do
    lits
    |> Enum.flat_map(fn {_pol, atom} ->
      {head, _args} = Terms.spine(arena, atom)

      if Terms.fvar?(arena, head) do
        {_tag, _flags, ty, var, _} = Arena.get_node(arena, head)
        [{var, ty}]
      else
        []
      end
    end)
    |> Enum.uniq()
  end

  @doc """
  Template substitutions for all flexible head variables of `lits` up to `level`.
  """
  @spec substitutions(Arena.t(), Astraea.ProofChecker.clause(), non_neg_integer(), pos_integer()) ::
          {Arena.t(), non_neg_integer(), [Arena.subst()]}
  def substitutions(%Arena{} = arena, lits, next_fvar, level) do
    arena
    |> head_vars(lits)
    |> Enum.reduce({arena, next_fvar, []}, fn {var, ty}, {ar, nf, acc} ->
      {ar, nf, bindings} = bindings(ar, nf, ty, level)
      {ar, nf, acc ++ Enum.map(bindings, &%{var => &1})}
    end)
  end

  @doc "Template bindings for a variable of type `ty` up to `level`."
  @spec bindings(Arena.t(), non_neg_integer(), Arena.type_id(), pos_integer()) ::
          {Arena.t(), non_neg_integer(), [Arena.term_id()]}
  def bindings(%Arena{} = arena, next_fvar, ty, level) do
    {taus, _o} = Terms.arrow_types(arena, ty)
    {arena, truth} = Arena.mk_const(arena, "$true", :o)
    {arena, falsum} = Arena.mk_const(arena, "$false", :o)
    quant_tys = Enum.uniq(taus ++ [Arena.ty_i()])

    heads =
      [:not, :or, {:sym, truth}, {:sym, falsum}] ++
        if(level >= 2, do: level_two(arena, taus, quant_tys), else: [])

    {arena, next_fvar, bindings} =
      Enum.reduce(heads, {arena, next_fvar, []}, fn head, {ar, nf, acc} ->
        {ar, nf, b} = Unify.partial_binding(ar, nf, taus, head)
        {ar, nf, [b | acc]}
      end)

    {arena, eq_bindings} = if level >= 3, do: eq_bindings(arena, taus), else: {arena, []}
    {arena, next_fvar, Enum.reverse(bindings) ++ eq_bindings}
  end

  defp level_two(arena, taus, quant_tys) do
    projections =
      for {tau, j} <- Enum.with_index(taus),
          elem(Terms.arrow_types(arena, tau), 1) == Arena.ty_o(),
          do: {:project, j}

    Enum.map(quant_tys, &{:forall, &1}) ++ Enum.map(quant_tys, &{:eq, &1}) ++ projections
  end

  # `^ [x, y]: x = y` and its negation, for exactly two arguments of the same type.
  defp eq_bindings(arena, [tau, tau]) do
    {arena, x} = Arena.mk_bvar(arena, 1, tau)
    {arena, y} = Arena.mk_bvar(arena, 0, tau)
    {arena, eq} = Arena.mk_eq(arena, x, y)
    {arena, neq} = Arena.mk_not(arena, eq)
    {arena, b_eq} = Terms.mk_lams(arena, [tau, tau], eq)
    {arena, b_neq} = Terms.mk_lams(arena, [tau, tau], neq)
    {arena, [b_eq, b_neq]}
  end

  defp eq_bindings(arena, _taus), do: {arena, []}
end
