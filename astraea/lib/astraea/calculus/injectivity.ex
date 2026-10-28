defmodule Astraea.Calculus.Injectivity do
  @moduledoc """
  Injective functions and their inverses (Leo-III `Control.detectInjectivity` and
  `InverseFunction`).

  A clause `f X1 ... Xn != f Y1 ... Yn | Xi = Yi` (all arguments variables) states
  that `f` is injective in argument `i`. Leo-III then adds the axiom
  `?[G]: ![X1 ... Xn]: G(X1, ..., X(i-1), X(i+1), ..., Xn, f X1 ... Xn) = Xi` and
  Skolemizes `G`. Astraea derives the same fact with existing kernel rules
  instead, with the inverse given by Hilbert choice,
  `G = ^[.., y]: $choice @ (^[x]: f Z1 .. x .. Zn = y)`:

    1. `{:choice}` with `P = ^[x]: f Z1 .. x .. Zn = f Z1 .. Zi .. Zn` and witness
       `Zi`: `~(f Z = f Z) | f Z1 .. e .. Zn = f Z`, where `e = $choice @ P`
    2. `{:refl}` on `f Z` and `{:resolve}`: `f Z1 .. e .. Zn = f Z`
    3. `{:subst}` of the injectivity clause (`Xj := Zj` except `Xi := e`,
       `Yj := Zj`) and `{:resolve}`: `e = Zi`

  The result `$choice @ (^[x]: f Z1 .. x .. Zn = f Z) = Zi` is the beta-normal
  form of Leo-III's `G(.., f Z) = Zi`, so the lemma needs no trusted axiom.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_eq 6

  @type info :: %{
          head: Arena.term_id(),
          index: non_neg_integer(),
          left_args: [Arena.term_id()],
          right_args: [Arena.term_id()],
          pos_atom: Arena.term_id(),
          neg_atom: Arena.term_id()
        }

  @doc "`{:ok, info}` if `lits` is an injectivity clause, else `:none`."
  @spec detect(Arena.t(), Astraea.ProofChecker.clause()) :: {:ok, info()} | :none
  def detect(%Arena{} = arena, lits) do
    with [{:neg, neg_atom}, {:pos, pos_atom}] <- Enum.sort_by(lits, &(elem(&1, 0) == :pos)),
         {@tag_eq, _, _, nl, nr} <- Arena.get_node(arena, neg_atom),
         {@tag_eq, _, _, pl, pr} <- Arena.get_node(arena, pos_atom),
         true <- Terms.fvar?(arena, pl) and Terms.fvar?(arena, pr),
         {head, left_args} <- Terms.spine(arena, nl),
         {^head, right_args} <- Terms.spine(arena, nr),
         true <- Terms.symbol?(arena, head),
         true <- left_args != [] and length(left_args) == length(right_args),
         true <- Enum.all?(left_args ++ right_args, &Terms.fvar?(arena, &1)),
         index when is_integer(index) <- injective_index(left_args, right_args, pl, pr) do
      {:ok,
       %{
         head: head,
         index: index,
         left_args: left_args,
         right_args: right_args,
         pos_atom: pos_atom,
         neg_atom: neg_atom
       }}
    else
      _ -> :none
    end
  end

  defp injective_index(left_args, right_args, pl, pr) do
    pairs = Enum.zip(left_args, right_args)

    Enum.find_index(pairs, &(&1 == {pl, pr})) || Enum.find_index(pairs, &(&1 == {pr, pl}))
  end

  @doc """
  The inverse function as a closed term,
  `G = ^[U1 .. U(n-1), y]: $choice @ (^[x]: f U1 .. x .. U(n-1) = y)` (Leo-III's
  Skolem `G` with the other arguments first). Leo-III's `G` is a symbol that
  unification can bind to a variable directly; the prover offers this term as an
  instance for variables of its type instead.
  """
  @spec inverse_term(Arena.t(), info()) :: {Arena.t(), Arena.term_id()}
  def inverse_term(%Arena{} = arena, info) do
    tys = Enum.map(info.left_args, &Arena.type_of(arena, &1))
    {ti, others} = List.pop_at(tys, info.index)
    {arena, fx_any} = Terms.mk_apps(arena, info.head, info.left_args)
    prefix = others ++ [Arena.type_of(arena, fx_any)]

    {arena, bound} = Terms.bound_args(arena, prefix, 1)
    {us, [y]} = Enum.split(bound, length(others))
    {arena, x} = Arena.mk_bvar(arena, 0, ti)
    {arena, fx} = Terms.mk_apps(arena, info.head, List.insert_at(us, info.index, x))
    {arena, body} = Arena.mk_eq(arena, fx, y)
    {arena, pred} = Arena.mk_lam(arena, ti, body)
    {arena, eps} = Arena.mk_const(arena, "$choice", {:arrow, Arena.type_of(arena, pred), ti})
    {arena, e} = Arena.mk_app(arena, eps, pred)
    {arena, inv} = Terms.mk_lams(arena, prefix, e)
    Arena.beta_eta_norm(arena, inv)
  end

  @doc """
  The predicate `P = ^[x]: f Z1 .. x .. Zn = f Z1 .. Zn` for the fresh variables
  `zs` (one per argument of `f`) and the substitution of the injectivity clause
  that turns its negative literal into `f Z1 .. e .. Zn != f Z1 .. Zn` with
  `e = $choice @ P`. Returns `:error` when the clause shares variables between
  argument positions in a way the substitution cannot respect.
  """
  @spec inverse_parts(Arena.t(), info(), [Arena.term_id()]) ::
          {:ok, Arena.t(), %{pred: Arena.term_id(), fz: Arena.term_id(), subst: Arena.subst()}}
          | :error
  def inverse_parts(%Arena{} = arena, info, zs) do
    zi = Enum.at(zs, info.index)
    ti = Arena.type_of(arena, zi)
    {arena, x} = Arena.mk_bvar(arena, 0, ti)
    {arena, fz} = Terms.mk_apps(arena, info.head, zs)
    {arena, fx} = Terms.mk_apps(arena, info.head, List.replace_at(zs, info.index, x))
    {arena, body} = Arena.mk_eq(arena, fx, fz)
    {arena, pred} = Arena.mk_lam(arena, ti, body)

    {arena, eps} = Arena.mk_const(arena, "$choice", {:arrow, Arena.type_of(arena, pred), ti})
    {arena, e} = Arena.mk_app(arena, eps, pred)
    left_targets = List.replace_at(zs, info.index, e)

    pairs = Enum.zip(info.left_args, left_targets) ++ Enum.zip(info.right_args, zs)

    subst =
      Enum.reduce_while(pairs, %{}, fn {var, target}, acc ->
        {_, _, _, var_id, _} = Arena.get_node(arena, var)

        case Map.fetch(acc, var_id) do
          :error -> {:cont, Map.put(acc, var_id, target)}
          {:ok, ^target} -> {:cont, acc}
          {:ok, _other} -> {:halt, :error}
        end
      end)

    if subst == :error, do: :error, else: {:ok, arena, %{pred: pred, fz: fz, subst: subst}}
  end
end
