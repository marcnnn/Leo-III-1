defmodule Astraea.Calculus.Miniscope do
  @moduledoc """
  Miniscoping of `Astraea.Arena` formulas: moves quantifiers as far inward as
  possible, after Leo-III's `Miniscope` (`leo.modules.calculus.NormalizationRules`)
  and `leo.modules.procedures.Miniscoping`.

  The arena has only `~`, `|` and `!` (with `s & t = ~(~s | ~t)` and
  `? [x]: s = ~(! [x]: ~s)`), so Leo-III's polarity bookkeeping for `&`, `=>` and
  `?` reduces to rewriting universal quantifiers, bottom-up:

    * `! [x]: s -> s` if `x` does not occur in `s`
    * `! [x]: (a | b) -> a | ! [x]: b` if `x` does not occur in `a` (and symmetrically)
    * `! [x]: ~(a | b) -> ~(~(! [x]: ~a) | ~(! [x]: ~b))`, i.e. `! [x]: (~a & ~b)`
      becomes `(! [x]: ~a) & (! [x]: ~b)`; under a negation this is `?` distributing
      over `|`
    * `! [x]: ! [y]: s -> ! [y]: ! [x]: s` when that lets `x` move further in

  Each rule is an equivalence (the first one because TPTP types are nonempty), so
  the result is equivalent to the input. Unlike Leo-III, which keeps a quantifier
  prefix and stops at the first quantifier it cannot push, adjacent universal
  quantifiers are swapped once to let an inner one past; the result can only have
  smaller quantifier scopes. Polarity is not needed because existential quantifiers
  are negated universals here.
  """

  import Bitwise

  alias Astraea.Arena
  alias Astraea.Calculus.Simplification

  # Node tags (u8) matching `Astraea.Arena`
  @tag_bvar 2
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @flag_has_bvar 0x01

  @doc """
  Miniscopes `term_id`, a beta-eta normal term. Quantifiers below lambdas and
  inside arguments are miniscoped too.
  """
  @spec apply(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def apply(%Arena{} = arena, term_id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, term_id)

    case tag do
      @tag_forall ->
        {arena, body} = __MODULE__.apply(arena, right)
        push(arena, left, body, true)

      @tag_not ->
        {arena, a} = __MODULE__.apply(arena, left)
        Simplification.negate(arena, a)

      @tag_lam ->
        {arena, body} = __MODULE__.apply(arena, right)
        Arena.mk_lam(arena, left, body)

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        {arena, l} = __MODULE__.apply(arena, left)
        {arena, r} = __MODULE__.apply(arena, right)
        rebuild(arena, t, l, r)

      _ ->
        {arena, term_id}
    end
  end

  # `push(ty, body, swap?)` returns a term equivalent to `! [x: ty]: body`, where
  # `body` is miniscoped and `x` is its de Bruijn index 0. Recursive calls are on
  # strictly smaller bodies, except the single call made after a swap, which may
  # not swap again; hence termination.
  defp push(arena, ty, body, swap?) do
    if not Arena.occurs_bvar?(arena, body, 0) do
      Arena.shift(arena, body, -1, 1)
    else
      case Arena.get_node(arena, body) do
        {@tag_or, _, _, a, b} ->
          cond do
            not Arena.occurs_bvar?(arena, a, 0) ->
              {arena, a} = Arena.shift(arena, a, -1, 1)
              {arena, b} = push(arena, ty, b, swap?)
              Arena.mk_or(arena, a, b)

            not Arena.occurs_bvar?(arena, b, 0) ->
              {arena, a} = push(arena, ty, a, swap?)
              {arena, b} = Arena.shift(arena, b, -1, 1)
              Arena.mk_or(arena, a, b)

            true ->
              Arena.mk_forall(arena, ty, body)
          end

        {@tag_not, _, _, inner, _} ->
          case Arena.get_node(arena, inner) do
            {@tag_or, _, _, a, b} -> push_conjunction(arena, ty, a, b, swap?)
            _ -> Arena.mk_forall(arena, ty, body)
          end

        {@tag_forall, _, _, inner_ty, inner} when swap? ->
          swap(arena, ty, inner_ty, inner, body)

        _ ->
          Arena.mk_forall(arena, ty, body)
      end
    end
  end

  # `! [x]: (~a & ~b)` where the conjunction is `~(a | b)`.
  defp push_conjunction(arena, ty, a, b, swap?) do
    {arena, na} = Simplification.negate(arena, a)
    {arena, nb} = Simplification.negate(arena, b)
    {arena, qa} = push(arena, ty, na, swap?)
    {arena, qb} = push(arena, ty, nb, swap?)
    {arena, nqa} = Simplification.negate(arena, qa)
    {arena, nqb} = Simplification.negate(arena, qb)
    {arena, disj} = Arena.mk_or(arena, nqa, nqb)
    Simplification.negate(arena, disj)
  end

  # `! [x]: ! [y]: s` where pushing `y` already failed: try `! [y]: ! [x]: s'`.
  defp swap(arena, x_ty, y_ty, inner, body) do
    {arena, swapped} = swap01(arena, inner, 0)
    {arena, unchanged} = Arena.mk_forall(arena, x_ty, swapped)
    {arena, pushed} = push(arena, x_ty, swapped, true)

    if pushed == unchanged do
      Arena.mk_forall(arena, x_ty, body)
    else
      push(arena, y_ty, pushed, false)
    end
  end

  # Exchanges the de Bruijn indices `depth` and `depth + 1`.
  defp swap01(arena, id, depth) do
    {tag, flags, ty, left, right} = Arena.get_node(arena, id)

    if band(flags, @flag_has_bvar) == 0 do
      {arena, id}
    else
      case tag do
        @tag_bvar ->
          cond do
            left == depth -> Arena.mk_bvar(arena, depth + 1, ty)
            left == depth + 1 -> Arena.mk_bvar(arena, depth, ty)
            true -> {arena, id}
          end

        @tag_not ->
          {arena, a} = swap01(arena, left, depth)
          Arena.mk_not(arena, a)

        @tag_lam ->
          {arena, b} = swap01(arena, right, depth + 1)
          Arena.mk_lam(arena, left, b)

        @tag_forall ->
          {arena, b} = swap01(arena, right, depth + 1)
          Arena.mk_forall(arena, left, b)

        t when t in [@tag_app, @tag_eq, @tag_or] ->
          {arena, l} = swap01(arena, left, depth)
          {arena, r} = swap01(arena, right, depth)
          rebuild(arena, t, l, r)

        _ ->
          {arena, id}
      end
    end
  end

  defp rebuild(arena, @tag_app, l, r), do: Arena.mk_app(arena, l, r)
  defp rebuild(arena, @tag_eq, l, r), do: Arena.mk_eq(arena, l, r)
  defp rebuild(arena, @tag_or, l, r), do: Arena.mk_or(arena, l, r)
end
