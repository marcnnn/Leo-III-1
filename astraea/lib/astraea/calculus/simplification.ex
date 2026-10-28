defmodule Astraea.Calculus.Simplification do
  @moduledoc """
  Propositional simplification of `Astraea.Arena` formulas, after Leo-III's
  `Simp.normalize` (`leo.modules.procedures.Simplification`).

  `apply/2` beta-eta normalizes the term and rewrites it bottom-up with

    * `s | s -> s`, `~s | s -> $true`, `s | $true -> $true`, `s | $false -> s`
    * `~~s -> s`, `~$true -> $false`, `~$false -> $true`
    * `t = t -> $true`, and for `s: $o`: `s = $true -> s`, `s = $false -> ~s`
    * `! [x]: s -> s` if `x` does not occur in `s`

  The arena encodes `s & t` as `~(~s | ~t)`, so `s & s -> s`, `~s & s -> $false`,
  `s & $true -> s` and `s & $false -> $false` follow from the rules above.

  Every rule is an equivalence in Henkin semantics (the vacuous quantifier rule
  because TPTP types are nonempty), so the result is equivalent to the input.
  Leo-III's arithmetic rules (`$greatereq` to `$less`, canonical rationals) are not
  ported: `Astraea.Input.Arith` evaluates ground arithmetic during lowering.
  """

  alias Astraea.Arena

  # Node tags (u8) matching `Astraea.Arena`
  @tag_const 1
  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9

  @doc """
  Simplifies `term_id` exhaustively. Returns the beta-eta normal result.
  """
  @spec apply(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def apply(%Arena{} = arena, term_id) do
    {arena, norm} = Arena.beta_eta_norm(arena, term_id)
    {arena, simp} = simp(arena, norm)
    # Removing a negation below a lambda can expose an eta redex.
    Arena.beta_eta_norm(arena, simp)
  end

  @doc """
  Negation that cancels double negations and truth constants (`~~s -> s`,
  `~$true -> $false`, `~$false -> $true`).
  """
  @spec negate(Arena.t(), Arena.term_id()) :: {Arena.t(), Arena.term_id()}
  def negate(%Arena{} = arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_not, _, _, inner, _} ->
        {arena, inner}

      {@tag_const, _, _, sym, _} ->
        case Map.get(arena.symbol_names, sym) do
          "$true" -> Arena.mk_const(arena, "$false", :o)
          "$false" -> Arena.mk_const(arena, "$true", :o)
          _ -> Arena.mk_not(arena, term_id)
        end

      _ ->
        Arena.mk_not(arena, term_id)
    end
  end

  defp simp(arena, id) do
    {tag, _flags, _ty, left, right} = Arena.get_node(arena, id)

    case tag do
      @tag_app ->
        {arena, f} = simp(arena, left)
        {arena, a} = simp(arena, right)
        Arena.mk_app(arena, f, a)

      @tag_lam ->
        {arena, body} = simp(arena, right)
        Arena.mk_lam(arena, left, body)

      @tag_forall ->
        {arena, body} = simp(arena, right)

        if Arena.occurs_bvar?(arena, body, 0),
          do: Arena.mk_forall(arena, left, body),
          else: Arena.shift(arena, body, -1, 1)

      @tag_not ->
        {arena, a} = simp(arena, left)
        negate(arena, a)

      @tag_or ->
        {arena, l} = simp(arena, left)
        {arena, r} = simp(arena, right)
        simp_or(arena, l, r)

      @tag_eq ->
        {arena, l} = simp(arena, left)
        {arena, r} = simp(arena, right)
        simp_eq(arena, l, r)

      _ ->
        {arena, id}
    end
  end

  defp simp_or(arena, l, r) do
    cond do
      l == r -> {arena, l}
      truth?(arena, l, "$true") or truth?(arena, r, "$true") -> Arena.mk_const(arena, "$true", :o)
      truth?(arena, l, "$false") -> {arena, r}
      truth?(arena, r, "$false") -> {arena, l}
      complementary?(arena, l, r) -> Arena.mk_const(arena, "$true", :o)
      true -> Arena.mk_or(arena, l, r)
    end
  end

  defp simp_eq(arena, same, same), do: Arena.mk_const(arena, "$true", :o)

  defp simp_eq(arena, l, r) do
    cond do
      Arena.type_of(arena, l) != Arena.ty_o() -> Arena.mk_eq(arena, l, r)
      truth?(arena, r, "$true") -> {arena, l}
      truth?(arena, l, "$true") -> {arena, r}
      truth?(arena, r, "$false") -> negate(arena, l)
      truth?(arena, l, "$false") -> negate(arena, r)
      true -> Arena.mk_eq(arena, l, r)
    end
  end

  defp complementary?(arena, l, r) do
    match?({@tag_not, _, _, ^r, _}, Arena.get_node(arena, l)) or
      match?({@tag_not, _, _, ^l, _}, Arena.get_node(arena, r))
  end

  defp truth?(arena, id, name), do: Arena.truth_const?(arena, id, name)
end
