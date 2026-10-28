defmodule Astraea.Calculus.AC do
  @moduledoc """
  Associativity and commutativity specifications (Leo-III
  `SimplificationControl.detectAC` / `findAC`) for AC simplification
  (Leo-III `acSimp`, behind the `acsimp` flag).

  Leo-III sorts the arguments of AC symbols, a step the LCF kernel cannot check.
  Astraea gets AC normal forms from the demodulator's ordered rewriting instead:
  with `A: f (f X Y) Z = f X (f Y Z)` and `C: f X Y = f Y X` it derives
  left-commutativity `LC: f X (f Y Z) = f Y (f X Z)`, and `{A, C, LC}` is ground
  convergent under a total simplification ordering, so ordered rewriting with these
  units normalizes ground AC terms. The derivation of `LC` uses only
  `:subst`, `:symm` and `:paramod`:

      f x (f y z) = f (f x y) z      symm of A[x, y, z]
      f x (f y z) = f (f y x) z      paramod with C[x, y]
      f x (f y z) = f y (f x z)      paramod with A[y, x, z]
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_eq 6

  @doc """
  `{:comm, f, %{a:, b:}}` for `f a b = f b a`, `{:assoc, f, %{x:, y:, z:, flipped:}}`
  for `f (f x y) z = f x (f y z)` (`flipped` when the equation is stated right to
  left), else `:none`. Variables are free-variable ids.
  """
  @spec detect(Arena.t(), Astraea.ProofChecker.clause()) ::
          {:comm | :assoc, Arena.term_id(), map()} | :none
  def detect(%Arena{} = arena, lits) do
    with [{:pos, eq}] <- MapSet.to_list(lits),
         {@tag_eq, _, _, l, r} <- Arena.get_node(arena, eq) do
      comm(arena, l, r) || assoc(arena, l, r, false) || assoc(arena, r, l, true) || :none
    else
      _ -> :none
    end
  end

  defp comm(arena, l, r) do
    with {f, [a, b]} <- binary(arena, l),
         {^f, [^b, ^a]} <- binary(arena, r),
         true <- a != b and var?(arena, a) and var?(arena, b) do
      {:comm, f, %{a: var_id(arena, a), b: var_id(arena, b)}}
    else
      _ -> nil
    end
  end

  # `l = f (f x y) z`, `r = f x (f y z)`.
  defp assoc(arena, l, r, flipped) do
    with {f, [fxy, z]} <- binary(arena, l),
         {^f, [x, y]} <- binary(arena, fxy),
         {^f, [^x, fyz]} <- binary(arena, r),
         {^f, [^y, ^z]} <- binary(arena, fyz),
         true <- Enum.all?([x, y, z], &var?(arena, &1)),
         true <- length(Enum.uniq([x, y, z])) == 3 do
      {:assoc, f,
       %{x: var_id(arena, x), y: var_id(arena, y), z: var_id(arena, z), flipped: flipped}}
    else
      _ -> nil
    end
  end

  defp binary(arena, term) do
    case Terms.spine(arena, term) do
      {head, [_, _] = args} -> if Terms.symbol?(arena, head), do: {head, args}, else: nil
      _ -> nil
    end
  end

  defp var?(arena, term), do: Terms.fvar?(arena, term)

  defp var_id(arena, term), do: elem(Arena.get_node(arena, term), 3)
end
