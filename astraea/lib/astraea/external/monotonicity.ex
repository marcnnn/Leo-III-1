defmodule Astraea.External.Monotonicity do
  @moduledoc """
  Monotonicity inference for encoded first-order problems, ported from Leo-III's
  `leo.modules.encoding.Monotonicity` (`BBPS`, after Blanchette, Böhme, Popescu
  and Smallbone, "Encoding Monomorphic and Polymorphic Types").

  A sort is monotonic in a problem if every model can be extended to one where
  the sort's domain is infinite (of any larger cardinality). A sort is certainly
  monotonic if none of its variables occurs naked, i.e. as a side of an equation
  that occurs positively: adding copies of an existing element then preserves
  the truth of every formula, since all symbols treat a copy like its original
  and only positive equations between variables can tell them apart.

  Leo-III's `BBPS` works on clauses, where only positive equational literals
  count. The encoded problems also contain auxiliary formulas with nested
  connectives and quantifiers, so polarity is tracked through negation, and both
  sides of an equivalence count as positive and negative. This is conservative:
  sorts may be reported as possibly non-monotonic although they are monotonic,
  which costs guards but never soundness.
  """

  alias Astraea.Arena
  alias Astraea.External.FolEncoding

  @doc """
  Returns the type ids of the sorts with a naked variable in a positive
  equation in `formulas` (the possibly non-monotonic sorts).
  """
  @spec nonmonotonic_sorts([FolEncoding.fo_formula()]) :: MapSet.t(Arena.type_id())
  def nonmonotonic_sorts(formulas) do
    Enum.reduce(formulas, MapSet.new(), &naked(&1, :pos, &2))
  end

  @doc """
  Returns `true` if the sort `ty` is monotonic in `formulas` according to the
  naked-variable criterion.
  """
  @spec monotone?(Arena.type_id(), [FolEncoding.fo_formula()]) :: boolean()
  def monotone?(ty, formulas), do: not MapSet.member?(nonmonotonic_sorts(formulas), ty)

  defp naked(f, pol, acc) do
    case f do
      {:eq, l, r} when pol != :neg -> acc |> naked_side(l) |> naked_side(r)
      {:not, g} -> naked(g, flip(pol), acc)
      {:or, l, r} -> naked(r, pol, naked(l, pol, acc))
      {:iff, l, r} -> naked(r, :both, naked(l, :both, acc))
      {:all, _vars, g} -> naked(g, pol, acc)
      _ -> acc
    end
  end

  defp naked_side(acc, {:var, _name, ty}), do: MapSet.put(acc, ty)
  defp naked_side(acc, _term), do: acc

  defp flip(:pos), do: :neg
  defp flip(:neg), do: :pos
  defp flip(:both), do: :both
end
