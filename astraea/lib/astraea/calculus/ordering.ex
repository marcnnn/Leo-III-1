defmodule Astraea.Calculus.Ordering do
  @moduledoc """
  Literal eligibility for ordered paramodulation, resolution and factoring (Leo-III
  `OrderedParamod`, `OrderedEqFac`) on top of the Knuth-Bendix ordering
  `Astraea.Arena.kbo_compare/3`.

  Literals are compared by their atoms; on equal atoms the negative literal is the
  larger one. A literal is *eligible* if no other literal of its clause is strictly
  greater. KBO is stable under substitution, so a literal that is already smaller
  than another before unification can never become maximal after it, which makes
  this pre-unification check safe.

  Literal selection (`:select`):
    * `:none` - no selection, eligibility by maximality only,
    * `:neg_max` - if the clause has negative literals, only the heaviest one (ties
      broken by term id) is eligible, as in E's `SelectMaxLComplex` family.
  """

  alias Astraea.Arena

  @type literal :: Astraea.ProofChecker.literal()
  @type opts :: %{ordered: boolean(), select: :none | :neg_max}

  @doc "Reads `:ordered` (default `false`) and `:literal_selection` (default `:none`)."
  @spec opts(keyword()) :: opts()
  def opts(kw),
    do: %{
      ordered: Keyword.get(kw, :ordered, false),
      select: Keyword.get(kw, :literal_selection, :none)
    }

  @doc "The eligible literals of `lits`."
  @spec eligible(Arena.t(), Astraea.ProofChecker.clause(), opts()) :: MapSet.t(literal())
  def eligible(%Arena{} = arena, lits, %{select: :neg_max} = opts) do
    case Enum.filter(lits, &match?({:neg, _}, &1)) do
      [] -> eligible(arena, lits, %{opts | select: :none})
      negs -> MapSet.new([Enum.max_by(negs, fn {_, atom} -> {weight(arena, atom), atom} end)])
    end
  end

  def eligible(%Arena{} = arena, lits, %{ordered: true}) do
    lits
    |> Enum.reject(fn lit -> Enum.any?(lits, &(compare(arena, lit, &1) == :lt)) end)
    |> MapSet.new()
  end

  def eligible(%Arena{}, lits, _opts), do: MapSet.new(lits)

  @doc "Compares two literals: atoms by KBO, then negative above positive."
  @spec compare(Arena.t(), literal(), literal()) :: :gt | :lt | :eq | :inc
  def compare(%Arena{} = arena, {p1, a1}, {p2, a2}) do
    case Arena.kbo_compare(arena, a1, a2) do
      :eq -> polarity_order(p1, p2)
      other -> other
    end
  end

  defp polarity_order(same, same), do: :eq
  defp polarity_order(:neg, :pos), do: :gt
  defp polarity_order(:pos, :neg), do: :lt

  defp weight(arena, atom), do: elem(Arena.term_weight_and_vars(arena, atom), 0)
end
