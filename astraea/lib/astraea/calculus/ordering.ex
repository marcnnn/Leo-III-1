defmodule Astraea.Calculus.Ordering do
  @moduledoc """
  Literal eligibility for ordered paramodulation, resolution and factoring (Leo-III
  `OrderedParamod`, `OrderedEqFac`) on top of a term ordering: the Knuth-Bendix
  ordering `Astraea.Arena.kbo_compare/3` (`term_ordering: :kbo`, the default) or
  the computability path ordering `Astraea.Calculus.Cpo.compare/4`
  (`term_ordering: :cpo`, Leo-III's `TO_CPO_Naive`).

  Literals are compared by their atoms; on equal atoms the negative literal is the
  larger one. A literal is *eligible* if no other literal of its clause is strictly
  greater. Both orderings are stable under substitution, so a literal that is
  already smaller than another before unification can never become maximal after
  it, which makes this pre-unification check safe.

  Literal selection (`:select`):
    * `:none` - no selection, eligibility by maximality only,
    * `:neg_max` - if the clause has negative literals, only the heaviest one (ties
      broken by term id) is eligible, as in E's `SelectMaxLComplex` family.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Cpo

  @type literal :: Astraea.ProofChecker.literal()
  @type term_ordering :: :kbo | :cpo
  @type opts :: %{ordered: boolean(), select: :none | :neg_max, term_ordering: term_ordering()}

  @doc """
  Reads `:ordered` (default `false`), `:literal_selection` (default `:none`) and
  `:term_ordering` (default `:kbo`).
  """
  @spec opts(keyword()) :: opts()
  def opts(kw),
    do: %{
      ordered: Keyword.get(kw, :ordered, false),
      select: Keyword.get(kw, :literal_selection, :none),
      term_ordering: Keyword.get(kw, :term_ordering, :kbo)
    }

  @doc "The eligible literals of `lits`."
  @spec eligible(Arena.t(), Astraea.ProofChecker.clause(), opts()) :: MapSet.t(literal())
  def eligible(%Arena{} = arena, lits, %{select: :neg_max} = opts) do
    case Enum.filter(lits, &match?({:neg, _}, &1)) do
      [] -> eligible(arena, lits, %{opts | select: :none})
      negs -> MapSet.new([Enum.max_by(negs, fn {_, atom} -> {weight(arena, atom), atom} end)])
    end
  end

  def eligible(%Arena{} = arena, lits, %{ordered: true} = opts) do
    ord = term_ordering(opts)

    lits
    |> Enum.reject(fn lit -> Enum.any?(lits, &(compare(arena, lit, &1, ord) == :lt)) end)
    |> MapSet.new()
  end

  def eligible(%Arena{}, lits, _opts), do: MapSet.new(lits)

  @doc """
  Compares two literals: atoms by the term ordering (`:kbo` unless given), then
  negative above positive.
  """
  @spec compare(Arena.t(), literal(), literal(), term_ordering() | opts()) ::
          :gt | :lt | :eq | :inc
  def compare(%Arena{} = arena, {p1, a1}, {p2, a2}, ordering \\ :kbo) do
    case compare_terms(arena, a1, a2, ordering) do
      :eq -> polarity_order(p1, p2)
      other -> other
    end
  end

  @doc """
  Compares two terms by the term ordering `ordering` (`:kbo`, `:cpo`, or the
  `:term_ordering` of an `opts/1` map). This is the comparison that orients rewrite
  rules and equations.
  """
  @spec compare_terms(Arena.t(), Arena.term_id(), Arena.term_id(), term_ordering() | opts()) ::
          :gt | :lt | :eq | :inc
  def compare_terms(arena, s, t, ordering \\ :kbo)
  def compare_terms(%Arena{} = arena, s, t, :kbo), do: Arena.kbo_compare(arena, s, t)
  def compare_terms(%Arena{} = arena, s, t, :cpo), do: Cpo.compare(arena, s, t)

  def compare_terms(%Arena{} = arena, s, t, %{} = opts),
    do: compare_terms(arena, s, t, term_ordering(opts))

  defp term_ordering(opts), do: Map.get(opts, :term_ordering, :kbo)

  defp polarity_order(same, same), do: :eq
  defp polarity_order(:neg, :pos), do: :gt
  defp polarity_order(:pos, :neg), do: :lt

  defp weight(arena, atom), do: elem(Arena.term_weight_and_vars(arena, atom), 0)
end
