defmodule Astraea.Engine.Fragment do
  @moduledoc """
  Recognizes clause sets in the first-order fragment, where the calculus of
  `Astraea.Prover` (resolution, factoring, paramodulation) needs no higher-order
  rules: every literal atom is a rigid predicate application or an equation between
  first-order terms, every argument and variable has an individual (non-`$o`, non
  functional) sort, and no lambda, quantifier, connective or combinator occurs inside
  an atom. Outside this fragment a saturated clause set does not show
  satisfiability: e.g. `p a, p b, ~p (a & b)` saturates without Boolean extensionality.
  """

  alias Astraea.Arena

  @tag_const 1
  @tag_fvar 3
  @tag_app 4
  @tag_eq 6
  @tag_skolem 10

  @doc "Whether every clause of `clauses` is first-order."
  @spec first_order?(Arena.t(), Enumerable.t()) :: boolean()
  def first_order?(%Arena{} = arena, clauses) do
    Enum.all?(clauses, fn lits -> Enum.all?(lits, fn {_pol, atom} -> atom?(arena, atom) end) end)
  end

  defp atom?(arena, atom) do
    case Arena.get_node(arena, atom) do
      {@tag_eq, _, _, l, r} -> term?(arena, l) and term?(arena, r)
      _ -> application?(arena, atom)
    end
  end

  defp term?(arena, term), do: individual?(arena, term) and application?(arena, term)

  # A rigid head applied to individual arguments, or an individual variable.
  defp application?(arena, term) do
    case Arena.get_node(arena, term) do
      {@tag_app, _, _, fun, arg} -> application?(arena, fun) and term?(arena, arg)
      {tag, _, _, _, _} when tag in [@tag_const, @tag_skolem] -> true
      {@tag_fvar, _, _, _, _} -> individual?(arena, term)
      _ -> false
    end
  end

  defp individual?(arena, term) do
    match?({:base, _}, Map.get(arena.type_table, Arena.type_of(arena, term))) or
      Arena.type_of(arena, term) == Arena.ty_i()
  end
end
