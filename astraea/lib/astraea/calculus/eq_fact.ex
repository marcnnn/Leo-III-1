defmodule Astraea.Calculus.EqFact do
  @moduledoc """
  Higher-Order Superposition: Equality Factoring (`EqFact`).

  Rule:
      C | s = t | s' = t'
    ────────────────────────   where sigma = mgu(s, s')
    (C | t != t' | s' = t')sigma

  In equational theorem proving and Higher-Order Superposition, Equality Factoring
  is necessary for refutational completeness of clauses containing multiple positive
  equalities.

  Soundness:
    If M |= s = t and M |= s' = t' and s = s', then by transitivity M |= t = t'.
    Therefore, if M |= ~(t != t') (i.e. M |= t = t'), then (s = t) implies (s' = t').
    Hence, (C | s = t | s' = t') |= (C | t != t' | s' = t').

  Verified in the LCF kernel by the atomic step:
      {:eq_fact, id, parent_id, eq1_id, eq2_id}
  """

  alias Astraea.Arena

  @tag_eq 6

  @doc """
  Finds candidate pairs of positive equalities in `clause_item` that can be factored.
  Returns a list of `{eq1_id, eq2_id, side1, side2, rem1, rem2}`.
  """
  @spec candidate_pairs(Arena.t(), map()) ::
          [{Arena.term_id(), Arena.term_id(), Arena.term_id(), Arena.term_id(), Arena.term_id(), Arena.term_id()}]
  def candidate_pairs(%Arena{} = arena, clause_item) do
    pos_eqs =
      Enum.flat_map(clause_item.lits, fn
        {:pos, eq_id} ->
          case Arena.get_node(arena, eq_id) do
            {@tag_eq, _, _, lhs, rhs} -> [{eq_id, lhs, rhs}]
            _ -> []
          end

        _ ->
          []
      end)

    if length(pos_eqs) < 2 do
      []
    else
      indexed = Enum.with_index(pos_eqs)

      for {{eq1_id, l1, r1}, i1} <- indexed,
          {{eq2_id, l2, r2}, i2} <- indexed,
          i1 < i2,
          {s1, s2, rem1, rem2} <- [
            {l1, l2, r1, r2},
            {l1, r2, r1, l2},
            {r1, l2, l1, r2},
            {r1, r2, l1, l2}
          ],
          Arena.type_of(arena, s1) == Arena.type_of(arena, s2) do
        {eq1_id, eq2_id, s1, s2, rem1, rem2}
      end
    end
  end
end
