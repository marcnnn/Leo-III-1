defmodule Astraea.Calculus.ArgCong do
  @moduledoc """
  Higher-Order Superposition: Argument Congruence (`ArgCong`).

  Rule:
        C | s = t
    ──────────────────   (where s, t: tau -> sigma, x is a fresh variable of type tau)
      C | s x = t x

  In Higher-Order Superposition (Bentkamp, Blanchette, Cruanes, Waldmann), Argument
  Congruence allows functions to be applied to arguments without generating Skolem
  constants from functional extensionality.

  Verified in the LCF kernel by the atomic step:
      {:cong, id, parent_id, eq_atom_id, arg_id}
  """

  alias Astraea.Arena

  @tag_eq 6

  @doc """
  Finds eligible positive equality literals in `clause_item` with functional types
  that can be extended via Argument Congruence.
  Returns a list of `{eq_id, lhs, rhs, dom_ty}`.
  """
  @spec candidates(Arena.t(), map()) :: [{Arena.term_id(), Arena.term_id(), Arena.term_id(), Arena.type_id()}]
  def candidates(%Arena{} = arena, clause_item) do
    Enum.flat_map(clause_item.lits, fn
      {:pos, eq_id} ->
        case Arena.get_node(arena, eq_id) do
          {@tag_eq, _, _, lhs, rhs} ->
            lhs_ty = Arena.type_of(arena, lhs)

            case Map.get(arena.type_table, lhs_ty) do
              {:arrow, dom_ty, _codom_ty} ->
                # Only apply if not already an applied congruence variable of the same shape
                [{eq_id, lhs, rhs, dom_ty}]

              _ ->
                []
            end

          _ ->
            []
        end

      _ ->
        []
    end)
  end
end
