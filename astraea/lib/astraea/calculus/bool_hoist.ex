defmodule Astraea.Calculus.BoolHoist do
  @moduledoc """
  Boolean hoisting (E `fool_unroll`, Zipperposition `BoolHoist`).

  A formula `phi` occurring as an argument of a literal is split by cases:

          C | L[phi]
    ─────────────────────────────────────────
     C | L[$true] | ~phi     C | L[$false] | phi

  Both conclusions are derived from existing kernel steps: `{:refl}` and
  `{:cnf, {:bool_eq, :left}}` give the tautology `~phi | phi`, `:lift_bool` turns it
  into `~phi | phi = $true` (or `phi | phi = $false`), and `:paramod` with that
  equation rewrites `L[phi]`.

  Candidates are the outermost Boolean subterms strictly below the atom that are not
  under a binder and neither a truth constant, a free variable nor an equation
  (`:lift_bool` does not apply to equations). Sides of Boolean equations are skipped
  as such (BoolExt handles them), but searched below.
  """

  alias Astraea.Arena
  alias Astraea.Calculus.Terms

  @tag_eq 6

  @doc "Distinct `{literal, phi}` pairs of `lits` to hoist."
  @spec candidates(Arena.t(), Astraea.ProofChecker.clause()) ::
          [{Astraea.ProofChecker.literal(), Arena.term_id()}]
  def candidates(%Arena{} = arena, lits) do
    for {_pol, atom} = lit <- lits,
        phi <- below(arena, atom, 0, MapSet.new()),
        do: {lit, phi}
  end

  # Outermost candidates strictly below `term_id`; `bound` counts crossed binders.
  defp below(arena, term_id, bound, acc) do
    bool_eq? = bool_eq?(arena, term_id)

    case Terms.view(arena, term_id) do
      {:rigid, _head, children} -> children
      {:flex, _f, args} -> Enum.map(args, &{&1, 0})
      {:lam, _dom, body} -> [{body, 1}]
    end
    |> Enum.reduce(acc, fn {c, b}, acc ->
      if not bool_eq? and bound + b == 0 and hoistable?(arena, c),
        do: MapSet.put(acc, c),
        else: below(arena, c, bound + b, acc)
    end)
  end

  defp hoistable?(arena, term_id) do
    Arena.type_of(arena, term_id) == Arena.ty_o() and
      not Arena.has_loose_bvar?(arena, term_id, 0) and
      not Terms.fvar?(arena, term_id) and
      not match?({@tag_eq, _, _, _, _}, Arena.get_node(arena, term_id)) and
      not Terms.const_named?(arena, term_id, "$true") and
      not Terms.const_named?(arena, term_id, "$false")
  end

  defp bool_eq?(arena, term_id) do
    case Arena.get_node(arena, term_id) do
      {@tag_eq, _, _, l, _r} -> Arena.type_of(arena, l) == Arena.ty_o()
      _ -> false
    end
  end
end
