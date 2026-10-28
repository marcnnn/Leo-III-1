defmodule Astraea.Calculus.Induction do
  @moduledoc """
  Goal-directed instantiation of induction principles (Pillar 4 of
  `Notes/beating_zipperposition_plan.md`, restricted to what is sound in THF).

  THF has no datatypes: a signature with `0` and `s` does not make `$i` inductive,
  so the prover may not assume an induction schema for it (a model can contain
  non-standard elements, and asserting the schema would turn CounterSatisfiable
  problems into "theorems"). Induction is only available when the problem states
  it, typically as a higher-order axiom

      ! [P: nat > $o]: ((P @ zero) & (! [N: nat]: ((P @ N) => (P @ (succ @ N)))))
                       => (! [N: nat]: (P @ N))

  whose clauses contain the free predicate variable `P`. Pre-unification rarely
  finds the instance that proves the goal: the goal itself, abstracted over the
  constant the conjecture talks about. This module supplies exactly those
  instances. A ground clause `C[c]` with a Skolem constant `c: tau` (the negated
  conjecture `~ G(c)`, or one of its clauses) yields the goal

      ^ [X: tau]: ~ C[X]

  which is offered for every free variable of type `tau > $o`. The instantiation is
  a kernel `:subst` step, so no assumption is added and the kernel is unchanged.
  """

  alias Astraea.Arena

  @tag_app 4
  @tag_lam 5
  @tag_eq 6
  @tag_not 7
  @tag_or 8
  @tag_forall 9
  @tag_skolem 10

  # Goals per problem; each one is tried on every matching variable.
  @max_goals 6

  @doc """
  Goal abstractions `{tau, ^ [X: tau]: ~ C[X]}` from the ground clauses among
  `clauses` that contain a Skolem constant of a non-functional type.
  """
  @spec goals(Arena.t(), [MapSet.t()]) :: {Arena.t(), [{Arena.type_id(), Arena.term_id()}]}
  def goals(%Arena{} = arena, clauses) do
    {goals, arena} =
      clauses
      |> Enum.filter(&ground?(arena, &1))
      |> Enum.flat_map_reduce(arena, fn lits, ar ->
        lits
        |> Enum.flat_map(fn {_pol, atom} -> skolem_constants(ar, atom) end)
        |> Enum.uniq()
        |> Enum.map_reduce(ar, fn c, ar -> goal(ar, lits, c) end)
      end)

    {arena, goals |> Enum.uniq() |> Enum.take(@max_goals)}
  end

  defp goal(arena, lits, c) do
    {arena, negated} = negated_clause(arena, Enum.sort(lits))
    {arena, body} = Arena.abstract_subterm(arena, negated, c)
    ty = Arena.type_of(arena, c)
    {arena, lam} = Arena.mk_lam(arena, ty, body)
    {{ty, lam}, arena}
  end

  # `~ (L1 | ... | Ln)`, written without a double negation for a single literal.
  defp negated_clause(arena, [{:neg, atom}]), do: {arena, atom}
  defp negated_clause(arena, [{:pos, atom}]), do: Arena.mk_not(arena, atom)

  defp negated_clause(arena, lits) do
    {terms, arena} =
      Enum.map_reduce(lits, arena, fn
        {:pos, atom}, ar -> {atom, ar}
        {:neg, atom}, ar -> ar |> Arena.mk_not(atom) |> swap()
      end)

    {arena, disj} =
      terms
      |> tl()
      |> Enum.reduce({arena, hd(terms)}, fn t, {ar, acc} -> Arena.mk_or(ar, acc, t) end)

    Arena.mk_not(arena, disj)
  end

  defp swap({a, b}), do: {b, a}

  defp ground?(arena, lits),
    do: Enum.all?(lits, fn {_pol, atom} -> MapSet.size(Arena.free_vars(arena, atom)) == 0 end)

  defp skolem_constants(arena, term) do
    {tag, _flags, ty, left, right} = Arena.get_node(arena, term)

    case tag do
      @tag_skolem ->
        if match?({:arrow, _, _}, Map.get(arena.type_table, ty)), do: [], else: [term]

      t when t in [@tag_app, @tag_eq, @tag_or] ->
        skolem_constants(arena, left) ++ skolem_constants(arena, right)

      @tag_not ->
        skolem_constants(arena, left)

      t when t in [@tag_lam, @tag_forall] ->
        skolem_constants(arena, right)

      _ ->
        []
    end
  end

  @doc """
  Instances `{var_id, goal}` for the free variables of `item` of type `tau > $o`
  with a goal over `tau`.
  """
  @spec instances(Arena.t(), map(), [{Arena.type_id(), Arena.term_id()}]) :: [
          {non_neg_integer(), Arena.term_id()}
        ]
  def instances(%Arena{} = arena, item, goals) do
    for {var_id, ty} <- Map.get(item, :fvars, MapSet.new()),
        {:arrow, dom, cod} <- [Map.get(arena.type_table, ty)],
        cod == Arena.ty_o(),
        {^dom, goal} <- goals,
        do: {var_id, goal}
  end
end
