defmodule Astraea.Calculus.Avatar do
  @moduledoc """
  AVATAR Clause Splitting (Advanced Vampire Architecture for Theorem Proving).

  Partitions non-unit clauses into variable-independent components:
  $$C = C_1 \\lor C_2 \\lor \\dots \\lor C_k$$
  where $\\text{vars}(C_i) \\cap \\text{vars}(C_j) = \\emptyset$ for $i \\ne j$.

  For each component $C_i$, AVATAR allocates a propositional abstraction guard variable
  $[C_i]$ in `Astraea.Engine.CdclSat`:
  1. The propositional clause $[C_1] \\lor \\dots \\lor [C_k]$ is asserted in the SAT solver.
  2. Each component $C_i$ enters saturation as an independent guarded clause $C_i \\leftarrow [C_i]$.
  3. When an empty clause is derived from guarded clauses ($\\bot \\leftarrow [A_1], \\dots, [A_m]$),
     the learned conflict clause $\\neg [A_1] \\lor \\dots \\lor \\neg [A_m]$ is fed back into
     the SAT solver.
  4. When the SAT solver becomes UNSAT, the propositional refutation certifies that all branches
     are closed.
  """

  alias Astraea.Arena

  @doc """
  Partitions a set of literals into variable-independent components.
  Two literals belong to the same component if they share at least one free variable.
  Ground literals (with zero free variables) each form their own distinct component.
  Returns a list of literal sets (MapSets).
  """
  @spec components(Arena.t(), MapSet.t(ProofChecker.literal())) :: [MapSet.t(ProofChecker.literal())]
  def components(%Arena{} = arena, lits) do
    lit_list = MapSet.to_list(lits)

    # Compute free variable set for each literal
    lits_with_vars =
      Enum.map(lit_list, fn {_pol, atom} = lit ->
        vars =
          arena
          |> Arena.free_vars(atom)
          |> MapSet.new(fn {id, _ty} -> id end)

        {lit, vars}
      end)

    # Separate ground literals (each is an independent component)
    {ground, open} =
      Enum.split_with(lits_with_vars, fn {_lit, vars} -> MapSet.size(vars) == 0 end)

    ground_comps = Enum.map(ground, fn {lit, _vars} -> MapSet.new([lit]) end)

    # Group open literals into connected components via variable sharing graph
    open_comps = connected_components(open, [])

    ground_comps ++ open_comps
  end

  @doc """
  Determines whether a clause can be split into at least two independent components.
  """
  @spec splittable?(Arena.t(), MapSet.t(ProofChecker.literal())) :: boolean()
  def splittable?(%Arena{} = arena, lits) do
    if MapSet.size(lits) >= 2 do
      length(components(arena, lits)) >= 2
    else
      false
    end
  end

  # ---------------------------------------------------------------------------
  # Graph Connected Components for Variable Sharing
  # ---------------------------------------------------------------------------

  defp connected_components([], acc), do: acc

  defp connected_components([{lit, vars} | rest], acc) do
    {merged_comp, remaining} = grow_component(vars, [lit], rest)
    connected_components(remaining, [MapSet.new(merged_comp) | acc])
  end

  defp grow_component(comp_vars, comp_lits, remaining) do
    # Find any remaining literal that shares a variable with comp_vars
    {connected, unconnected} =
      Enum.split_with(remaining, fn {_l, v} ->
        not MapSet.disjoint?(comp_vars, v)
      end)

    if connected == [] do
      {comp_lits, unconnected}
    else
      new_vars =
        Enum.reduce(connected, comp_vars, fn {_l, v}, cv -> MapSet.union(cv, v) end)

      new_lits =
        comp_lits ++ Enum.map(connected, &elem(&1, 0))

      grow_component(new_vars, new_lits, unconnected)
    end
  end
end
