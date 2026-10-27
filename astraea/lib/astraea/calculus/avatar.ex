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
  # ---------------------------------------------------------------------------
  # Propositional Refutation Reconstruction
  # ---------------------------------------------------------------------------

  @doc """
  Reconstructs a propositional resolution refutation from an unsatisfiable set of propositional clauses.
  Takes `clauses_map` (%{step_id => MapSet.t(literal())}) and `next_id`.
  Returns `{:ok, steps, empty_id}` or `:error`.
  """
  @spec resolve_propositional_unsat(
          %{pos_integer() => MapSet.t(ProofChecker.literal())},
          pos_integer()
        ) :: {:ok, [ProofChecker.step()], pos_integer()} | :error
  def resolve_propositional_unsat(clauses_map, next_id) do
    case Enum.find(clauses_map, fn {_id, lits} -> MapSet.size(lits) == 0 end) do
      {empty_id, _} ->
        {:ok, [], empty_id}

      nil ->
        do_prop_resolve(clauses_map, next_id, [])
    end
  end

  defp do_prop_resolve(clauses, next_id, steps_acc) do
    case Enum.find(clauses, fn {_id, lits} -> MapSet.size(lits) == 0 end) do
      {empty_id, _} ->
        {:ok, Enum.reverse(steps_acc), empty_id}

      nil ->
        unit_candidates =
          Enum.filter(clauses, fn {_id, lits} -> MapSet.size(lits) == 1 end)

        unit_resolution_result =
          Enum.find_value(unit_candidates, fn {u_id, u_lits} ->
            [{u_pol, u_atom}] = MapSet.to_list(u_lits)
            opp_lit = {flip_pol(u_pol), u_atom}

            Enum.find_value(clauses, fn {c_id, c_lits} ->
              if c_id != u_id and MapSet.member?(c_lits, opp_lit) do
                resolvent = MapSet.delete(c_lits, opp_lit)

                if MapSet.size(resolvent) == 0 or not Enum.any?(clauses, fn {_id, l} -> l == resolvent end) do
                  {pos_id, neg_id} =
                    if u_pol == :pos, do: {u_id, c_id}, else: {c_id, u_id}

                  step = {:resolve, next_id, pos_id, neg_id, {:pos, u_atom}}
                  {resolvent, step}
                else
                  nil
                end
              else
                nil
              end
            end)
          end)

        case unit_resolution_result do
          {resolvent, step} ->
            if MapSet.size(resolvent) == 0 do
              {:ok, Enum.reverse([step | steps_acc]), next_id}
            else
              do_prop_resolve(
                Map.put(clauses, next_id, resolvent),
                next_id + 1,
                [step | steps_acc]
              )
            end

          nil ->
            general_prop_resolve(clauses, next_id, steps_acc)
        end
    end
  end

  defp general_prop_resolve(clauses, next_id, steps_acc) do
    pos_atoms =
      Enum.reduce(clauses, MapSet.new(), fn {_id, lits}, acc ->
        Enum.reduce(lits, acc, fn
          {:pos, a}, ac -> MapSet.put(ac, a)
          _, ac -> ac
        end)
      end)

    neg_atoms =
      Enum.reduce(clauses, MapSet.new(), fn {_id, lits}, acc ->
        Enum.reduce(lits, acc, fn
          {:neg, a}, ac -> MapSet.put(ac, a)
          _, ac -> ac
        end)
      end)

    pivot_atoms = MapSet.intersection(pos_atoms, neg_atoms)

    case Enum.at(pivot_atoms, 0) do
      nil ->
        :error

      pivot ->
        pos_clauses =
          Enum.filter(clauses, fn {_id, lits} -> MapSet.member?(lits, {:pos, pivot}) end)

        neg_clauses =
          Enum.filter(clauses, fn {_id, lits} -> MapSet.member?(lits, {:neg, pivot}) end)

        pairs = for p <- pos_clauses, n <- neg_clauses, do: {p, n}

        {new_clauses, new_steps, next_id_acc, finished} =
          Enum.reduce_while(
            pairs,
            {clauses, steps_acc, next_id, nil},
            fn {{p_id, p_lits}, {n_id, n_lits}}, {cls, acc, nid, _} ->
              res =
                MapSet.union(
                  MapSet.delete(p_lits, {:pos, pivot}),
                  MapSet.delete(n_lits, {:neg, pivot})
                )

              if tautology?(res) or Enum.any?(cls, fn {_id, l} -> l == res end) do
                {:cont, {cls, acc, nid, nil}}
              else
                step = {:resolve, nid, p_id, n_id, {:pos, pivot}}

                if MapSet.size(res) == 0 do
                  {:halt, {cls, [step | acc], nid, :done}}
                else
                  {:cont, {Map.put(cls, nid, res), [step | acc], nid + 1, nil}}
                end
              end
            end
          )

        if finished == :done do
          {:ok, Enum.reverse(new_steps), next_id_acc}
        else
          remaining =
            new_clauses
            |> Enum.reject(fn {_id, lits} ->
              MapSet.member?(lits, {:pos, pivot}) or MapSet.member?(lits, {:neg, pivot})
            end)
            |> Map.new()

          do_prop_resolve(remaining, next_id_acc, new_steps)
        end
    end
  end

  defp flip_pol(:pos), do: :neg
  defp flip_pol(:neg), do: :pos

  defp tautology?(lits) do
    Enum.any?(lits, fn
      {:pos, a} -> MapSet.member?(lits, {:neg, a})
      {:neg, a} -> MapSet.member?(lits, {:pos, a})
    end)
  end
end
