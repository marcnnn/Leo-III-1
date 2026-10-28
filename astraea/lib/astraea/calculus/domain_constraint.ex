defmodule Astraea.Calculus.DomainConstraint do
  @moduledoc """
  Domain constraints (Leo-III `DomainConstraintInstanceControl.detectDomainConstraint`
  and `DomainConstraintInstances`).

  A clause `X = t1 | ... | X = tn` with a single free variable `X: T` and closed
  `ti` states that every element of `T` is one of the `ti`, i.e. `dom(T)` is a
  subset of `{t1, ..., tn}`. Clauses with variables of a constrained type are then
  also instantiated with these terms. Leo-III's `constraintLiteral` ignores the
  polarity; here only positive literals count, since `X != a | X != b` does not
  bound the domain.

  Instances are plain `:subst` steps, so they need no kernel support, and the
  original clause stays (as in Leo-III), so completeness is unaffected.
  """

  alias Astraea.Arena

  @tag_fvar 3
  @tag_eq 6

  @doc """
  `{:ok, type, terms}` if `lits` is a domain constraint, else `:none`.
  """
  @spec detect(Arena.t(), Astraea.ProofChecker.clause()) ::
          {:ok, Arena.type_id(), [Arena.term_id()]} | :none
  def detect(%Arena{} = arena, lits) do
    fvars =
      Enum.reduce(lits, MapSet.new(), fn {_pol, atom}, acc ->
        MapSet.union(acc, Arena.free_vars(arena, atom))
      end)

    with [{var, ty}] <- MapSet.to_list(fvars),
         true <- MapSet.size(lits) > 0,
         terms when is_list(terms) <- constraint_terms(arena, lits, var) do
      {:ok, ty, terms |> Enum.uniq() |> Enum.sort()}
    else
      _ -> :none
    end
  end

  defp constraint_terms(arena, lits, var) do
    Enum.reduce_while(lits, [], fn
      {:pos, atom}, acc ->
        case Arena.get_node(arena, atom) do
          {@tag_eq, _, _, l, r} ->
            cond do
              var?(arena, l, var) and Arena.free_vars(arena, r) == MapSet.new() ->
                {:cont, [r | acc]}

              var?(arena, r, var) and Arena.free_vars(arena, l) == MapSet.new() ->
                {:cont, [l | acc]}

              true ->
                {:halt, :none}
            end

          _ ->
            {:halt, :none}
        end

      _, _acc ->
        {:halt, :none}
    end)
  end

  defp var?(arena, term, var), do: match?({@tag_fvar, _, _, ^var, _}, Arena.get_node(arena, term))

  @doc """
  Records a detected constraint; of two constraints on one type the smaller set
  wins (Leo-III `addDomainConstr` on a duplicate).
  """
  @spec add(%{Arena.type_id() => [Arena.term_id()]}, Arena.type_id(), [Arena.term_id()]) ::
          %{Arena.type_id() => [Arena.term_id()]}
  def add(domains, ty, terms) do
    Map.update(domains, ty, terms, fn old ->
      if length(old) > length(terms), do: terms, else: old
    end)
  end

  @doc """
  Substitutions instantiating the variables of `fvars` (`{var, type}`) whose type
  is constrained, smallest domains first. As in Leo-III, a positive `max_instances`
  stops before the number of instances would exceed it; `-1` means no bound and
  `0` disables the rule.
  """
  @spec substitutions(
          MapSet.t({non_neg_integer(), Arena.type_id()}),
          %{Arena.type_id() => [Arena.term_id()]},
          integer()
        ) :: [Arena.subst()]
  def substitutions(_fvars, _domains, 0), do: []

  def substitutions(fvars, domains, max_instances) do
    vars =
      fvars
      |> Enum.filter(fn {_var, ty} -> Map.has_key?(domains, ty) end)
      |> Enum.sort_by(fn {var, ty} -> {length(Map.fetch!(domains, ty)), var} end)

    {substs, _count} =
      Enum.reduce_while(vars, {[%{}], 1}, fn {var, ty}, {substs, count} ->
        terms = Map.fetch!(domains, ty)

        if max_instances > 0 and count * length(terms) > max_instances do
          {:halt, {substs, count}}
        else
          substs = for s <- substs, t <- terms, do: Map.put(s, var, t)
          {:cont, {substs, count * length(terms)}}
        end
      end)

    Enum.reject(substs, &(map_size(&1) == 0))
  end
end
