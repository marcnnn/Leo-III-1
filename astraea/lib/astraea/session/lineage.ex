defmodule Astraea.Session.Lineage do
  @moduledoc """
  Extracts mathematically sound, conjecture-free sub-proof lemmas from refutation DAGs.

  In refutation-based theorem proving, an intermediate inference step derived in
  search may depend on the negated conjecture (~Goal). Such steps are unsound to
  reuse across independent problems. This module traces ancestor derivation DAGs
  and partitions derived clauses into:
  - Pure theory lemmas: strictly derived from background axioms.
  - Goal-dependent inferences: discarded or kept local to the query.
  """

  alias Astraea.{Arena, Clausifier, External.ThfPrinter, ProofChecker, TptpLower, Tstp}

  @tag_eq 6

  @type lemma :: %{
          id: non_neg_integer(),
          rule: atom(),
          clause: MapSet.t(),
          thf: String.t(),
          is_unit: boolean(),
          is_equality: boolean(),
          lhs: non_neg_integer() | nil,
          rhs: non_neg_integer() | nil
        }

  @doc """
  Inspects a verified refutation `{arena, steps}` against its `%TptpLower{}` specification,
  identifies true background axioms, and harvests all non-empty intermediate clauses
  whose ancestors contain zero dependencies on the problem conjecture.
  """
  @spec harvest_theory_lemmas(Arena.t(), [ProofChecker.step()], TptpLower.t()) ::
          {:ok, [lemma()], %{total_derived: non_neg_integer(), conj_dependent: non_neg_integer()}}
          | {:error, term()}
  def harvest_theory_lemmas(%Arena{} = arena, steps, %TptpLower{} = lowered) when is_list(steps) do
    # 1. Compute keys of conjecture clauses (clausifying ONLY the 1-2 conjectures, instantaneous!)
    conj_keys =
      if lowered.conjectures == [] do
        MapSet.new()
      else
        {conj_arena, conj_clauses} = Clausifier.clausify(%{lowered | axioms: []}, sine_limit: nil)
        MapSet.new(conj_clauses, &Tstp.clause_key(conj_arena, &1))
      end

    # 2. Tag each input :axiom step as :axiom (theory) or :conjecture (goal)
    axiom_sources =
      Enum.reduce(steps, %{}, fn
        {:axiom, id, clause}, acc ->
          key = Tstp.clause_key(arena, clause)
          is_conj? = MapSet.member?(conj_keys, key)
          Map.put(acc, id, if(is_conj?, do: :conjecture, else: :axiom))

        _other, acc ->
          acc
      end)

    steps_map = Map.new(steps, fn s -> {elem(s, 1), s} end)

    # 3. Derive intermediate clauses at every step in the DAG
    case ProofChecker.derive_steps(arena, steps) do
      {:ok, _ar, derived_map} ->
        derived_steps = Enum.reject(steps, &(elem(&1, 0) == :axiom))

        {c_dep_count, lemmas} =
          Enum.reduce(derived_steps, {0, []}, fn step, {cd, acc_lemmas} ->
            id = elem(step, 1)
            clause = Map.get(derived_map, id, MapSet.new())\

            # Empty clause is the refutation root; not an intermediate lemma
            if MapSet.size(clause) == 0 do
              {cd + 1, acc_lemmas}
            else
              ancestors = collect_ancestors(steps_map, [id], MapSet.new())

              touches_conj? =
                Enum.any?(ancestors, fn anc_id ->
                  Map.get(axiom_sources, anc_id) == :conjecture
                end)

              if touches_conj? do
                {cd + 1, acc_lemmas}
              else
                case build_lemma(arena, id, elem(step, 0), clause) do
                  nil -> {cd, acc_lemmas}
                  lemma -> {cd, [lemma | acc_lemmas]}
                end
              end
            end
          end)

        stats = %{
          total_derived: length(derived_steps),
          conj_dependent: c_dep_count,
          pure_lemmas: length(lemmas)
        }

        {:ok, Enum.reverse(lemmas), stats}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp collect_ancestors(_steps_map, [], visited), do: visited

  defp collect_ancestors(steps_map, [id | rest], visited) do
    if MapSet.member?(visited, id) do
      collect_ancestors(steps_map, rest, visited)
    else
      new_visited = MapSet.put(visited, id)

      parent_ids =
        case Map.get(steps_map, id) do
          nil -> []
          {:axiom, ^id, _} -> []
          {:resolve, ^id, p1, p2, _, _} -> [p1, p2]
          {:paramod, ^id, p1, p2, _, _} -> [p1, p2]
          {:avatar_split, ^id, p, _} -> [p]
          {:avatar_assert, ^id, p, _} -> [p]
          tuple when is_tuple(tuple) and tuple_size(tuple) >= 3 ->
            p = elem(tuple, 2)
            if is_integer(p), do: [p], else: []
          _ -> []
        end

      collect_ancestors(steps_map, parent_ids ++ rest, new_visited)
    end
  end

  defp build_lemma(arena, id, rule, clause) do
    # Only harvest unit clauses (literal count == 1)
    if MapSet.size(clause) == 1 do
      [{pol, atom_id}] = MapSet.to_list(clause)

      {is_eq, l, r} =
        if pol == :pos do
          case Arena.get_node(arena, atom_id) do
            {@tag_eq, _, _, lhs, rhs} -> {true, lhs, rhs}
            _ -> {false, nil, nil}
          end
        else
          {false, nil, nil}
        end

      thf_str =
        try do
          ThfPrinter.clause_to_string(arena, clause)
        rescue
          _ -> ""
        end

      %{
        id: id,
        rule: rule,
        clause: clause,
        thf: thf_str,
        is_unit: true,
        is_equality: is_eq,
        lhs: l,
        rhs: r
      }
    else
      nil
    end
  end
end
