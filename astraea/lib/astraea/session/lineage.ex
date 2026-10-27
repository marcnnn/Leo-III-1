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
    # 1. Compute keys of pure background axioms (without conjectures or SInE)
    {ax_arena, ax_clauses} = Clausifier.clausify(%{lowered | conjectures: []}, sine_limit: nil)
    axiom_keys = MapSet.new(ax_clauses, &Tstp.clause_key(ax_arena, &1))

    # 2. Tag each input :axiom step as :axiom (theory) or :conjecture (goal)
    axiom_sources =
      Enum.reduce(steps, %{}, fn
        {:axiom, id, clause}, acc ->
          key = Tstp.clause_key(arena, clause)
          is_axiom? = MapSet.member?(axiom_keys, key)
          Map.put(acc, id, if(is_axiom?, do: :axiom, else: :conjecture))

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
            clause = Map.get(derived_map, id, MapSet.new())

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
      step = Map.get(steps_map, id)
      parents = if step, do: ProofChecker.step_parents(step), else: []
      collect_ancestors(steps_map, parents ++ rest, MapSet.put(visited, id))
    end
  end

  defp build_lemma(%Arena{} = arena, id, rule, clause) do
    thf_str =
      try do
        ThfPrinter.clause_to_string(arena, clause)
      rescue
        _ -> nil
      end

    if is_nil(thf_str) do
      nil
    else
      is_unit = MapSet.size(clause) == 1

      {is_eq, lhs, rhs} =
        if is_unit do
          [{pol, atom_id}] = MapSet.to_list(clause)

          if pol == :pos do
            case Arena.get_node(arena, atom_id) do
              {@tag_eq, _flags, _ty, l, r} -> {true, l, r}
              _ -> {false, nil, nil}
            end
          else
            {false, nil, nil}
          end
        else
          {false, nil, nil}
        end

      %{
        id: id,
        rule: rule,
        clause: clause,
        thf: thf_str,
        is_unit: is_unit,
        is_equality: is_eq,
        lhs: lhs,
        rhs: rhs
      }
    end
  end
end
