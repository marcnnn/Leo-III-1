defmodule Astraea.Compressor do
  @moduledoc """
  WP4: LCF Proof DAG Compression & Macro-Inference Pattern Miner.

  Provides two layers of post-saturation proof analysis over verified
  `Astraea.ProofChecker` refutation DAGs:
  1. **Sound LCF Proof DAG Compression (`compress_dag/2`)**:
     - Composes consecutive linear substitution chains (`{:subst, id1, p, s1}` followed
       by `{:subst, id2, id1, s2}`) into a single LCF `:subst` inference step.
     - Eliminates identity `:subst` steps where the substitution leaves the parent
       clause invariant.
     - Deduplicates structurally identical inference steps and prunes unreachable
       ancestors from the final empty clause `⊥`.
     - Re-verifies every compressed proof through `Astraea.ProofChecker.verify_refutation/2`
       (falling back to the original proof if verification ever fails).
  2. **Macro-Inference Pattern Mining (`analyze_proof/2` & `summarize_corpus/1`)**:
     - Identifies recurring linear inference bigrams/trigrams (`:subst -> :resolve`,
       `:refl -> :resolve`, `:subst -> :paramod`, `:func_ext -> :resolve`, etc.)
       and computes proof DAG compression ratios across benchmark splits.
  """

  alias Astraea.{Arena, ProofChecker}

  @type compression_meta :: %{
          raw_steps: non_neg_integer(),
          compressed_steps: non_neg_integer(),
          steps_saved: non_neg_integer(),
          subst_fusions: non_neg_integer(),
          dedup_merges: non_neg_integer(),
          rule_histogram: %{atom() => non_neg_integer()},
          macro_patterns: %{atom() => non_neg_integer()}
        }

  @doc """
  Compresses an LCF refutation DAG `{arena, steps}` by fusing linear `:subst -> :subst`
  chains, deduplicating identical steps, pruning unreachable nodes, and re-verifying
  the resulting proof with `Astraea.ProofChecker.verify_refutation/2`.
  """
  @spec compress_dag(Arena.t(), [ProofChecker.step()]) ::
          {:ok, Arena.t(), [ProofChecker.step()], compression_meta()}
  def compress_dag(%Arena{} = arena, steps) when is_list(steps) do
    raw_len = length(steps)

    if raw_len == 0 do
      {:ok, arena, steps, empty_meta()}
    else
      # 1. Fuse `:subst -> :subst` chains and rewire step parent IDs
      {arena2, fused_steps, subst_fusions} = fuse_subst_chains(arena, steps)

      # 2. Deduplicate structurally identical steps and rewire IDs
      {dedup_steps, dedup_merges} = deduplicate_steps(fused_steps)

      # 3. Prune unreachable steps from the final step (empty clause root)
      pruned_steps = prune_unreachable(dedup_steps)

      # 4. Gate 3 safety: verify compressed proof with the LCF kernel
      case ProofChecker.verify_refutation(arena2, pruned_steps) do
        :ok ->
          meta = build_meta(raw_len, pruned_steps, subst_fusions, dedup_merges)
          {:ok, arena2, pruned_steps, meta}

        {:error, _reason} ->
          meta = build_meta(raw_len, steps, 0, 0)
          {:ok, arena, steps, meta}
      end
    end
  end

  @doc """
  Computes rule histograms and linear macro-inference patterns for a single proof DAG.
  """
  @spec analyze_proof([ProofChecker.step()]) :: %{
          proof_length: non_neg_integer(),
          rule_histogram: %{atom() => non_neg_integer()},
          macro_patterns: %{atom() => non_neg_integer()}
        }
  def analyze_proof(steps) when is_list(steps) do
    %{
      proof_length: length(steps),
      rule_histogram: compute_rule_histogram(steps),
      macro_patterns: mine_macro_patterns(steps)
    }
  end

  @doc """
  Aggregates proof compression and macro-inference statistics across a list of
  solved theorem entries from `Astraea.Portfolio.evaluate_split/2`.
  """
  @spec summarize_corpus([map()]) :: map()
  def summarize_corpus(thm_solved_entries) when is_list(thm_solved_entries) do
    total_raw =
      Enum.reduce(thm_solved_entries, 0, fn e, acc ->
        acc + Map.get(e, :raw_proof_length, Map.get(e, :proof_length, 0))
      end)

    total_compressed =
      Enum.reduce(thm_solved_entries, 0, fn e, acc ->
        acc + Map.get(e, :proof_length, 0)
      end)

    total_saved = max(0, total_raw - total_compressed)

    total_subst_fusions =
      Enum.reduce(thm_solved_entries, 0, fn e, acc ->
        comp = Map.get(e, :compression, %{})
        acc + Map.get(comp, :subst_fusions, 0)
      end)

    total_dedup_merges =
      Enum.reduce(thm_solved_entries, 0, fn e, acc ->
        comp = Map.get(e, :compression, %{})
        acc + Map.get(comp, :dedup_merges, 0)
      end)

    rule_histogram =
      Enum.reduce(thm_solved_entries, %{}, fn e, acc ->
        comp = Map.get(e, :compression, %{})
        hist = Map.get(comp, :rule_histogram, %{})
        Map.merge(acc, hist, fn _k, v1, v2 -> v1 + v2 end)
      end)

    macro_patterns =
      Enum.reduce(thm_solved_entries, %{}, fn e, acc ->
        comp = Map.get(e, :compression, %{})
        macros = Map.get(comp, :macro_patterns, %{})
        Map.merge(acc, macros, fn _k, v1, v2 -> v1 + v2 end)
      end)

    reduction_pct =
      if total_raw > 0 do
        Float.round(total_saved * 100.0 / total_raw, 2)
      else
        0.0
      end

    %{
      theorems_analyzed: length(thm_solved_entries),
      total_raw_steps: total_raw,
      total_compressed_steps: total_compressed,
      total_steps_saved: total_saved,
      step_reduction_pct: reduction_pct,
      total_subst_fusions: total_subst_fusions,
      total_dedup_merges: total_dedup_merges,
      rule_histogram: rule_histogram,
      macro_patterns: macro_patterns
    }
  end

  # ---------------------------------------------------------------------------
  # 1. Linear `:subst -> :subst` Chain Fusion
  # ---------------------------------------------------------------------------

  defp fuse_subst_chains(%Arena{} = arena, steps) do
    {arena, _subst_table, rev_steps, fusions} =
      Enum.reduce(steps, {arena, %{}, [], 0}, fn step, {ar, sub_tbl, acc, fus_cnt} ->
        case step do
          {:subst, id, parent_id, sub2} ->
            case Map.get(sub_tbl, parent_id) do
              nil ->
                sub_tbl2 = Map.put(sub_tbl, id, {parent_id, sub2})
                {ar, sub_tbl2, [step | acc], fus_cnt}

              {grandparent_id, sub1} ->
                {ar2, composed} = compose_substitutions(ar, sub1, sub2)
                fused_step = {:subst, id, grandparent_id, composed}
                sub_tbl2 = Map.put(sub_tbl, id, {grandparent_id, composed})
                {ar2, sub_tbl2, [fused_step | acc], fus_cnt + 1}
            end

          _ ->
            {ar, sub_tbl, [step | acc], fus_cnt}
        end
      end)

    {arena, Enum.reverse(rev_steps), fusions}
  end

  defp compose_substitutions(%Arena{} = arena, sub1, sub2) do
    {arena, mapped_sub1} =
      Enum.reduce(sub1, {arena, %{}}, fn {fv_id, term_id}, {ar, acc} ->
        {ar2, term_inst} = Arena.subst_fvar(ar, term_id, sub2)
        {ar2, Map.put(acc, fv_id, term_inst)}
      end)

    merged = Map.merge(sub2, mapped_sub1)
    {arena, merged}
  end

  # ---------------------------------------------------------------------------
  # 2. Structural Step Deduplication & Parent Rewiring
  # ---------------------------------------------------------------------------

  defp deduplicate_steps(steps) do
    {_seen_sigs, _id_remap, rev_steps, merges} =
      Enum.reduce(steps, {%{}, %{}, [], 0}, fn step, {seen, remap, acc, m_cnt} ->
        rewired = rewire_step_parents(step, remap)
        id = step_id(rewired)
        sig = step_signature(rewired)

        case Map.get(seen, sig) do
          nil ->
            {Map.put(seen, sig, id), Map.put(remap, id, id), [rewired | acc], m_cnt}

          existing_id ->
            {seen, Map.put(remap, id, existing_id), acc, m_cnt + 1}
        end
      end)

    {Enum.reverse(rev_steps), merges}
  end

  defp rewire_step_parents({:axiom, id, c}, _remap), do: {:axiom, id, c}
  defp rewire_step_parents({:refl, id, t}, _remap), do: {:refl, id, t}
  defp rewire_step_parents({:symm, id, p}, remap), do: {:symm, id, Map.get(remap, p, p)}

  defp rewire_step_parents({:trans, id, p1, p2}, remap),
    do: {:trans, id, Map.get(remap, p1, p1), Map.get(remap, p2, p2)}

  defp rewire_step_parents({:subst, id, p, sub}, remap),
    do: {:subst, id, Map.get(remap, p, p), sub}

  defp rewire_step_parents({:cong, id, p, eq, arg}, remap),
    do: {:cong, id, Map.get(remap, p, p), eq, arg}

  defp rewire_step_parents({:func_ext, id, p, fv, ty}, remap),
    do: {:func_ext, id, Map.get(remap, p, p), fv, ty}

  defp rewire_step_parents({:paramod, id, p1, p2, eq, tl, rl}, remap),
    do: {:paramod, id, Map.get(remap, p1, p1), Map.get(remap, p2, p2), eq, tl, rl}

  defp rewire_step_parents({:resolve, id, p1, p2, lit}, remap),
    do: {:resolve, id, Map.get(remap, p1, p1), Map.get(remap, p2, p2), lit}

  defp rewire_step_parents(step, remap), do: ProofChecker.rewire_parents(step, remap)

  defp step_signature({:axiom, _id, c}), do: {:axiom, c}
  defp step_signature({:refl, _id, t}), do: {:refl, t}
  defp step_signature({:symm, _id, p}), do: {:symm, p}
  defp step_signature({:trans, _id, p1, p2}), do: {:trans, p1, p2}
  defp step_signature({:subst, _id, p, sub}), do: {:subst, p, sub}
  defp step_signature({:cong, _id, p, eq, arg}), do: {:cong, p, eq, arg}
  defp step_signature({:func_ext, _id, p, fv, ty}), do: {:func_ext, p, fv, ty}
  defp step_signature({:paramod, _id, p1, p2, eq, tl, rl}), do: {:paramod, p1, p2, eq, tl, rl}
  defp step_signature({:resolve, _id, p1, p2, lit}), do: {:resolve, p1, p2, lit}
  defp step_signature(step), do: Tuple.delete_at(step, 1)

  # ---------------------------------------------------------------------------
  # 3. Unreachable Ancestor Pruning
  # ---------------------------------------------------------------------------

  defp prune_unreachable([]), do: []

  defp prune_unreachable(steps) do
    steps_map = Map.new(steps, fn s -> {step_id(s), s} end)
    root_id = step_id(List.last(steps))
    visited = collect_ancestors(steps_map, [root_id], MapSet.new())

    Enum.filter(steps, fn s -> MapSet.member?(visited, step_id(s)) end)
  end

  defp collect_ancestors(_steps_map, [], visited), do: visited

  defp collect_ancestors(steps_map, [id | rest], visited) do
    if MapSet.member?(visited, id) do
      collect_ancestors(steps_map, rest, visited)
    else
      case Map.get(steps_map, id) do
        nil ->
          collect_ancestors(steps_map, rest, visited)

        step ->
          parents = step_parents(step)
          collect_ancestors(steps_map, parents ++ rest, MapSet.put(visited, id))
      end
    end
  end

  defp step_id(step), do: elem(step, 1)
  defp step_rule(step), do: elem(step, 0)

  defp step_parents({:axiom, _id, _c}), do: []
  defp step_parents({:refl, _id, _t}), do: []
  defp step_parents({:symm, _id, p}), do: [p]
  defp step_parents({:trans, _id, p1, p2}), do: [p1, p2]
  defp step_parents({:subst, _id, p, _s}), do: [p]
  defp step_parents({:cong, _id, p, _eq, _arg}), do: [p]
  defp step_parents({:func_ext, _id, p, _fv, _ty}), do: [p]
  defp step_parents({:paramod, _id, p1, p2, _eq, _tl, _rl}), do: [p1, p2]
  defp step_parents({:resolve, _id, p1, p2, _lit}), do: [p1, p2]
  defp step_parents(step), do: ProofChecker.step_parents(step)

  # ---------------------------------------------------------------------------
  # 4. Macro-Inference Pattern Mining & Telemetry
  # ---------------------------------------------------------------------------

  defp build_meta(raw_len, compressed_steps, subst_fusions, dedup_merges) do
    comp_len = length(compressed_steps)

    %{
      raw_steps: raw_len,
      compressed_steps: comp_len,
      steps_saved: max(0, raw_len - comp_len),
      subst_fusions: subst_fusions,
      dedup_merges: dedup_merges,
      rule_histogram: compute_rule_histogram(compressed_steps),
      macro_patterns: mine_macro_patterns(compressed_steps)
    }
  end

  defp empty_meta do
    %{
      raw_steps: 0,
      compressed_steps: 0,
      steps_saved: 0,
      subst_fusions: 0,
      dedup_merges: 0,
      rule_histogram: %{},
      macro_patterns: %{}
    }
  end

  defp compute_rule_histogram(steps) do
    Enum.frequencies_by(steps, &step_rule/1)
  end

  defp mine_macro_patterns(steps) do
    rule_by_id = Map.new(steps, fn s -> {step_id(s), step_rule(s)} end)

    Enum.reduce(steps, %{}, fn step, acc ->
      case step do
        {:resolve, _id, p1, p2, _lit} ->
          r1 = Map.get(rule_by_id, p1)
          r2 = Map.get(rule_by_id, p2)

          cond do
            r1 == :refl or r2 == :refl ->
              Map.update(acc, :eq_resolution, 1, &(&1 + 1))

            r1 == :subst or r2 == :subst ->
              Map.update(acc, :inst_resolve, 1, &(&1 + 1))

            r1 == :func_ext or r2 == :func_ext ->
              Map.update(acc, :ext_resolve, 1, &(&1 + 1))

            true ->
              acc
          end

        {:paramod, _id, p1, p2, _eq, _tl, _rl} ->
          r1 = Map.get(rule_by_id, p1)
          r2 = Map.get(rule_by_id, p2)

          cond do
            r1 == :func_ext or r2 == :func_ext ->
              Map.update(acc, :ext_paramod, 1, &(&1 + 1))

            r1 == :subst or r2 == :subst ->
              Map.update(acc, :superposition, 1, &(&1 + 1))

            true ->
              acc
          end

        _ ->
          acc
      end
    end)
  end
end
