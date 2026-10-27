defmodule Astraea.Experiments.MacroCachingEval do
  @moduledoc """
  Empirical evaluation of:
  1. Proof DAG macro-compression (compressing multi-step primitive inferences into single rules).
  2. Sub-proof / Lemma Caching across theorem proving problems:
     - Extracting non-trivial intermediate derived lemmas from solved proofs.
     - Testing whether caching & seeding these lemmas helps solve previously unsolved problems.
     - Measuring the impact on search efficiency (iterations, time, active clauses, swamping effect).
  """

  alias Astraea.{Arena, Compressor, Portfolio, ProofChecker, Prover, TptpCorpus, TptpLower}

  def run(split \\ :smoke, opts \\ []) do
    timeout_ms = Keyword.get(opts, :timeout_ms, 2500)
    concurrency = Keyword.get(opts, :concurrency, 4)

    IO.puts("=====================================================================")
    IO.puts(" ASTRAEA WP4 EXPERIMENT: SUB-PROOF CACHING & MACRO-RULE EVALUATION  ")
    IO.puts(" Split: #{split} | Timeout: #{timeout_ms}ms | Concurrency: #{concurrency}")
    IO.puts("=====================================================================\n")

    # 1. Run Baseline Evaluation
    IO.puts("--- Phase 1: Baseline Split Evaluation ---")
    baseline = Portfolio.evaluate_split(split, timeout_ms: timeout_ms, max_concurrency: concurrency)
    IO.puts("Theorems Solved: #{baseline.thm_solved_count} / #{baseline.thm_total} (#{Float.round(baseline.thm_solved_count * 100.0 / max(baseline.thm_total, 1), 2)}%)")

    # 2. Macro-Inference & DAG Compression Census
    IO.puts("\n--- Phase 2: Macro-Inference Compression Census ---")
    comp_summary = Compressor.summarize_corpus(baseline.thm_solved)
    IO.puts("Total Proofs Analyzed: #{comp_summary.theorems_analyzed}")
    IO.puts("Raw LCF Steps:         #{comp_summary.total_raw_steps}")
    IO.puts("Compressed LCF Steps:  #{comp_summary.total_compressed_steps}")
    IO.puts("Steps Saved:           #{comp_summary.total_steps_saved} (#{comp_summary.reduction_pct}%)")
    IO.puts("Subst Fusions:         #{comp_summary.total_subst_fusions}")
    IO.puts("Structural Dedup:      #{comp_summary.total_dedup_merges}")
    IO.puts("Mined Macro-Patterns:")
    for {macro, count} <- comp_summary.macro_patterns do
      IO.puts("  * #{macro}: #{count}")
    end

    # 3. Extract Derived Lemmas (Sub-proofs) from Solved Theorems
    IO.puts("\n--- Phase 3: Sub-Proof Lemma Extraction ---")
    lemmas_by_domain = extract_lemmas(baseline.raw_results)
    total_lemmas = Enum.reduce(lemmas_by_domain, 0, fn {_, l}, acc -> acc + length(l) end)
    IO.puts("Extracted #{total_lemmas} non-trivial derived lemmas across #{map_size(lemmas_by_domain)} domains:")
    for {dom, lemmas} <- lemmas_by_domain do
      units = Enum.count(lemmas, &(MapSet.size(&1.clause) == 1))
      IO.puts("  * Domain #{dom}: #{length(lemmas)} lemmas (#{units} unit clauses / equalities)")
    end

    # 4. Identify Solved vs Unsolved Problems
    unsolved_theorems =
      baseline.raw_results
      |> Enum.filter(fn {e, status, _} -> e.status == "Theorem" and not match?({:proved, _, _}, status) end)
      |> Enum.map(&elem(&1, 0))

    solved_theorems =
      baseline.raw_results
      |> Enum.filter(fn {e, status, _} -> e.status == "Theorem" and match?({:proved, _, _}, status) end)
      |> Enum.map(fn {e, {:proved, steps, stats}, dur} -> {e, steps, stats, dur} end)

    IO.puts("\n--- Phase 4: Cross-Problem Lemma Transfer on Unsolved Problems ---")
    IO.puts("Evaluating if caching sub-proof lemmas from solved problems can prove unsolved problems:")
    IO.puts("Unsolved problem count: #{length(unsolved_theorems)}")

    unsolved_transfer_results =
      for prob <- unsolved_theorems do
        path = TptpCorpus.problem_path(prob.problem)
        dom_lemmas = Map.get(lemmas_by_domain, prob.domain, [])
        eval_with_cached_lemmas(path, prob, dom_lemmas, timeout_ms)
      end

    newly_solved = Enum.filter(unsolved_transfer_results, & &1.proved)
    IO.puts("Newly Solved with Cached Sub-proofs: #{length(newly_solved)} / #{length(unsolved_theorems)}")
    for res <- newly_solved do
      IO.puts("  [SUCCESS] #{res.problem.problem} solved with #{res.used_lemmas} cached lemmas used!")
    end
    if newly_solved == [] do
      IO.puts("  [RESULT] None of the #{length(unsolved_theorems)} open problems were solved solely by injecting cached lemmas.")
    end

    # 5. Search Efficiency & Utility Problem on Solved Problems
    IO.puts("\n--- Phase 5: Search Efficiency Impact on Solved Problems (Utility Problem Test) ---")
    IO.puts("Testing search impact when injecting domain-cached lemmas into already-solved problems:")
    test_sample = Enum.take(solved_theorems, 10)

    utility_results =
      for {prob, _steps, base_stats, base_dur} <- test_sample do
        path = TptpCorpus.problem_path(prob.problem)
        dom_lemmas = Map.get(lemmas_by_domain, prob.domain, [])
        # Exclude lemmas that originated from this exact problem
        external_lemmas = Enum.reject(dom_lemmas, &(&1.source == prob.problem))

        eval_utility(path, prob, base_stats, base_dur, external_lemmas, timeout_ms)
      end

    IO.puts("\nSummary of Search Impact across #{length(utility_results)} test theorems:")
    valid_diffs = Enum.filter(utility_results, &is_nil(&1[:note]))
    if valid_diffs != [] do
      avg_iter_change =
        Enum.sum(Enum.map(valid_diffs, & &1.iter_diff)) / length(valid_diffs)
      avg_time_change =
        Enum.sum(Enum.map(valid_diffs, & &1.time_diff)) / length(valid_diffs)
      avg_clause_change =
        Enum.sum(Enum.map(valid_diffs, & &1.passive_diff)) / length(valid_diffs)

      IO.puts("  Average Iteration Change: #{Float.round(avg_iter_change, 2)} iterations")
      IO.puts("  Average Time Change:      #{Float.round(avg_time_change, 2)} ms")
      IO.puts("  Average Passive Queue Change: #{Float.round(avg_clause_change, 2)} clauses")
    end

    %{
      baseline: baseline,
      comp_summary: comp_summary,
      total_lemmas: total_lemmas,
      unsolved_transfer_results: unsolved_transfer_results,
      utility_results: utility_results
    }
  end

  defp extract_lemmas(raw_results) do
    Enum.reduce(raw_results, %{}, fn
      {entry, {:proved, steps, stats}, _ms}, acc when is_map(entry) and entry.status == "Theorem" ->
        arena = stats.arena
        prob = entry.problem
        domain = entry.domain

        if arena && steps != [] do
          case ProofChecker.derive_steps(arena, steps) do
            {:ok, _ar, derived_map} ->
              # Filter non-axiom, non-empty derived clauses
              lemmas =
                steps
                |> Enum.reject(&(elem(&1, 0) == :axiom))
                |> Enum.map(fn step ->
                  id = elem(step, 1)
                  clause = Map.get(derived_map, id, MapSet.new())
                  %{id: id, rule: elem(step, 0), clause: clause, source: prob}
                end)
                |> Enum.reject(&(MapSet.size(&1.clause) == 0))
                # Keep small/focused lemmas (at most 2 literals)
                |> Enum.filter(&(MapSet.size(&1.clause) <= 2))

              Map.update(acc, domain, lemmas, &(&1 ++ lemmas))

            _ ->
              acc
          end
        else
          acc
        end

      _other, acc ->
        acc
    end)
  end

  defp eval_with_cached_lemmas(path, prob, dom_lemmas, timeout_ms) do
    lowered = TptpLower.from_file(path)

    relevant_lemmas =
      dom_lemmas
      |> Enum.take(20)

    {arena, extra_clauses} = import_lemmas(lowered.arena, relevant_lemmas)
    all_clauses = lowered.clauses ++ extra_clauses

    t0 = System.monotonic_time(:millisecond)
    res = Prover.prove_clauses(arena, all_clauses, timeout_ms: timeout_ms)
    t1 = System.monotonic_time(:millisecond)
    dur = t1 - t0

    case res do
      {:proved, steps, stats} ->
        %{problem: prob, proved: true, duration_ms: dur, iterations: stats.iterations, used_lemmas: count_used_lemmas(steps, extra_clauses)}

      other ->
        %{problem: prob, proved: false, duration_ms: dur, status: elem(other, 0)}
    end
  end

  defp eval_utility(path, prob, base_stats, base_dur, external_lemmas, timeout_ms) do
    lowered = TptpLower.from_file(path)
    base_iters = Map.get(base_stats, :iterations, 0)
    base_passive = Map.get(base_stats, :passive_clauses, 0)

    if external_lemmas == [] do
      %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, passive_diff: 0, note: "No external lemmas in domain"}
    else
      sample_lemmas = Enum.take(external_lemmas, 15)
      {arena, extra_clauses} = import_lemmas(lowered.arena, sample_lemmas)
      all_clauses = lowered.clauses ++ extra_clauses

      t0 = System.monotonic_time(:millisecond)
      res = Prover.prove_clauses(arena, all_clauses, timeout_ms: timeout_ms)
      t1 = System.monotonic_time(:millisecond)
      dur = t1 - t0

      case res do
        {:proved, _steps, stats} ->
          iter_diff = stats.iterations - base_iters
          time_diff = dur - (base_dur * 1000.0)
          passive_diff = stats.passive_clauses - base_passive

          IO.puts("  #{prob.problem}: iters #{base_iters} -> #{stats.iterations} (#{format_diff(iter_diff)}), time #{Float.round(base_dur * 1000.0, 1)}ms -> #{dur}ms (#{format_diff(time_diff)}ms), passive #{base_passive} -> #{stats.passive_clauses}")
          %{problem: prob.problem, iter_diff: iter_diff, time_diff: time_diff, passive_diff: passive_diff}

        {:saturated, _stats} ->
          IO.puts("  #{prob.problem}: SATURATED without proof! (Swamped by #{length(extra_clauses)} lemmas)")
          %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, passive_diff: 0, note: "Saturated"}

        {:resource_out, _stats} ->
          IO.puts("  #{prob.problem}: TIMEOUT with cached lemmas! (Swamped by extra clauses)")
          %{problem: prob.problem, iter_diff: 0, time_diff: timeout_ms * 1.0, passive_diff: 0, note: "Timed out"}

        other ->
          %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, passive_diff: 0, note: inspect(elem(other, 0))}
      end
    end
  end

  defp import_lemmas(%Arena{} = target_arena, lemmas) do
    valid_clauses =
      lemmas
      |> Enum.map(& &1.clause)
      |> Enum.filter(fn clause ->
        Enum.all?(clause, fn {_pol, atom_id} ->
          atom_id < target_arena.next_id
        end)
      end)

    {target_arena, valid_clauses}
  end

  defp count_used_lemmas(steps, extra_clauses) do
    extra_set = MapSet.new(extra_clauses)
    Enum.count(steps, fn
      {:axiom, _id, c} -> MapSet.member?(extra_set, c)
      _ -> false
    end)
  end

  defp format_diff(val) when is_number(val) and val > 0, do: "+#{Float.round(val * 1.0, 2)}"
  defp format_diff(val) when is_number(val), do: "#{Float.round(val * 1.0, 2)}"
end
