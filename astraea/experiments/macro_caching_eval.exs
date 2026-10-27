defmodule Astraea.Experiments.MacroCachingEval do
  @moduledoc """
  Empirical evaluation of:
  1. Proof DAG macro-compression (compressing multi-step primitive inferences into single rules).
  2. Sub-proof / Lemma Caching across theorem proving problems:
     - Analyzing conjecture-dependency of derived sub-proofs in refutations.
     - Extracting sound, theory-derived intermediate lemmas (pure consequences of axioms).
     - Testing whether caching & seeding these lemmas helps solve previously unsolved problems.
     - Measuring the impact on search efficiency (iterations, time, active clauses, swamping effect).
  """

  alias Astraea.{Clausifier, Compressor, External.ThfPrinter, Portfolio, ProofChecker, TptpCorpus, TptpLower, Tstp}

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
    IO.puts("Steps Saved:           #{comp_summary.total_steps_saved} (#{comp_summary.step_reduction_pct}%)")
    IO.puts("Subst Fusions:         #{comp_summary.total_subst_fusions}")
    IO.puts("Structural Dedup:      #{comp_summary.total_dedup_merges}")
    IO.puts("Mined Macro-Patterns:")
    for {macro, count} <- comp_summary.macro_patterns do
      IO.puts("  * #{macro}: #{count}")
    end

    # 3. Analyze Sub-Proof Lineage & Conjecture Dependency
    IO.puts("\n--- Phase 3: Sub-Proof Lineage & Sound Lemma Extraction ---")
    lineage_stats = analyze_proof_lineage(baseline.raw_results)
    IO.puts("Total Derived Steps Across All Proofs: #{lineage_stats.total_derived}")
    IO.puts("  * Conjecture-Dependent Steps:        #{lineage_stats.conj_dependent} (#{lineage_stats.conj_pct}%)")
    IO.puts("  * Sound Background-Axiom Lemmas:     #{lineage_stats.pure_axiom_lemmas} (#{lineage_stats.axiom_pct}%)")

    pure_lemmas_by_domain = lineage_stats.lemmas_by_domain
    for {dom, lemmas} <- pure_lemmas_by_domain do
      IO.puts("  Domain #{dom}: #{length(lemmas)} sound background lemmas extracted")
    end

    # 4. Identify Solved vs Unsolved Problems
    unsolved_theorems =
      baseline.raw_results
      |> Enum.filter(fn {e, status, _} -> is_map(e) and e.status == "Theorem" and not match?({:proved, _, _}, status) end)
      |> Enum.map(&elem(&1, 0))

    solved_theorems =
      baseline.raw_results
      |> Enum.filter(fn {e, status, _} -> is_map(e) and e.status == "Theorem" and match?({:proved, _, _}, status) end)
      |> Enum.map(fn {e, {:proved, steps, stats}, dur} -> {e, steps, stats, dur} end)

    IO.puts("\n--- Phase 4: Cross-Problem Lemma Transfer on Unsolved Problems ---")
    IO.puts("Evaluating if caching sound sub-proof lemmas from solved problems can prove unsolved problems:")
    IO.puts("Unsolved problem count: #{length(unsolved_theorems)}")

    unsolved_transfer_results =
      for prob <- unsolved_theorems do
        path = TptpCorpus.problem_path(prob.problem)
        dom_lemmas = Map.get(pure_lemmas_by_domain, prob.domain, [])
        eval_with_cached_lemmas(path, prob, dom_lemmas, timeout_ms)
      end

    newly_solved = Enum.filter(unsolved_transfer_results, & &1.proved)
    IO.puts("\nNewly Solved with Cached Sub-proofs: #{length(newly_solved)} / #{length(unsolved_theorems)}")
    for res <- newly_solved do
      IO.puts("  [SUCCESS] #{res.problem.problem} solved!")
    end
    if newly_solved == [] do
      IO.puts("  [RESULT] 0 / #{length(unsolved_theorems)} open problems solved by injecting sound domain lemmas.")
    end

    # 5. Search Efficiency & Utility Problem on Solved Problems
    IO.puts("\n--- Phase 5: Search Efficiency Impact on Solved Problems (Utility Problem Test) ---")
    IO.puts("Testing search impact when injecting domain-cached lemmas into already-solved problems:")
    test_sample = Enum.take(solved_theorems, 8)

    utility_results =
      for {prob, _steps, base_stats, base_dur} <- test_sample do
        path = TptpCorpus.problem_path(prob.problem)
        dom_lemmas = Map.get(pure_lemmas_by_domain, prob.domain, [])
        external_lemmas = Enum.reject(dom_lemmas, &(&1.source == prob.problem))

        eval_utility(path, prob, base_stats, base_dur, external_lemmas, timeout_ms)
      end

    valid_diffs = Enum.filter(utility_results, &is_nil(&1[:note]))
    if valid_diffs != [] do
      avg_iter_change =
        Enum.sum(Enum.map(valid_diffs, & &1.iter_diff)) / length(valid_diffs)
      avg_time_change =
        Enum.sum(Enum.map(valid_diffs, & &1.time_diff)) / length(valid_diffs)

      IO.puts("\nSummary of Search Impact across #{length(valid_diffs)} test theorems:")
      IO.puts("  Average Iteration Change: #{Float.round(avg_iter_change, 2)} iterations")
      IO.puts("  Average Time Change:      #{Float.round(avg_time_change, 2)} ms")
    end

    %{
      baseline: baseline,
      comp_summary: comp_summary,
      lineage_stats: lineage_stats,
      unsolved_transfer_results: unsolved_transfer_results,
      utility_results: utility_results
    }
  end

  defp analyze_proof_lineage(raw_results) do
    Enum.reduce(
      raw_results,
      %{total_derived: 0, conj_dependent: 0, pure_axiom_lemmas: 0, lemmas_by_domain: %{}},
      fn
        {entry, {:proved, steps, stats}, _ms}, acc when is_map(entry) and entry.status == "Theorem" ->
          path = TptpCorpus.problem_path(entry.problem)
          domain = entry.domain

          case TptpLower.from_file(path) do
            {:ok, lowered} ->
              # Compute keys of true background axioms
              {ax_arena, ax_clauses} = Clausifier.clausify(%{lowered | conjectures: []}, sine_limit: nil)
              axiom_keys = MapSet.new(ax_clauses, &Tstp.clause_key(ax_arena, &1))

              # Build step graph
              steps_map = Map.new(steps, fn s -> {elem(s, 1), s} end)

              # Trace ancestor axiom ids for every step
              axiom_sources =
                Enum.reduce(steps, %{}, fn step, m ->
                  id = elem(step, 1)
                  case step do
                    {:axiom, _, clause} ->
                      key = Tstp.clause_key(stats.arena, clause)
                      is_axiom? = MapSet.member?(axiom_keys, key)
                      Map.put(m, id, if(is_axiom?, do: :axiom, else: :conjecture))

                    _other ->
                      m
                  end
                end)

              # Trace dependency for derived steps
              case ProofChecker.derive_steps(stats.arena, steps) do
                {:ok, _ar, derived_map} ->
                  derived_steps = Enum.reject(steps, &(elem(&1, 0) == :axiom))

                  {c_dep, p_lemmas} =
                    Enum.reduce(derived_steps, {0, []}, fn step, {cd, pl} ->
                      id = elem(step, 1)
                      clause = Map.get(derived_map, id, MapSet.new())

                      if MapSet.size(clause) == 0 do
                        {cd + 1, pl}
                      else
                        ancestors = collect_ancestors(steps_map, [id], MapSet.new())
                        touches_conj? =
                          Enum.any?(ancestors, fn anc_id ->
                            Map.get(axiom_sources, anc_id) == :conjecture
                          end)

                        if touches_conj? do
                          {cd + 1, pl}
                        else
                          thf_str =
                            try do
                              ThfPrinter.clause_to_string(stats.arena, clause)
                            rescue
                              _ -> nil
                            end

                          if thf_str do
                            lemma = %{
                              id: id,
                              clause: clause,
                              thf: thf_str,
                              is_unit: MapSet.size(clause) == 1,
                              source: entry.problem
                            }
                            {cd, [lemma | pl]}
                          else
                            {cd, pl}
                          end
                        end
                      end
                    end)

                  new_lemmas_by_domain =
                    if p_lemmas != [] do
                      Map.update(acc.lemmas_by_domain, domain, p_lemmas, &(&1 ++ p_lemmas))
                    else
                      acc.lemmas_by_domain
                    end

                  %{
                    acc
                    | total_derived: acc.total_derived + length(derived_steps),
                      conj_dependent: acc.conj_dependent + c_dep,
                      pure_axiom_lemmas: acc.pure_axiom_lemmas + length(p_lemmas),
                      lemmas_by_domain: new_lemmas_by_domain
                  }

                _ ->
                  acc
              end

            _ ->
              acc
          end

        _other, acc ->
          acc
      end
    )
    |> finalize_lineage_stats()
  end

  defp finalize_lineage_stats(st) do
    tot = max(st.total_derived, 1)
    Map.merge(st, %{
      conj_pct: Float.round(st.conj_dependent * 100.0 / tot, 2),
      axiom_pct: Float.round(st.pure_axiom_lemmas * 100.0 / tot, 2)
    })
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

  defp eval_with_cached_lemmas(path, prob, dom_lemmas, timeout_ms) do
    original_source = File.read!(path)

    candidate_lemmas =
      dom_lemmas
      |> Enum.filter(& &1.is_unit)
      |> Enum.take(10)

    if candidate_lemmas == [] do
      IO.puts("  #{prob.problem}: No compatible sound domain lemmas in cache.")
      %{problem: prob, proved: false, note: "No sound domain lemmas"}
    else
      lemma_lines =
        candidate_lemmas
        |> Enum.with_index()
        |> Enum.map(fn {lem, idx} ->
          "thf(cached_lem_#{idx}, axiom, #{lem.thf})."
        end)
        |> Enum.join("\n")

      augmented_src = original_source <> "\n% --- CACHED LEMMAS ---\n" <> lemma_lines

      case TptpLower.from_string(augmented_src) do
        {:ok, lowered} ->
          t0 = System.monotonic_time(:millisecond)
          res = Portfolio.prove_lowered(lowered, timeout_ms: timeout_ms)
          dur = System.monotonic_time(:millisecond) - t0

          case res do
            {:proved, steps, stats} ->
              strat = Map.get(stats, :winning_strategy, Map.get(stats, :strategy, :unknown))
              IO.puts("  #{prob.problem}: PROVED with #{length(candidate_lemmas)} cached lemmas in #{strat}! (#{dur}ms)")
              %{problem: prob, proved: true, duration_ms: dur, iterations: Map.get(stats, :iterations, 0), steps: length(steps)}

            _ ->
              IO.puts("  #{prob.problem}: Still unsolved with #{length(candidate_lemmas)} cached lemmas.")
              %{problem: prob, proved: false, duration_ms: dur}
          end

        {:error, reason} ->
          IO.puts("  #{prob.problem}: Lemma signature mismatch (#{inspect(reason)}), skipping.")
          %{problem: prob, proved: false, note: "Signature mismatch"}
      end
    end
  end

  defp eval_utility(path, prob, base_stats, base_dur, external_lemmas, timeout_ms) do
    base_iters = Map.get(base_stats, :iterations, 0)
    original_source = File.read!(path)

    candidate_lemmas =
      external_lemmas
      |> Enum.filter(& &1.is_unit)
      |> Enum.take(5)

    if candidate_lemmas == [] do
      IO.puts("  #{prob.problem}: No sound external lemmas in domain to inject.")
      %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, note: "No sound external lemmas"}
    else
      lemma_lines =
        candidate_lemmas
        |> Enum.with_index()
        |> Enum.map(fn {lem, idx} ->
          "thf(cached_lem_#{idx}, axiom, #{lem.thf})."
        end)
        |> Enum.join("\n")

      augmented_src = original_source <> "\n% --- CACHED LEMMAS ---\n" <> lemma_lines

      case TptpLower.from_string(augmented_src) do
        {:ok, lowered} ->
          t0 = System.monotonic_time(:millisecond)
          res = Portfolio.prove_lowered(lowered, timeout_ms: timeout_ms)
          dur = System.monotonic_time(:millisecond) - t0

          case res do
            {:proved, _steps, stats} ->
              iters = Map.get(stats, :iterations, 0)
              iter_diff = iters - base_iters
              time_diff = dur - (base_dur * 1000.0)

              IO.puts("  #{prob.problem}: iters #{base_iters} -> #{iters} (#{format_diff(iter_diff)}), time #{Float.round(base_dur * 1000.0, 1)}ms -> #{dur}ms (#{format_diff(time_diff)}ms)")
              %{problem: prob.problem, iter_diff: iter_diff, time_diff: time_diff}

            {:saturated, _stats} ->
              IO.puts("  #{prob.problem}: SATURATED without proof! (Swamped by #{length(candidate_lemmas)} lemmas)")
              %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, note: "Saturated"}

            {:resource_out, _stats} ->
              IO.puts("  #{prob.problem}: TIMEOUT with cached lemmas! (Swamped by extra clauses)")
              %{problem: prob.problem, iter_diff: 0, time_diff: timeout_ms * 1.0, note: "Timed out"}

            other ->
              %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, note: inspect(elem(other, 0))}
          end

        {:error, _reason} ->
          IO.puts("  #{prob.problem}: Injected lemmas signature mismatch.")
          %{problem: prob.problem, iter_diff: 0, time_diff: 0.0, note: "Signature mismatch"}
      end
    end
  end

  defp format_diff(val) when is_number(val) and val > 0, do: "+#{Float.round(val * 1.0, 2)}"
  defp format_diff(val) when is_number(val), do: "#{Float.round(val * 1.0, 2)}"
end
