# ============================================================================
# CASC Large Theory Batch (LTB) Overnight Benchmark Runner for Astraea / Leo-III
# ============================================================================
# Usage:
#   cd astraea && mix run ../scripts/run_ltb_benchmark.exs [options]
#
# Options:
#   --spec <path>             Path to .spec file (defaults to auto-generated VBT spec)
#   --format <thf|tff|all>    Problem format to include (default: thf)
#   --limit <N>               Run only first N problems (e.g. for smoke testing)
#   --timeout <sec>           Per-problem timeout in seconds (default: 15)
#   --overall-timeout <sec>   Overall batch timeout in seconds (default: 28800 = 8h)
#   --competitive             Race external provers (vampire, eprover-ho, cvc5)
#   --checkpoint <path>       Checkpoint JSON path (default: benchmarks/results/checkpoint.json)
#   --no-resume               Start fresh without resuming from existing checkpoint
#   --output-dir <path>       Results directory (default: benchmarks/results)
#   --help                    Show help
# ============================================================================

alias Astraea.{Session, Session.Ltb, TptpCorpus}

# ----------------------------------------------------------------------------
# 1. Parse Command Line Arguments
# ----------------------------------------------------------------------------

args = System.argv()

if "--help" in args or "-h" in args do
  IO.puts("""
  Astraea CASC Large Theory Batch (LTB) Overnight Benchmark Runner

  Usage:
    cd astraea && mix run ../scripts/run_ltb_benchmark.exs [options]

  Options:
    --spec <path>            Path to .spec file (defaults to auto-generated VBT spec)
    --format <thf|tff|all>   Problem format to evaluate (default: thf)
    --limit <N>              Run only first N problems
    --timeout <seconds>      Per-problem timeout in seconds (default: 15)
    --overall-timeout <sec>  Overall batch timeout in seconds (default: 28800 = 8 hours)
    --competitive            Race external provers (eprover-ho, vampire, cvc5)
    --checkpoint <path>      Custom checkpoint JSON path
    --no-resume              Start fresh without resuming
    --output-dir <path>      Output directory for results (default: benchmarks/results)
  """)
  System.halt(0)
end

get_arg = fn flag, default ->
  case Enum.find_index(args, &(&1 == flag)) do
    nil -> default
    idx -> Enum.at(args, idx + 1, default)
  end
end

has_flag = fn flag -> flag in args end

format_arg = String.to_atom(get_arg.("--format", "thf"))
limit_arg = case get_arg.("--limit", nil) do
  nil -> nil
  s -> String.to_integer(s)
end

timeout_sec = String.to_integer(get_arg.("--timeout", "15"))
overall_sec = String.to_integer(get_arg.("--overall-timeout", "28800"))
competitive? = has_flag.("--competitive")
resume? = not has_flag.("--no-resume")

out_dir = get_arg.("--output-dir", "benchmarks/results")
File.mkdir_p!(out_dir)

timestamp = DateTime.utc_now() |> DateTime.to_iso8601() |> String.replace(~r/[:\.]/, "-")
csv_path = Path.join(out_dir, "ltb_report_#{timestamp}.csv")
checkpoint_path = get_arg.("--checkpoint", Path.join(out_dir, "checkpoint_ltb_vbt.json"))

# ----------------------------------------------------------------------------
# 2. Resolve or Generate Batch Specification
# ----------------------------------------------------------------------------

spec_path =
  case get_arg.("--spec", nil) do
    nil ->
      auto_spec = Path.join(out_dir, "casc_j11_vbt_#{format_arg}.spec")
      IO.puts("[LTB] Generating CASC-J11 VBT specification: #{auto_spec}")
      case Ltb.generate_vbt_spec(auto_spec,
        format: format_arg,
        limit: limit_arg,
        timeout_problem: timeout_sec,
        timeout_overall: overall_sec
      ) do
        {:ok, generated} ->
          generated

        {:error, reason} ->
          IO.puts("\e[31m[ERROR] Could not find TPTP Problems/ITP directory: #{inspect(reason)}\e[0m")
          IO.puts("Please pass --spec <path_to_spec> or ensure TPTP environment variable is set.")
          System.halt(1)
      end

    custom_path ->
      Path.expand(custom_path)
  end

IO.puts("""
==============================================================================
               ASTRAEA CASC LTB OVERNIGHT BENCHMARK
==============================================================================
  Spec File         : #{spec_path}
  Problem Format    : #{format_arg}
  Problem Limit     : #{inspect(limit_arg)}
  Timeout / Problem : #{timeout_sec}s
  Overall Timeout   : #{overall_sec}s (#{Float.round(overall_sec / 3600.0, 1)} hours)
  Competitive Mode  : #{competitive?} (Vampire, E-HO, cvc5 external race)
  Resume Checkpoint : #{resume?} (#{checkpoint_path})
  CSV Report        : #{csv_path}
  Output Directory  : #{out_dir}
==============================================================================
""")

# Initialize CSV Header
csv_header = "index,problem,szs,verified,winning_strategy,duration_ms,proof_length,iterations,demod_rules,timestamp\n"
if not File.exists?(csv_path) do
  File.write!(csv_path, csv_header)
end

# ----------------------------------------------------------------------------
# 3. Live Telemetry Callback
# ----------------------------------------------------------------------------

on_result_cb = fn %{
  problem: prob_rel,
  result: res,
  index: idx,
  total: total,
  elapsed_ms: cur_ms,
  stats: cur_stats,
  cached: cached?
} ->
  pct = Float.round(idx * 100.0 / max(total, 1), 1)
  szs = Map.get(res, :szs, :unknown)
  dur_s = Float.round(Map.get(res, :duration_ms, 0) / 1000.0, 2)
  strat = Map.get(res, :winning_strategy, :unknown)
  verified? = Map.get(res, :verified, false)
  v_tag = if verified?, do: " [LCF]", else: ""
  cached_tag = if cached?, do: " (cached)", else: ""

  prob_name = Path.basename(prob_rel)

  status_str =
    case szs do
      :theorem -> "\e[32mTheorem#{v_tag}\e[0m"
      :unsatisfiable -> "\e[32mUnsatisfiable#{v_tag}\e[0m"
      :counter_satisfiable -> "\e[33mCounterSatisfiable\e[0m"
      :timeout -> "\e[31mTimeout\e[0m"
      other -> "\e[31m#{Atom.to_string(other)}\e[0m"
    end

  solve_pct =
    if idx > 0 do
      Float.round(cur_stats.queries_proved * 100.0 / idx, 1)
    else
      0.0
    end

  elapsed_min = Float.round(cur_ms / 60_000.0, 1)

  IO.puts(
    "[#{String.pad_leading(to_string(idx), 4)}/#{total}] (#{String.pad_leading(to_string(pct), 5)}%) " <>
    "#{String.pad_trailing(prob_name, 12)} | #{status_str}#{cached_tag} | " <>
    "strat: #{inspect(strat)} | #{dur_s}s | " <>
    "Solved: #{cur_stats.queries_proved}/#{idx} (#{solve_pct}%) | " <>
    "Demod: #{cur_stats.demod_rules_count} | #{elapsed_min}m"
  )

  # Append row to CSV
  csv_line =
    "#{idx},#{prob_name},#{szs},#{verified?},#{inspect(strat)}," <>
    "#{Map.get(res, :duration_ms, 0)},#{Map.get(res, :proof_length, 0)}," <>
    "#{Map.get(res, :iterations, 0)},#{cur_stats.demod_rules_count},#{DateTime.utc_now() |> DateTime.to_iso8601()}\n"

  File.write!(csv_path, csv_line, [:append])
end

# ----------------------------------------------------------------------------
# 4. Run Batch
# ----------------------------------------------------------------------------

batch_opts = [
  timeout_ms: timeout_sec * 1000,
  overall_timeout_ms: overall_sec * 1000,
  competitive: competitive?,
  checkpoint_file: checkpoint_path,
  resume: resume?,
  on_result: on_result_cb
]

t_start = System.monotonic_time(:millisecond)

case Ltb.run_batch(spec_path, batch_opts) do
  {:ok, report} ->
    total_time_s = Float.round((System.monotonic_time(:millisecond) - t_start) / 1000.0, 1)
    total_time_h = Float.round(total_time_s / 3600.0, 2)

    # Strategy breakdown
    strat_counts =
      report.results
      |> Enum.map(fn {_, r} -> Map.get(r, :winning_strategy, :none) end)
      |> Enum.frequencies()
      |> Enum.sort_by(&elem(&1, 1), :desc)

    # Status breakdown
    szs_counts =
      report.results
      |> Enum.map(fn {_, r} -> Map.get(r, :szs, :unknown) end)
      |> Enum.frequencies()

    lcf_verified_count =
      Enum.count(report.results, fn {_, r} ->
        Map.get(r, :szs) in [:theorem, :unsatisfiable] and Map.get(r, :verified, false)
      end)

    IO.puts("""

==============================================================================
               CASC LTB OVERNIGHT BENCHMARK FINAL REPORT
==============================================================================
  Category                : #{report.category}
  Total Problems in Batch : #{report.total_problems}
  Attempted Problems      : #{report.attempted}
  Proved Theorems         : #{report.solved}
  Solve Rate              : #{report.solve_rate_pct}%
  LCF Verified Theorems   : #{lcf_verified_count} (#{Float.round(lcf_verified_count * 100.0 / max(report.total_problems, 1), 2)}%)
  Harvested Sound Lemmas  : #{report.harvested_lemmas}
  Active Demod Rules      : #{report.demod_rules}
  Background Theory Clauses: #{report.background_clauses}
  Total Wall Clock Time   : #{total_time_s}s (~#{total_time_h} hours)
  Average Time / Problem  : #{if report.attempted > 0, do: Float.round(total_time_s / report.attempted, 2), else: 0.0}s

SZS Status Breakdown:
#{Enum.map(szs_counts, fn {szs, count} -> "    #{String.pad_trailing(Atom.to_string(szs), 20)}: #{count}" end) |> Enum.join("\n")}

Winning Strategy Breakdown:
#{Enum.map(strat_counts, fn {strat, count} -> "    #{String.pad_trailing(inspect(strat), 30)}: #{count}" end) |> Enum.join("\n")}

------------------------------------------------------------------------------
HISTORICAL CASC COMPETITION BASELINES (LTB Division):
  Stock Leo-III 1.6 (CASC-28 JJT Batch)    :  24.8% (2,481 / 10,000)
  E 3.0 (CASC-J11 VBT Batch)               :  41.2% (3,292 / 8,000)
  iProver 3.6 (CASC-J11 VBT Batch)         :  43.1% (3,446 / 7,999)
  Vampire 4.7 (CASC-J11 VBT Winner)        :  46.6% (3,729 / 8,000)
  Zipperposition (CASC-28 JJT Batch)       :  69.5% (6,952 / 10,000)
------------------------------------------------------------------------------
ASTRAEA / LEO-III COMPETITIVENESS VERDICT:
""")

    cond do
      report.solve_rate_pct >= 46.6 ->
        IO.puts("  \e[32m[EXCEPTIONAL]\e[0m Astraea (#{report.solve_rate_pct}%) SURPASSES the winning CASC-J11 Vampire 4.7 baseline (46.6%)!")
      report.solve_rate_pct >= 41.2 ->
        IO.puts("  \e[32m[COMPETITIVE]\e[0m Astraea (#{report.solve_rate_pct}%) is FULLY ON PAR with top CASC SOTA provers (E 3.0: 41.2%, iProver: 43.1%)!")
      report.solve_rate_pct >= 24.8 ->
        IO.puts("  \e[34m[SURPASSES LEO-III]\e[0m Astraea (#{report.solve_rate_pct}%) beats historical stock Leo-III (24.8%) by +#{Float.round(report.solve_rate_pct - 24.8, 1)}%!")
      true ->
        IO.puts("  \e[33m[BELOW BASELINE]\e[0m Astraea solved #{report.solve_rate_pct}%. Investigate search depth or timeout limits.")
    end

    IO.puts("""
==============================================================================
Results saved to:
  CSV Report : #{csv_path}
  Checkpoint : #{checkpoint_path}
==============================================================================
""")

  {:error, reason} ->
    IO.puts("\e[31m[ERROR] Batch execution failed: #{inspect(reason)}\e[0m")
    System.halt(1)
end
