# Plan: Honest Benchmarking and Closing the Gap (2026-10-28)

Replaces the targets in `beating_zipperposition_plan.md`. Background: `claims_review.md`. Each work package (WP) below is meant to be started in a fresh session: paste the session preamble, then the WP.

## Session preamble (paste at the start of every session)

> Work on Astraea (`astraea/`, branch `astraea`), the pure-Elixir higher-order prover with an LCF kernel. Read `Notes/benchmark_and_gap_plan.md` (this plan) and `Notes/claims_review.md` first. Rules:
> - Pure Elixir, no new Rust; hot loops may go through NxSimd.
> - Every counted Astraea theorem must pass `Astraea.ProofChecker.verify_refutation/2`.
> - 0 false theorems on the CounterSatisfiable/Satisfiable traps.
> - Never run, read or inspect `TPTP-Holdout` (or the new holdout from WP4).
> - Benchmark on `armix` only after `uptime` shows a 1-minute load below 2, and ask the user before starting. Other people's jobs run there. Kill processes by PID, never with `pkill -f` patterns that also match your own ssh command.
> - Don't claim a difference smaller than the noise band from WP3.
> - Keep the internal, kernel-checked Astraea number separate from any run with external provers.
> - Log results as a new entry in `Notes/thesis_work_log.md`.
> - Commit only when asked.
>
> Now do work package WP<n>.

## Facts every session needs

| Item | Value |
|---|---|
| Bench machine | `armix`: 14-core ARM Neoverse-N1, shared. TPTP at `~/.local/share/tptp/TPTP-v9.3.1`. |
| Elixir env on armix | `PATH=$HOME/.asdf/shims:$PATH MIX_ENV=prod ELIXIR_ERL_OPTIONS=+fnu` |
| Splits | `benchmarks/manifests/tptp_thf0_{smoke,dev}.txt`, hash-locked in `manifest_lock.json`. Dev has 237 theorems and 60 CounterSatisfiable/Satisfiable traps. |
| Difficulty | The `rating` column in `benchmarks/manifests/thf_catalog.csv`: the share of state-of-the-art provers that fail on a problem. On Dev, 32 theorems have rating 1.00, so the best possible result is 205. An average state-of-the-art prover is expected to solve about 146 (the sum of 1 - rating). |
| Installed provers | E-HO 3.5.1 (`~/tools/eprover-ho`), E 3.5.1, Vampire 5.1.0, Leo-III 1.8.1 (`~/tools/leo3`). The cvc5 1.4.2 in `~/tools/cvc5` cannot read TPTP. Zipperposition is not installed. |
| Existing scripts | `scripts/astraea_eval_split.exs` (`--width`, `--csv`, `--competitive`), `mix external.eval`, `scripts/leo3_run.py`, `scripts/leo3_gap.py`. |
| Astraea now (Dev, 2.5 s, loaded machine) | About 108-119 / 237 internal; noise about +-5. By rating: 30/32 at 0.00, 80/116 at 0.01-0.33, 6/35 at 0.34-0.67, 2/22 at 0.68-0.99, 0/32 at 1.00. |

## Dependency order

```
WP1 harness ─┐
WP2 provers ─┼─> WP3 baselines ─> WP5 triage ─> WP6 rules / WP7 speed / WP8 selection ─> WP9 schedule
WP4 holdout (user decision, can run in parallel)                      WP10 write-up (after WP3, then rolling)
```

WP1, WP2 and WP4 can run in parallel sessions. WP6 and WP7 can also run in parallel once WP5 exists.

---

## WP1: Reference benchmark harness

**Goal:** one script that runs any prover, or Astraea in a given mode, on a split with identical conditions and writes one CSV row per problem and run.

**Build:** `scripts/reference_eval.py`, which runs on armix. Python 3 with the standard library only; style as in `scripts/leo3_run.py`.

* **Prover adapters:**
  * E-HO, Vampire, Zipperposition, cvc5 and Leo-III, each with its proper higher-order mode. WP2 verifies the exact flags.
  * Astraea in two modes, both through a small entry script around `Astraea.Portfolio`:
    * `astraea-1core`: `ELIXIR_ERL_OPTIONS="+fnu +S 1"`, with the strategies run as a time-sliced sequence instead of a race (add `Portfolio`/`Schedule` support if missing);
    * `astraea-Ncore`: the parallel portfolio.
  * Astraea is started once per problem as an OS process, so BEAM startup counts just as JVM startup does for Leo-III. A warm-session variant may be reported separately, labelled.
* **Resources:** each prover process is pinned with `taskset -c <cores>`. The one-core track uses 1 core per problem; the N-core track uses N cores (default 4) for every prover (`vampire --cores N`, E's multi-core `--auto-schedule=N`, Astraea `+S N`). Concurrency is 14 / cores.
* **Time:** wall-clock limit from process start, `timeout -s KILL`. Also record user+sys CPU of the process tree (`/usr/bin/time -f` or `wait4`).
* **Load gate:** record the 1-minute load at start and end and every 60 s. Mark the run `INVALID` if the load exceeded the cores in use (plus 1).
* **Output CSV:** `run_id, prover, version, track, cores, limit_s, repeat, problem, expected_status, rating, szs_status, wall_ms, cpu_ms, load_start, load_end`. For Astraea also: `lcf_verified`, `winner`, `per_strategy` (see WP5).
* **Scoring:**
  * A theorem counts if the SZS status is Theorem, Unsatisfiable or ContradictoryAxioms on a problem whose expected status allows it.
  * Any Theorem answer on a CounterSatisfiable/Satisfiable problem counts as unsound and is reported in red.
  * Astraea counts only with `lcf_verified=true`.
* **Report script:** `scripts/reference_report.py`. Per configuration: median and range over repeats, solves by rating bucket, unique solves, the union, a pairwise McNemar test between any two configurations, and cactus-plot data (solved vs time).
* **Holdout guard:** refuse any manifest except Smoke and Dev unless `--final` is given together with the hash from `manifest_lock.json`.

**Done when:**
* It runs on Smoke locally on macOS, for the provers that are present, plus Astraea.
* Its unit check of the SZS parsing passes on recorded outputs.
* A dry run prints the commands for all adapters.
* No armix timing run yet.

## WP2: Install and verify the reference provers on armix

**Goal:** every reference prover runs in its strongest higher-order configuration, which you verify yourself.

* **Zipperposition:** opam is not installed. Try opam in user space (`bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"` with a user prefix), then `opam install zipperposition`. Otherwise build from source. Use the CASC portfolio script if it is available (`zipperposition` ships a `portfolio` mode, also used at CASC). Record the version.
* **cvc5:** find a build that accepts `--lang=tptp`, or the CASC wrapper that converts the input. If no ARM build reads TPTP, drop cvc5 and say so in the log.
* **Vampire 5.1:** confirm the higher-order schedule. Compare `--mode casc` with `--mode portfolio --schedule snake_tptp_hol` (or whatever the 5.x CASC THF script uses) on 20 Dev problems.
* **E-HO 3.5.1:** compare `--auto-schedule` with the CASC THF command line on the same 20.
* Check each prover's output on 3 known theorems and 3 known CounterSatisfiable problems from Smoke.

**Done when:** the adapters in WP1 use the verified flags, and a table of prover, version, exact command and source of the command is in the work log.

## WP3: Baseline measurement

**Goal:** the first comparable numbers. Needs WP1 and WP2, and an idle armix or `zib`.

* **Matrix:** provers {E-HO, Vampire, Zipperposition, cvc5 if available, Leo-III, Astraea} × tracks {1 core, 4 cores} × limits {2.5, 10, 60 s} × 3 repeats, on Dev. Start with 2.5 s and 10 s. At 60 s Dev takes about 4 h per prover-track on 1 core at 14-way concurrency; schedule it overnight.
* Also run Astraea plus E/Vampire (competitive mode), labelled as such, and compare it only to its best single member.
* **Noise band:** derive it from the 3 repeats per configuration. It becomes the threshold for every later claim.

**Done when:** there is a work-log entry with the tables (solves by rating bucket, cactus data, unique solves, traps), the noise band, the load records, and a short honest statement of where Astraea stands per track and time limit.

## WP4: Holdout decision and freeze (needs the user)

Entry 007 ran `TPTP-Holdout` and logged per-domain and per-strategy results, so it is no longer blind.

* **Ask the user:** keep it with that caveat stated, or freeze a new one. Recommendation: freeze a new one.
* **If new:**
  * Select THF0 problems that appear in no existing split, stratified by domain and rating like Dev, at least 300 theorems plus traps.
  * Write `tptp_thf0_holdout2.txt` with a single script whose output is not printed, and record its sha256 in `manifest_lock.json`.
  * Mark the old holdout as burned in `tptp_test_plan.md`.
  * Nobody looks at the list.
* The final evaluation runs the frozen Astraea configuration once, with the WP1 harness, `--final`.

## WP5: Gap triage with results per strategy

**Goal:** know why each missed theorem fails, instead of guessing from the portfolio's result.

* Add a per-strategy mode to `scripts/astraea_eval_split.exs` (or to the WP1 Astraea entry): run each strategy alone for the full limit, one core, and record `{strategy, result, ms, iterations, passive_size}`.
* **Gap set:** Dev theorems that E-HO, Vampire or Zipperposition solve at 10 s (WP3) and Astraea does not. Until WP3 exists, use rating ≤ 0.67.
* **Classes**, computed by `scripts/gap_triage.py`:
  * **A, missing rule:** a strategy without axiom selection (`complete_saturation`, `sine_limit: nil`) saturates.
  * **B, selection:** only strategies with SInE saturate, and complete ones time out.
  * **C, search or speed:** every strategy times out or runs out of resources.
  * **D, front end:** lowering, parse or type errors.
  * **E, kernel:** a proof was found but rejected by `verify_refutation/2`. Treat as a bug, top priority.
* Attach the reference prover's proof (E or Vampire TSTP output, inference names) to each A and C problem: `benchmarks/results/gap_proofs/`.

**Done when:** there is a CSV and a work-log table of the gap set by class and rating bucket, rerun on the current tree.

Starting point (before Entry 019, 16 strategies, 2.5 s): 38 theorems with rating ≤ 0.33 were missed. 29 ended `saturated` in the portfolio and 9 `resource_out`. Only SYN983^1, SYO026^1 and SYO515^1 saturated fast; most others saturated at about 2.7 s, which points to class B or C, not A.

## WP6: Missing rules (class A)

The method of Entry 019, one rule per session:

1. Pick the class-A problems that share a rule in the reference proofs.
2. Implement the rule as a composition of existing kernel steps; a kernel change needs explicit user approval.
3. Write tests: the problem from source, proved only with the rule on, and a trap check.
4. Measure per problem, with the rule on and off, 3 repeats. Then do one full Dev run to check that nothing else is lost.
5. Turn the rule on by default only if the full Dev result does not get worse beyond the noise band.

Known candidates:
* Constraint resolution, for SYO026^1. It is implemented but off because its active-set scan is slow, so it needs an index.
* SYO515^1.
* The demodulation, choice, extensionality and pre-unification gaps from `leo3_baseline.md` section 4, re-checked against the current tree.

## WP7: Throughput (class C)

* **Measure** processed clauses per second and generated clauses per second for Astraea against E-HO, using E's `--print-statistics`, on 10 class-C problems. Also measure where Astraea spends its time (`:eprof` or `:tprof`): unification, subsumption, demodulation, indexing or kernel replay.
* **Fix the largest item first:**
  * Index subsumption and unification partners (fingerprint or feature-vector indexing, with NxSimd for the vector scan; see Entry 004).
  * Avoid repeated kernel replays during search.
* **Acceptance:** at least 2x throughput on the class-C sample, and Dev at 10 s not worse.

## WP8: Axiom selection (class B)

* For class-B problems, find which needed axioms SInE dropped: compare against the axioms used in the reference prover's proof.
* Then tune the SInE parameters (tolerance, depth, generality), or add a strategy that relaxes selection after saturation instead of giving up. When a SInE strategy saturates, restart it with a wider selection within the remaining time.
* **Acceptance:** per problem, as in WP6.

## WP9: Strategy schedule

* Only after WP6-WP8 have changed the strategy set.
* Fit a time-sliced schedule (for the one-core track) and a parallel set (for the N-core track) on Dev from per-strategy results (WP5 data). Use 5-fold cross-validation over Dev problems, and report the fold-held-out score, not the training score.
* Replace the hand-picked `wide_strategies(16)` only if the cross-validated score beats it beyond the noise band.

## WP10: Write-up and claim hygiene

* Add a correction note to Entries 007, 014, 016 and 017, pointing to `claims_review.md`. Don't rewrite history; annotate it.
* Remove the unsourced CASC/LTB percentages from the notes. Cite CASC results only with a tptp.org link, and only as context.
* **Thesis framing:** the claim the data can carry is "certified proofs, X% of what E/Vampire/Zipperposition solve under equal resources". Also compare against other provers whose proofs can be checked independently (Satallax/Lash, Leo-III with proof output) on the certified-proof axis.

## How progress is reported

For every change, one line in its work-log entry: track, limit, Dev theorems as median [min-max] over 3 repeats, trap result, problems gained and lost (per problem, confirmed with the rule off), and the load during the run. Every comparison is against the WP3 reference numbers at the same track and limit.
