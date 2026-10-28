# Review of Benchmark Claims and Revised Plan (2026-10-28)

Scope: every comparative or quantitative claim in `thesis_work_log.md` (Entries 004-019), `leo3_baseline.md` and `beating_zipperposition_plan.md`. Nothing on `TPTP-Holdout` was read or run for this review.

## 1. Findings

### 1.1 Problems with the setup

| # | Finding | Evidence | Affects |
|---|---|---|---|
| F1 | The cvc5 on `armix` cannot read TPTP. `~/tools/cvc5/bin/cvc5` (1.4.2) rejects `--lang=tptp` ("unknown language `tptp'"); `--lang help` lists only SMT-LIB and SyGuS. Every cvc5 racer and every cvc5 cooperation call failed. | Run on 2026-10-28 | Entries 008, 009, 014, 015, 017; `leo3_baseline.md` 3.2 |
| F2 | `TPTP-Holdout` is not blind any more. Entry 007 ran it (155 / 398) and logged per-domain and per-strategy counts for it. Everything tuned on Dev after Entry 007 was tuned with that table in the log. | Entry 007, 7.1-7.3 | Gate 3, final thesis numbers |
| F3 | `armix` is never idle. On 2026-10-28 the load average was 24-28 on 14 cores: `perstrat.exs` at about 430% CPU, `/tmp/drop.exs` (running for 8 days), two podman jobs (running for 8 days). `leo3_baseline.md` already reported a load of 6-26. No entry records the load during its run. | `uptime`, `ps` | All 2.5 s numbers |
| F4 | Run-to-run noise on Dev at 2.5 s is about +-5 problems or more, so single runs can't show small differences. Entry 019 measured 108 for 16 strategies without its new rules. Entry 018 measured 118-119 for the same 16 strategies. Leo-III+E at 2.5 s ranged from 65 to 91 across 3 passes. | Entries 018, 019; `leo3_baseline.md` 3.1 | Every delta of fewer than about 6-10 problems |

### 1.2 Claims that do not hold

| Claim | Where | Status | Why |
|---|---|---|---|
| "Competitive CASC Mode: 162 / 237 (68.35%)" | Entry 014 | Misleading | 47 of the 162 are SZS answers from E-HO or Vampire that Astraea did not check. Only 115 are kernel-checked, and 112 of those are solved internally anyway. That 162 measures E-HO + Vampire + Astraea together, not Astraea. |
| "within 2% of cvc5 (~70%)" | Entry 014 | Wrong | (a) cvc5 was a member of the portfolio being compared against cvc5. (b) Because of F1, that member never answered. (c) At CASC-J12, cvc5 1.1.3 solved 299 / 500 THF (59.8%), not about 70%. |
| "within ~3% of cvc5 (~69%)" | Entry 017 | Wrong | Same reasons as above. |
| "ahead of Satallax (~62%)" | Entries 014, 017 | Unsourced | Satallax did not enter CASC-J12, and no source for 62% is given. |
| "Zipperposition 84-88%", "world-champion prover Zipperposition" | Plan, Entry 015 | Partly right | Zipperpin 2.1.9999 solved 433 / 500 THF (86.6%) at CASC-J12. But Vampire won THF at both CASC-J12 (463 / 500, 92.6%) and CASC-30, and E 3.2.0 solved 411 / 500 (82.2%). In any case, CASC problems, time limits and hardware are not Dev at 2.5 s. |
| "surpassing stock Leo-III by +47% (162 vs 110)" | Entry 014 | Wrong comparison | It compares Astraea plus E/Vampire against Leo-III without E. The matching Leo-III figure is Leo-III+E at 10 s, which solved 131. |
| "112 at 2.5 s surpasses stock Leo-III 10 s (110) in 1/4 the time" | Entries 012, 014, plan | Needs a qualifier | Each Astraea problem gets 4 cores, or 14 when problems run one at a time. Leo-III's search loop is sequential. Leo-III also loses about 1.5 s per problem to JVM startup. A per-core or CPU-time comparison would be the fair one. |
| "Positions Astraea ... on the world THF0 ladder" | Entries 014, 017 | Wrong | There is no such ladder. The percentages come from different problems and different setups. |
| CASC LTB baselines ("Leo-III 1.6 24.8% 2,481 / 10,000 in CASC-28 JJT", "Vampire 4.7 46.6% 3,729 / 8,000 in CASC-J11 VBT", and the E and iProver figures) | Entry 016 | Unsourced, likely invented | No source is given. The CASC-28 LTB results page has no such figures. Remove them until each one has a link to a tptp.org results page. |
| "16 strategies: 119 vs 113" | Entry 018 (mine) | Within noise | Entry 019 got 108 for the same 16 strategies. My statement "one problem at a time so each race has all 14 cores" was false, because of F3. The +6 still needs to be shown with repeated runs. |
| "Holdout +4.34 points over Dev, anti-overfitting validation" | Entry 007 | Spent | The number may be right, but see F2. It cannot serve as a blind final number any more. |
| Phase targets "+15 / +6 / +8 / +10 theorems, 205 / 237" | Plan section 4 | Not grounded | Measured: AVATAR gave -1 (111 vs 112, Entry 015). The discrimination tree gave about 0. FluidSup and induction fired 0 times on Dev. The 16-strategy portfolio gave between -5 and +6. |

### 1.3 Claims that hold up

* 0 false proofs on the CounterSatisfiable/Satisfiable traps, and every counted internal proof passes `ProofChecker.verify_refutation/2`. Every entry reports this, and it is checked per problem.
* The `leo3_baseline.md` numbers: Leo-III stock 63 / 110 and Leo-III+E 91 / 131 on Dev at 2.5 s / 10 s. The method is documented, the load is reported and variance was measured.
* The internal Dev progression 82 (Entry 007) to about 108-114 now. The size of the trend is real, apart from the noise in F4.
* Entry 019's attribution: specific problems that only the new rule solves, checked with the rule off.
* Entry 018's attribution: the new rules fired 0 times in the wins of the `fluid` and `induction` strategies.
* Entry 004 microbenchmarks: not re-checked here.

## 2. Where Astraea actually stands

The only figure that measures Astraea is its own kernel-checked count. On Dev at 2.5 s that is about 108-119 / 237 (46-50%), depending on the run. No external prover has been measured on Dev under the same conditions. A standalone E-HO and Vampire run was started on 2026-10-28 and stopped because of F3; it is not used.

## 3. Revised plan

The original plan assumed a 16-20 point gap to close with five features. The measured gap to the provers that matter is unknown, probably large, and the five features did not move Dev. So the plan starts with measurement.

### Phase 0: measurement that can carry a thesis claim

1. **Quiet machine.** Run benchmarks only when no other jobs are running (agree on this, or use `zib`). Each run records the load average at its start and end, and a run is invalid if the 1-minute load exceeded the cores it used.
2. **Repeats.** Do 3 runs per configuration and report the median and the range. A difference only counts if it is larger than the range, or if it is confirmed per problem with the rule switched off (as Entry 019 did).
3. **Equal resources.** Report both wall clock at a fixed core count and total CPU time. For Astraea, run 1-core runs (one strategy, or a sequential schedule) next to the parallel portfolio.
4. **Reference provers on Dev, same machine, same budgets (2.5 s, 10 s, 60 s):**
   * E-HO 3.5.1 and Vampire 5.1, both installed.
   * Zipperposition, to be installed.
   * cvc5, using a build with TPTP input or the CASC wrapper; otherwise drop it.
   * Leo-III (already measured).
5. **Holdout.** Decide whether the Entry 007 run spent the holdout. If it did, freeze a new one from THF0 problems that are in no split (or from problems added in a newer TPTP release), lock its hash, and never run it before the final evaluation.

### Phase 1: report two systems, never mixed

* **Astraea:** internal, kernel-checked. This is the thesis number.
* **Astraea + E/Vampire:** label it that way. Compare it only to its best single member, since the question is whether Astraea adds anything to their union. Never compare it to E, Vampire or cvc5 alone.
* Remove the ladder percentages and the unsourced LTB baselines. Cite CASC results only with a tptp.org link, and only as context, not as a comparison.

### Phase 2: close the gap the data shows

* The work list is the Dev theorems solved by E-HO or Vampire alone and not by Astraea, split by:
  * saturated: a rule is missing (the method of Entry 019);
  * timed out: a search or speed problem.
* The Leo-III gap analysis already ranks the missing rules (`leo3_baseline.md`, section 4). Demodulation was the largest group (27 of 40) and should be re-checked against the current tree.
* Each change is accepted on the per-problem evidence of Phase 0.2, not on the total.

### Phase 3: optional features, off by default

* **Keep (tested, sound, no measured gain):** FluidSup, stated induction, AVATAR.
* **Discrimination tree:** keep. Test it where rule sets are large (LTB), not on Dev.
* **Lemma bus:** a net loss at 2.5 s. Revisit only with a profile of the import path (SEU668^2).
* **Wide portfolio:** repeat 4 vs 16 strategies under Phase 0. If the gain holds, use a schedule fitted on Dev with cross-validation, not a hand-picked 16.

### Targets

Set them after Phase 0.4, as fractions of what E-HO and Vampire solve on Dev under the same conditions. The next defensible bar is Leo-III+E at 10 s (131 / 237), which Astraea has not reached with internal proofs.

Sources: [CASC-J12 results summary](https://tptp.org/CASC/J12/WWWFiles/ResultsSummary.html), [CASC-30 results summary](https://tptp.org/CASC/30/WWWFiles/ResultsSummary.html), [CASC-28 LTB results](https://tptp.org/Seminars/CASC/CASC-28-LONG/ResultsLTB.html).
