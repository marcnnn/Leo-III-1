# Leo-III Baseline on TPTP-Smoke and TPTP-Dev, and the Gap to Astraea

Date: 2026-10-26/27 (armix). Source commit of both provers: `b63f03e0`.
TPTP-Holdout was not run, read or used in any way.

## Summary

* Leo-III 1.8.1 was built from this repository's `src/` (it carries local changes such as `--instantiate-sets`, so no release jar was used) and installed at `armix:~/tools/leo3/bin/leo3`.
* At 2.5 s wall clock per problem, Astraea's baseline portfolio solves more than stock Leo-III: Dev 82 vs 63, Smoke 27 vs 19. Leo-III pays about 1.5 s of JVM startup, parsing and JIT warm-up before it can answer anything: no problem was solved in under 1.45 s wall. Astraea's median solve time is 10 ms.
* With more time the order flips. At 10 s, stock Leo-III solves 110 of 237 Dev theorems and Leo-III+E solves 131. Astraea's baseline gains almost nothing from the extra time (82 to 84). The gap is in the calculus and search, not in the time budget.
* 58 THM problems are solved by some Leo-III configuration and not by Astraea's baseline at 2.5 s. 40 of them are solved by Leo-III on its own (calculus/search gap) and 18 only with E. None is explained by "Astraea just needs more time".
* Within the 40 calculus/search problems, the Leo-III proofs use: unit rewriting (demodulation) in 27, choice in 8, pre-unification beyond patterns in 6, Boolean extensionality in 6, functional extensionality in 5, special instances in 5, primitive substitution in 2. 3 proofs use none of these.
* 14 THM problems are solved by Astraea (some configuration) and by no Leo-III configuration. Astraea's baseline portfolio solves 7 of them (5 at 2.5 s, 2 more at 10 s); the other 7 need Astraea's external racers or cooperation.
* No configuration of either prover claimed a theorem on a CounterSatisfiable or Satisfiable problem.

## 1. Installation of Leo-III on armix

[`scripts/leo3_build.sh`](../scripts/leo3_build.sh) does everything in user space:

1. Temurin JDK 21 (21.0.13, aarch64) into `~/tools/jdk`, from the Adoptium API.
2. sbt 1.13.0 launcher into `~/tools/sbt` (the project pins `sbt.version=1.13.0`, Scala 3.9.0).
3. `rsync` of `build.sbt`, `Makefile`, `project/` and `src/` to `~/tools/leo3/src`, then `sbt -batch assembly` (70 s on armix).
4. The jar is copied to `~/tools/leo3/bin/leo3.jar`. The launcher `~/tools/leo3/bin/leo3` runs it with the JVM flags of `src/main/resources/scripts/exec_dummy` (`-Xss32m -Xmx1g`) and the absolute JDK path, plus optional `$LEO3_JAVA_ARGS`.

picosat (`contrib/picosat-965.tar.gz`) is not referenced by the current sources or the Makefile and was not built. `leo3 --version` prints `Leo-III 1.8.1`. Spot checks with `-t 10 -p`: `SET014^4` Theorem in 2.1 s, `SYO088^5` Theorem in 1.9 s, `LCL621^1` Timeout. `leo3 --version` alone takes 0.59 s wall, which is the bare JVM startup.

E is the existing `~/tools/eprover/bin/eprover`, E 3.5.1. Its `--version` reports a `-DEBUG` build, so it is likely slower than a release build.

## 2. Method

**Leo-III runner.** [`scripts/leo3_run.py`](../scripts/leo3_run.py) runs `leo3 <problem> -t ceil(T) -p`, plus `--atp e=~/tools/eprover/bin/eprover` for the E configuration, with `TPTP` set. Each problem gets a hard wall-clock budget of T seconds from process start, so JVM startup counts. Leo-III's `-t` only takes whole seconds, so the process group is SIGKILLed at T. A THM problem counts as solved if the SZS status `Theorem` (or `Unsatisfiable`/`ContradictoryAxioms`) line was printed before the kill. "Proof" means the complete `SZS output start ... end` block was printed: a few problems print the status and are then killed while printing the proof. CPU time is user+sys of Leo-III and its children (E) from `wait4`. Leo-III's self-reported time (counted from JVM `main`, so without JVM startup) and its time without parsing are also recorded.

**Concurrency.** 4 Leo-III problems in parallel. Leo-III used 1.55-1.98 CPU seconds per wall second (JIT, GC and E), so about 7 cores. Astraea ran with `--concurrency 2` as requested. Each Astraea problem runs 4 internal strategies in parallel (plus external provers in the racer configurations), so Astraea also used up to about 8 cores. **The two systems do not get the same CPU per problem**: Astraea gets up to 4 cores per problem, Leo-III's search loop is sequential.

**Machine load.** Other agents benchmarked on armix at the same time (14 cores). Measured 1-minute load average: 9-17 during the first Leo-III pass, 6-26 (median 16.5) during the Astraea 2.5 s runs, about 11 (1.5-13.7) during the second Leo-III 2.5 s pass. At its worst, a trivial problem took 3.2 s wall but only 2.2 s CPU, so CPU starvation was real at times.

**Astraea.** `mix external.eval` from a synced copy at `armix:~/Projects/wt/baseline/`, all configurations at 2.5 s, baseline also at 10 s. Two configurations were added to `mix external.eval` for this report (section 5): `leo3_racer` and `leo3`. Solved means an LCF-verified proof, as in Entries 007/008.

## 3. Results

THM counts: Smoke has 34 Theorem problems, Dev has 237. The CSA/SAT traps are 15 on Smoke and 60 on Dev; the ContradictoryAxioms problems (1 and 3) are counted in neither.

### 3.1 Leo-III

| Split | Config | 2.5 s wall: solved (proofs) | 10 s wall: solved (proofs) | Median wall of solved, 10 s run | CSA/SAT traps: false Theorem |
| :--- | :--- | ---: | ---: | ---: | ---: |
| Smoke | stock | 19 (19) | 25 (25) | 2.18 s | 0 / 15 |
| Smoke | + E | 23 (23) | 30 (30) | 2.80 s | 0 / 15 |
| Dev | stock | 63 (61) | 110 (110) | 3.07 s | 0 / 60 |
| Dev | + E | 91 (88) | 131 (129) | 3.15 s | 0 / 60 |

Leo-III answered CounterSatisfiable/Satisfiable on none of the traps; it has no model finder in this setup. The Smoke+E 10 s run solved `SWW473^1`, which is a ContradictoryAxioms problem, so that answer is correct.

**Run-to-run variance at 2.5 s.** The 2.5 s runs were repeated:

| Split | Config | Pass 1 | Pass 2 | Pass 3 |
| :--- | :--- | ---: | ---: | ---: |
| Smoke | stock | 19 (a trial run before pass 1: 20) | 20 | |
| Smoke | + E | 23 | 18 | |
| Dev | stock | 63 | 61 | |
| Dev | + E | 91 | 65 | 86 |

Stock Leo-III is stable within 2-3 problems. Leo-III+E at 2.5 s is not. E's answer arrives at about 1.8-2.3 s, right at the budget. In pass 2, E answered in 43 problems instead of 59, and `LCL584^1` (solved in 1.8 s in pass 1) was killed at 2.5 s with only 2.3 s CPU. Run alone, it solved 4 out of 4 times at 2.5 s. Treat the 2.5 s E numbers as a range: 65-91 on Dev.

**JVM startup and the 2.5 s budget.** The same 10 s runs, cut at 2.5 s by different clocks:

| Split | Config | 2.5 s wall run | 10 s run: Leo-III time <= 2.5 s (no JVM startup) | 10 s run: time w/o parsing <= 2.5 s | 10 s run: CPU <= 2.5 s | 10 s wall run |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| Smoke | stock | 19 | 19 | 21 | 6 | 25 |
| Smoke | + E | 23 | 15 | 27 | 6 | 30 |
| Dev | stock | 63 | 50 | 78 | 20 | 110 |
| Dev | + E | 91 | 53 | 97 | 7 | 131 |

* The gap between Leo-III's own time and wall time (JVM start before `main`) has a median of 0.24-0.43 s. Parsing (TPTP parser plus includes, cold JIT) adds a median of about 0.6-1.0 s. The fastest solve in any run took 1.45 s wall.
* Excluding startup and parsing, stock Leo-III would solve 78 Dev problems within 2.5 s of reasoning, against 63 under the wall-clock budget.
* Columns 3 and 4 come from runs with `-t 10`. Leo-III schedules its strategies and E calls relative to `-t`, and these runs saw higher load (about 17), so they are not a clean "same run, other clock" view. The low "Leo-III time <= 2.5 s" count for E (53 vs 91) mostly reflects that E is called later under `-t 10`.
* CPU <= 2.5 s is a bad fit for Leo-III. The JVM spends CPU on JIT and GC threads, so even trivial problems use 2.3-3 CPU seconds.

### 3.2 Astraea (`mix external.eval`, concurrency 2)

| Split | Config | Timeout | LCF-verified solved | Externally assisted (LCF) | Unverified external only | CSA/SAT false proofs |
| :--- | :--- | :---: | ---: | ---: | ---: | ---: |
| Smoke | baseline | 2.5 s | 27 | 0 | 0 | 0 / 15 |
| Smoke | racers (E-HO, Vampire, cvc5) | 2.5 s | 30 | 4 | 4 | 0 / 15 |
| Smoke | cooperate (E-HO) | 2.5 s | 27 | 2 | 0 | 0 / 15 |
| Smoke | leo3_racer | 2.5 s | 27 | 0 | 0 | 0 / 15 |
| Smoke | leo3 (standalone) | 2.5 s | 0 | 0 | 2 | 0 / 15 |
| Smoke | baseline | 10 s | 27 | 0 | 0 | 0 / 15 |
| Smoke | leo3_racer | 10 s | 27 | 0 | 1 | 0 / 15 |
| Smoke | leo3 (standalone) | 10 s | 0 | 0 | 25 | 0 / 15 |
| Dev | baseline | 2.5 s | 82 | 0 | 0 | 0 / 60 |
| Dev | racers | 2.5 s | 91 | 13 | 60 | 0 / 60 |
| Dev | cooperate | 2.5 s | 88 | 13 | 0 | 0 / 60 |
| Dev | leo3_racer | 2.5 s | 82 | 0 | 11 | 0 / 60 |
| Dev | leo3 (standalone) | 2.5 s | 0 | 0 | 58 | 0 / 60 |
| Dev | baseline | 10 s | 84 | 0 | 0 | 0 / 60 |

Baseline, racers and cooperate reproduce Entry 008: 82/91/88 on Dev, 27/30/27 on Smoke. Racers lost 2 against Entry 008's 93, which is within the load noise. The median wall time of Astraea baseline solves is 10 ms on Dev.

### 3.3 Head to head

| Split | Comparison | Both | Only Astraea | Only Leo-III |
| :--- | :--- | ---: | ---: | ---: |
| Smoke | Astraea baseline 2.5 s vs Leo-III stock 2.5 s | 19 | 8 | 0 |
| Smoke | Astraea racers 2.5 s vs Leo-III+E 2.5 s | 22 | 8 | 1 |
| Dev | Astraea baseline 2.5 s vs Leo-III stock 2.5 s | 49 | 33 | 14 |
| Dev | Astraea racers 2.5 s vs Leo-III+E 2.5 s | 63 | 28 | 28 |

| Split | Leo-III stock, any timeout | Leo-III, any config | Astraea baseline, any timeout | Astraea, any LCF config | Union |
| :--- | ---: | ---: | ---: | ---: | ---: |
| Smoke (34) | 25 | 30 | 27 | 30 | 33 |
| Dev (237) | 110 | 132 | 84 | 97 | 143 |

## 4. Gap analysis

Per-problem data: [`benchmarks/results/leo3_gap.csv`](../benchmarks/results/leo3_gap.csv). Leo-III output for every gap problem: [`benchmarks/results/leo3_gap_proofs/`](../benchmarks/results/leo3_gap_proofs/). Rule counts of every Leo-III proof: [`benchmarks/results/leo3_proof_features.csv`](../benchmarks/results/leo3_proof_features.csv). Produced by [`scripts/leo3_gap.py`](../scripts/leo3_gap.py).

**Method.** The gap set is the THM problems that some Leo-III run (stock or E, 2.5 s or 10 s) solves and the Astraea baseline at 2.5 s does not. Each gets a class:

* *more search time*: Astraea's baseline solves it at 10 s. This matched **0** problems. Astraea's two extra 10 s solves (`NUM417^1`, `SWV431^2`) are not solved by Leo-III.
* *external cooperation (E)*: stock Leo-III never solves it and the Leo-III+E output says `External prover 'e' found a proof`.
* *calculus/search*: everything else. Here Leo-III finds a proof on its own; two of these were solved only in an E run, but without E's help, which is run-to-run variance.

Features come from the inference names in the TSTP proof. The stock 10 s proof is preferred, then stock 2.5 s, then E. Leo-III rule name to feature:

| Feature | Leo-III rules |
| :--- | :--- |
| choice | `choice` |
| primitive substitution | `prim_subst` |
| pre-unification beyond patterns | `pre_uni`, `flex_uni` (Astraea has pattern unification, Leo-III's `pattern_uni` is not counted) |
| function synthesis | `funcspec` |
| Boolean extensionality | `bool_ext` |
| functional extensionality | `func_ext` (Astraea has a ξ-rule `:func_ext`; this counts Leo-III's in-search use) |
| special instances | `instance` (instantiation of quantifiers over Booleans/functions with special terms) |
| unit rewriting (demodulation) | `rewrite` (`Control.rewriteSimp`: rewriting with ground and non-ground unit equations, including Boolean units `p` to `$true`/`$false`) |
| AC simplification | `ac_simp` |
| external cooperation (E) | `e`, or the "found a proof" line when the proof was cut off |

Not counted, because Astraea has equivalents: `cnf`, `neg_conjecture`, `defexp_and_simp_and_etaexpand`, `simp`, `paramod_ordered`, `eqfactor_ordered`, `pattern_uni`, `lifteq`, `miniscope`, `polarity_switch`, `replace_leibeq`, `replace_andrewseq`.

**Caveat.** A rule appearing in a proof shows Leo-III used it, not that the problem cannot be solved without it. Unit rewriting in particular fires whenever unit equations exist. The "primary feature" column assigns each problem to its single most specific feature, in the table order. At `b63f03e0`, Astraea's `Prover` has no demodulation, primitive substitution, choice rule, in-search Boolean extensionality or pre-unification beyond patterns. It only has the ξ-rule, higher-order predicate instantiation and the `$o` domain split in the clausifier.

### 4.1 Gap classes (58 problems)

| Gap class | Problems | Smoke | Dev | Of these, solved by another LCF-verified Astraea config |
| :--- | ---: | ---: | ---: | ---: |
| calculus/search | 40 | 1 | 39 | 3 |
| external cooperation (E) | 18 | 4 | 14 | 6 |
| more search time (Astraea solves at 10 s) | 0 | 0 | 0 | 0 |

Of the 40 calculus/search problems, stock Leo-III solves 14 already at 2.5 s wall; 26 need its 10 s run.

### 4.2 Calculus/search gap by feature (40 problems)

| Feature in Leo-III proof | Problems using it | As primary feature | Smoke | Dev | Examples |
| :--- | ---: | ---: | ---: | ---: | :--- |
| choice | 8 | 8 | 0 | 8 | CAT038^2, LCL735^5, LCL736^5, SYO295^5, SYO530^1, SYO537^1, SYO539^1, SYO540^1 |
| primitive substitution | 2 | 2 | 0 | 2 | CSR139^1, SYO259^5 |
| pre-unification beyond patterns | 6 | 4 | 0 | 6 | CAT038^2, CSR133^1, CSR139^1, NUN023^2, SEV162^5, SYO553^1 |
| function synthesis | 0 | 0 | 0 | 0 | |
| Boolean extensionality | 6 | 5 | 0 | 6 | CSR151^3, SET047^1, SET143^3, SEV162^5, SYN983^1, SYO026^1 |
| functional extensionality | 5 | 0 | 0 | 5 | CSR133^1, CSR139^1, SET047^1, SET143^3, SYO026^1 |
| special instances | 5 | 2 | 0 | 5 | LCL735^5, LCL736^5, NUN023^2, SYO029^1, SYO199^5 |
| unit rewriting (demodulation) | 27 | 15 | 1 | 26 | SYO444^1, AGT031^1, ALG285^5, CSR127^1, CSR142^1, ITP196^1, SEU537^1, SYO349^5 |
| none of the above (search) | 3 | 3 | 0 | 3 | SET162^5, SEU520^1, SEU544^1 |
| no proof recorded (status printed, killed during proof output) | 1 | 1 | 0 | 1 | SWX154^1 |

The primary features add up to 40. For the 18 E problems, the Leo-III part of the proof also used pre-unification (`NUM808^5`, `SEU668^2`, `SEU969^5`), primitive substitution (`SEU668^2`), functional extensionality (`ITP117^1`) and unit rewriting (`NUM727^1`).

### 4.3 Gap by TPTP domain

| Domain | Gap problems | Gap classes | Features in the calculus/search problems |
| :--- | ---: | :--- | :--- |
| SYO | 16 | calculus/search 14, E 2 | unit rewriting 9, choice 5, special instances 2, Boolean ext. 1, functional ext. 1, prim. subst. 1, pre-unification 1 |
| SEU | 13 | E 8, calculus/search 5 | unit rewriting 3, none 2 |
| ITP | 6 | E 4, calculus/search 2 | unit rewriting 2 |
| CSR | 5 | calculus/search 5 | unit rewriting 5, pre-unification 2, functional ext. 2, prim. subst. 1, Boolean ext. 1 |
| LCL | 4 | calculus/search 3, E 1 | unit rewriting 3, choice 2, special instances 2 |
| NUM | 3 | E 2, calculus/search 1 | unit rewriting 1 |
| SET | 3 | calculus/search 3 | Boolean ext. 2, functional ext. 2, unit rewriting 1, none 1 |
| AGT, ALG | 1 each | calculus/search | unit rewriting |
| CAT | 1 | calculus/search | choice, pre-unification |
| NUN | 1 | calculus/search | pre-unification, special instances |
| SEV | 1 | calculus/search | pre-unification, Boolean ext. |
| SYN | 1 | calculus/search | Boolean ext., unit rewriting |
| SWW | 1 | E | |
| SWX | 1 | calculus/search | no proof recorded |

### 4.4 Full gap list (verification targets)

Format: split, problem, class, proof used for the features (`stock_10s` = stock Leo-III at 10 s), features.

- smoke ITP117^1: E; e_10s: functional extensionality, E
- smoke ITP130^1: E; e_10s: E
- smoke NUM727^1: E; e_10s: unit rewriting, E
- smoke SEU522^1: E; e_10s: E
- smoke SYO444^1: calculus/search; stock_10s: unit rewriting
- dev AGT031^1: calculus/search; stock_10s: unit rewriting
- dev ALG285^5: calculus/search; stock_10s: unit rewriting
- dev CAT038^2: calculus/search; stock_10s: choice, pre-unification
- dev CSR127^1: calculus/search; stock_10s: unit rewriting
- dev CSR133^1: calculus/search; stock_10s: pre-unification, functional ext., unit rewriting
- dev CSR139^1: calculus/search; stock_10s: prim. subst., pre-unification, functional ext., unit rewriting
- dev CSR142^1: calculus/search; stock_10s: unit rewriting
- dev CSR151^3: calculus/search; stock_10s: Boolean ext., unit rewriting
- dev ITP138^1: E; e_10s: E
- dev ITP150^1: E; e_10s: E
- dev ITP196^1: calculus/search; stock_10s: unit rewriting
- dev ITP233^1: calculus/search; stock_10s: unit rewriting
- dev LCL623^1: E; e_10s: E
- dev LCL735^5: calculus/search; stock_10s: choice, special instances, unit rewriting
- dev LCL736^5: calculus/search; stock_10s: choice, special instances, unit rewriting
- dev LCL958^18: calculus/search; stock_10s: unit rewriting
- dev NUM808^5: E; e_10s: pre-unification, E
- dev NUM925^1: calculus/search; stock_10s: unit rewriting
- dev NUN023^2: calculus/search; stock_10s: pre-unification, special instances
- dev SET047^1: calculus/search; stock_10s: Boolean ext., functional ext.
- dev SET143^3: calculus/search; stock_10s: Boolean ext., functional ext., unit rewriting
- dev SET162^5: calculus/search; stock_10s: none
- dev SEU518^1: E; e_10s: E
- dev SEU520^1: calculus/search; stock_10s: none
- dev SEU537^1: calculus/search; stock_10s: unit rewriting
- dev SEU544^1: calculus/search; stock_10s: none
- dev SEU557^1: calculus/search; stock_10s: unit rewriting
- dev SEU575^1: E; e_10s: E
- dev SEU668^2: E; e_10s: prim. subst., pre-unification, E
- dev SEU705^2: E; e_10s: E
- dev SEU742^2: E; e_10s: E
- dev SEU781^2: E; e_10s: E
- dev SEU821^1: calculus/search (solved only in the E run, without E); e_10s: unit rewriting
- dev SEU969^5: E; e_10s: pre-unification, E
- dev SEV162^5: calculus/search; stock_10s: pre-unification, Boolean ext.
- dev SWW470^1: E; e_10s: E (proof cut off at 10 s)
- dev SWX154^1: calculus/search (solved only in the E run, without E); no proof recorded
- dev SYN983^1: calculus/search; stock_10s: Boolean ext., unit rewriting
- dev SYO026^1: calculus/search; stock_10s: Boolean ext., functional ext., unit rewriting
- dev SYO029^1: calculus/search; stock_10s: special instances
- dev SYO068^4.020: E; e_10s: E
- dev SYO170^5: E; e_10s: E
- dev SYO199^5: calculus/search; stock_10s: special instances
- dev SYO259^5: calculus/search; stock_10s: prim. subst.
- dev SYO295^5: calculus/search; stock_10s: choice
- dev SYO349^5: calculus/search; stock_10s: unit rewriting
- dev SYO447^1: calculus/search; stock_10s: unit rewriting
- dev SYO530^1: calculus/search; stock_10s: choice, unit rewriting
- dev SYO537^1: calculus/search; stock_10s: choice, unit rewriting
- dev SYO539^1: calculus/search; stock_10s: choice, unit rewriting
- dev SYO540^1: calculus/search; stock_10s: choice, unit rewriting
- dev SYO553^1: calculus/search; stock_10s: pre-unification
- dev SYO572^7: calculus/search; stock_10s: unit rewriting

### 4.5 Astraea solves, Leo-III does not (14 problems)

Astraea configurations that solve each problem are in brackets. "Any Leo-III" covers stock and E, 2.5 s and 10 s.

| Split | Problem | Astraea configurations |
| :--- | :--- | :--- |
| smoke | ITP175^1 | baseline 2.5 s and 10 s, cooperate, racers, leo3_racer |
| smoke | LCL866^1 | baseline 2.5 s and 10 s, cooperate, racers, leo3_racer |
| smoke | ITP202^1 | racers |
| dev | ITP127^1 | baseline 2.5 s and 10 s, cooperate, racers, leo3_racer |
| dev | SET002^4 | baseline 2.5 s and 10 s, cooperate, racers, leo3_racer |
| dev | SEU477^1 | baseline 2.5 s and 10 s, cooperate, racers, leo3_racer |
| dev | NUM417^1 | baseline 10 s |
| dev | SWV431^2 | baseline 10 s, cooperate |
| dev | AGT029^1 | cooperate, racers |
| dev | ITP048^1, ITP071^1, ITP104^1, ITP124^1, ITP149^1 | racers |

7 are Astraea baseline portfolio solves (`ITP175^1`, `LCL866^1`, `ITP127^1`, `SET002^4`, `SEU477^1` at 2.5 s; `NUM417^1`, `SWV431^2` only at 10 s). The other 7 rely on E-HO, Vampire or cvc5, mainly on ITP problems.

## 5. Leo-III inside Astraea (`mix external.eval`)

[`astraea/lib/mix/tasks/external_eval.ex`](../astraea/lib/mix/tasks/external_eval.ex) now has two extra configurations, enabled when `leo3` is on `$PATH`:

* `leo3_racer`: the internal strategies plus Leo-III racing on the original problem (`leo3 file -t S -p`), with unsat-core reconstruction (`external: [:leo3]`).
* `leo3`: Leo-III alone (`strategies: [], external: [{:leo3, reconstruct: false}]`); its proofs count as `external_unverified`.

It also has a `--csv` option that writes one row per problem and configuration: result tag, LCF-solved, external-only, winning strategy, external prover, elapsed ms.

Findings:

* Standalone `leo3` through Astraea reproduces the direct runs within the noise: Dev 58 vs 63 at 2.5 s, Smoke 25 vs 25 at 10 s. The Smoke 2.5 s run (2 of 34) ran at load about 27, when a trivial problem took 3.2 s wall, so it is not representative.
* `leo3_racer` added **no** LCF-verified proofs: 0 reconstructed on Dev at 2.5 s (11 Leo-III-only refutations) and on Smoke at 10 s (1). At 2.5 s, Leo-III answers at a median of 2.2 s, which leaves almost no time for `Reconstruct.problem` before the deadline. At 10 s, the only Leo-III-only Smoke problem was not reconstructed either. `Reconstruct.problem` re-runs `Astraea.Prover` on the core axioms, so it cannot replay steps Astraea lacks (section 4). Leo-III as a racer is therefore only useful as an oracle until the prover gains the missing rules or a TSTP proof replay exists.

## 6. Caveats

* **JVM startup.** At least 1.45 s of every Leo-III solve is fixed overhead: about 0.3-0.6 s JVM start, about 0.6-1.0 s parsing and cold JIT. Under a 2.5 s wall budget this costs Leo-III about 15 Dev problems (63 vs 78 without startup and parsing). A GraalVM native image (`make native`) or a persistent JVM would remove most of it; neither was tried.
* **Unequal parallelism.** Astraea runs 4 strategies in parallel per problem; Leo-III runs one sequential loop (plus JIT/GC threads and E). Per-problem CPU budgets are therefore not equal; with Astraea's per-problem parallelism, its 2.5 s are up to 10 CPU seconds.
* **Load.** Other agents used armix at the same time; load ranged from 1.5 to 27. Stock Leo-III counts are stable within about 3. Leo-III+E at 2.5 s varied from 65 to 91 on Dev across three passes. The Astraea 2.5 s runs were at a median load of 16.5.
* **`-t` changes Leo-III's behaviour.** Leo-III plans its strategy schedule and E calls relative to `-t`. So the 10 s run cut at 2.5 s is not the same as a 2.5 s run.
* **E build.** `~/tools/eprover` is a DEBUG build of E 3.5.1.
* **Feature attribution** is by rule occurrence in one Leo-III proof (section 4) and is an upper bound on what each feature contributes.
* **Concurrency.** Leo-III 4 problems in parallel, Astraea 2 problems in parallel.

## 7. Reproduction

On the local checkout:

```bash
rsync -az --delete --exclude _build --exclude deps --exclude experiments --exclude target \
  astraea benchmarks armix:~/Projects/wt/baseline/
rsync -az scripts src project build.sbt Makefile armix:~/Projects/wt/baseline/
```

On armix:

```bash
cd ~/Projects/wt/baseline
scripts/leo3_build.sh .                 # JDK, sbt, Leo-III jar, ~/tools/leo3/bin/leo3
scripts/leo3_baseline.sh                # Leo-III: {smoke,dev} x {stock,e} x {2.5,10} s, 4 in parallel
                                        #   -> benchmarks/results/leo3_*.csv, raw output in ~/leo3_runs/
scripts/leo3_astraea_eval.sh            # Astraea: all configs at 2.5 s, baseline at 10 s, 2 in parallel
                                        #   -> benchmarks/results/astraea_{smoke,dev}_{2500,10000}ms.{csv,json}

# Single runs
python3 -I scripts/leo3_run.py --split dev --timeout 2.5 --config e --concurrency 4 \
  --out benchmarks/results/leo3_dev_e_2.5s_run3.csv --proofs ~/leo3_runs/dev_e_2.5_run3
cd astraea && PATH=$HOME/.asdf/shims:$HOME/.cargo/bin:$HOME/tools/eprover-ho/bin:$HOME/tools/eprover/bin:$HOME/tools/vampire/bin:$HOME/tools/cvc5/bin:$HOME/tools/leo3/bin:$PATH \
  mix external.eval --split smoke --timeout 10000 --concurrency 2 --configs leo3_racer,leo3 \
  --out ../benchmarks/results/astraea_smoke_10000ms_leo3.json --csv ../benchmarks/results/astraea_smoke_10000ms_leo3.csv

# Gap analysis (prints the tables of sections 3.1 and 4)
python3 -I scripts/leo3_gap.py --raw ~/leo3_runs --results benchmarks/results \
  --copy-proofs benchmarks/results/leo3_gap_proofs
```

The `_run2` (second, lower-load pass) and `_run3` CSVs are the repeats from section 3.1. `leo3_gap.py` reads only the pass-1 CSVs (file names without a suffix).

## 8. Files

* `scripts/leo3_build.sh`, `scripts/leo3_run.py`, `scripts/leo3_baseline.sh`, `scripts/leo3_astraea_eval.sh`, `scripts/leo3_gap.py`
* `benchmarks/results/leo3_{smoke,dev}_{stock,e}_{2.5,10}s.csv` (pass 1), `*_2.5s_run2.csv`, `leo3_dev_e_2.5s_run3.csv`
* `benchmarks/results/astraea_{smoke,dev}_{2500,10000}ms.{csv,json}`, `astraea_smoke_10000ms_leo3.{csv,json}`
* `benchmarks/results/leo3_proof_features.csv`, `leo3_gap.csv`, `leo3_gap_proofs/`
