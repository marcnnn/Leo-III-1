# Master's Thesis Work & Evaluation Log — Project Astraea

**Thesis Title:** *Oracle-Guided Agentic Synthesis of a Modular Higher-Order Micro-Prover: Revisiting Parallel HOL Deduction via Declarative Elixir Specifications and Data-Oriented Native Execution*  
**Repository & Branch:** `marcnnn/Leo-III-1` (`astraea`)  
**Primary Benchmark & Synthesis Node:** `armix` (`aarch64` 14-core ARM Neoverse-N1, 1 thread/core, 31.26 GiB RAM, 2.0 TiB NVMe/LVM, Linux `7.2.11-100.fc43.aarch64`, Erlang/OTP `27.3.3` `[jit] [smp:14:14]`, Elixir `1.18.3`, Rust `1.97.1`, GCC/G++ `-O3 -march=native -fopenmp-simd`)  
**Logging Policy:** Every architectural decision, corpus measurement, synthesis iteration (RQ2 defect interception), and hardware benchmark (RQ1/RQ3) is recorded here at the time of execution with exact commit SHAs, reproducible commands, and raw metrics.

---

## Entry 001 — Leo-III Codebase & Concurrency Archaeology (2026-10-26)

### 1.1 Findings from the Upstream Leo-III Repository
* **Scale & Stack:** Modern Leo-III (`build.sbt` v1.8.1, Scala `3.9.0`) comprises ~34,700 LOC across `leo.datastructures` and `leo.modules`, relying on pointer-based JVM object graphs (`TermImpl`, `Spine`, `ClauseProxy`) and external first-order/SMT cooperation (`eprover`, `vampire`, `cvc5`, `z3`).
* **Why Fine-Grained Blackboard Parallelism Failed (Commit `28a8c43a`, Feb 3, 2021):**
  * Inspecting git history (`git show 28a8c43a --stat`) revealed that ~75 files implementing Leo-III's original multi-agent blackboard architecture (`src/main/scala/leo/agents/impl/RuleAgent.scala`, `src/main/scala/leo/datastructures/blackboard/impl/AuctionBlackboard.scala`, `TreeContextSet.scala`, ` Splitting.scala`) were moved out of the active build (`oldsrc`).
  * **Root Causes Identified:**
    1. *Synchronization Granularity vs. Inference Latency:* Individual higher-order paramodulation, normalization, and subsumption steps take microseconds; coordinating per-rule agents via central blackboard auctions and locks created severe lock contention.
    2. *Context-Tree Index Pollution:* Storing case-split branches inside a shared `TreeContextSet` complicated forward/backward subsumption and term indexing, causing modern Leo-III to revert to sequential strategy schedules (`SeqLoop.scala` / `ScheduledRun.scala`).
    3. *Counter-Based Skolemization Hazard:* In `src/main/scala/leo/modules/calculus/Rules.scala` (`FuncExt`, status `SZS_EquiSatisfiable`) and clausification, fresh Skolem symbols are generated via a mutable counter (`vargen`). In parallel search with lemma exchange, independent workers either collide on Skolem IDs (unsound) or create duplicate isomorphic Skolem constants for the same quantified formula (exploding the signature).
* **Reusable Conceptual Hooks in Leo-III:**
  * [`AntiUnification.scala`](file:///Users/marcnickert/Projects/opensource/Leo-III/src/main/scala/leo/modules/calculus/AntiUnification.scala) (`PatternAntiUnification`): Higher-order pattern anti-unification (least general generalization), ideal for generalizing recurring inference chains observed in BEAM telemetry.
  * [`CompressProof.scala`](file:///Users/marcnickert/Projects/opensource/Leo-III/src/main/scala/leo/modules/proof_object/CompressProof.scala) (`CompressedRule`): Collapsing linear multi-step chains in proof DAGs into derived macro-inference rules.
  * [`SineSelector.scala`](file:///Users/marcnickert/Projects/opensource/Leo-III/src/main/scala/leo/modules/relevance/SineSelector.scala): SInE symbol-incidence premise selection for large axiom sets.
  * [`contrib/ltbrun`](file:///Users/marcnickert/Projects/opensource/Leo-III/contrib/ltbrun) & [`contrib/crossverify_starexec`](file:///Users/marcnickert/Projects/opensource/Leo-III/contrib/crossverify_starexec): CASC LTB shared-axiom batch runner and SZS soundness compatibility lattice (`{Theorem, ContradictoryAxioms}` vs. `{CounterSatisfiable, Satisfiable}`).

### 1.2 Architectural Resolution in Astraea
1. **Coarse-Grained OTP + Lock-Free Native Micro-Arenas:** Never cross the NIF or process boundary per inference rule. Each parallel OTP worker runs 50–200ms saturation bursts inside an isolated, lock-free native arena (`Rustler` / `NxSimd`), while Elixir/OTP handles top-level goal decomposition, AVATAR clause splitting (over an incremental SAT solver), and Profile-Guided Optimization (PGO) telemetry aggregation.
2. **Content-Addressed (Structural Hash) Skolemization:** Skolem symbols derive their ID from the SHA-256 structural hash of the canonicalized de Bruijn quantified predicate (`Astraea.Arena.skolem_hash/2`), making unit-lemma sharing across parallel workers mathematically sound without central coordination.

---

## Entry 002 — Remote Infrastructure (`armix`) & `TPTP-v9.3.1` THF0 Corpus Census (2026-10-26)

* **Commits:** `c8dc83e0`, `1fa4abc5`, `4b89dcfd`
* **Artifacts Created:**
  * [`Notes/master_thesis_proposal.md`](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/master_thesis_proposal.md)
  * [`Notes/tptp_test_plan.md`](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/tptp_test_plan.md)
  * [`scripts/tptp_thf0_setup.py`](file:///Users/marcnickert/Projects/opensource/Leo-III/scripts/tptp_thf0_setup.py)
  * [`benchmarks/manifests/manifest_lock.json`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/manifest_lock.json)
  * [`benchmarks/manifests/thf_catalog.csv`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/thf_catalog.csv)

### 2.1 `TPTP-v9.3.1` Higher-Order Census
Installed the full `TPTP-v9.3.1` distribution (released Aug 21, 2026; 10.5 GB unpacked) at `armix:~/.local/share/tptp/TPTP-v9.3.1`. Running [`scripts/tptp_thf0_setup.py`](file:///Users/marcnickert/Projects/opensource/Leo-III/scripts/tptp_thf0_setup.py) across all higher-order (`^`) problems and transitively included `Axioms/*.ax` files yielded:

| Metric / Filter Stage | Problem Count | Notes |
| :--- | :---: | :--- |
| **Total THF (`Problems/*/*^*.p`) Scanned** | **5,279** | Across all TPTP v9.3.1 domains |
| **Strict Monomorphic THF0 (`THM` / `ContradictoryAxioms`)** | **3,241** | Excludes `BuggedProblems-v9.3.1.txt`, `TH1_*` polymorphism, `*_ARI` arithmetic, tuples, `$modal`, `@+`/`@-` choice, `$let`/`$ite` |
| **Strict Monomorphic THF0 (`CSA` / `Satisfiable` Traps)** | **468** | Essential soundness traps: claiming `Theorem` on any of these is a critical soundness failure |
| **Total Eligible Strict THF0 Pool** | **3,709** | Spanning 33 TPTP domains (top domains: `SEU` 821, `SYO` 756, `ITP` 458, `SEV` 370, `NUM` 310, `LCL` 176, `SET` 161, `GRA` 84, `CSR` 82, `ALG` 80) |

### 2.2 Anti-Leakage Benchmark Splits (SHA-256 Locked, Seed `"astraea-tptp-v9.3.1"`)
To prevent LLM benchmark memorization and PGO overfitting, the eligible pool was partitioned deterministically into three strictly disjoint tiers (verified on every `mix test` run by [`Astraea.GatesTest`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/test/astraea/gates_test.exs)):

| Split Tier | Manifest File | Total | `THM` | `CSA`/`SAT` Traps | SHA-256 Digest | Role & Access Policy |
| :--- | :--- | :---: | :---: | :---: | :--- | :--- |
| **Tier 1 (`TPTP-Smoke`)** | [`tptp_thf0_smoke.txt`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/tptp_thf0_smoke.txt) | **50** | 35 | 15 | `fc88a708...db95617` | Inner Gate-3 synthesis check (`<1s` timeout) |
| **Tier 2 (`TPTP-Dev`)** | [`tptp_thf0_dev.txt`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/tptp_thf0_dev.txt) | **300** | 240 | 60 | `e53d398a...eff499b` | PGO telemetry, `CompressedRule` learning, & anonymized failure feedback |
| **Tier 3 (`TPTP-Holdout`)** | [`tptp_thf0_holdout.txt`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/tptp_thf0_holdout.txt) | **500** | 400 | 100 | `f904f43a...c7bb13` | Frozen blind thesis evaluation (`armix` & `zib` HPC) — **never read during synthesis/training** |

### 2.3 AST Node-Kind Census via `{:tptp, "~> 0.3.0"}`
Running a full AST walk with `Tptp.Unit.from_file/2` (`resolver: Tptp.Resolver.Fs`) across all **50 `TPTP-Smoke`** and **300 `TPTP-Dev`** problems (plus all transitively included `Axioms/*.ax` files) proved that both splits use the **exact same 27 `{kind, arity}` CST node shapes**:
* **Leaf tokens (arity 0):** `:ampersand`, `:constant`, `:defined_constant`, `:exists`, `:forall`, `:iff`, `:implies`, `:lambda`, `:tilde`, `:variable`, `:vline`
* **Composite nodes:** `:thf_and_formula/2`, `:thf_apply_formula/2`, `:thf_atom_typing/2`, `:thf_binary_pair/3`, `:thf_defined_atomic/1` (higher-order connective constants `(~)`, `(&)`, `(|)`, `(=>)`), `:thf_defined_infix/2`, `:thf_infix_unary/2`, `:thf_mapping_type/2`, `:thf_or_formula/2`, `:thf_prefix_unary/2`, `:thf_quantification/2`, `:thf_quantified_formula/2`, `:thf_typed_variable/2`, `:thf_unitary_formula/1`, `:thf_unitary_term/1`, `:thf_variable_list/2`.

---

## Entry 003 — Layer-2 Reference Arena, THF0 Lowering & RQ2 Synthesis Log (2026-10-26)

* **Commits:** `65ba9dc7`, `f6b11863`, `d5eb664a`
* **Modules Implemented:**
  * [`Astraea.Arena`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex) — 12-byte big-endian flat node layout (`<<tag::8, flags::8, type_id::16, left::32, right::32>>`), hash-consing, de Bruijn shifting/substitution, reference $\beta\eta$-normalizer (`beta_eta_norm/2`), Turner $S, K, I, B, C$ bracket abstraction (`to_combinators/2`) & reducer (`comb_norm/2`), content-addressed `skolem_hash/2`, reference KBO (`kbo_compare/3`), and 16-lane `FVIndex` (`feature_vector/2`).
  * [`Astraea.TptpLower`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/tptp_lower.ex) — Lowers all 27 THF0 CST shapes (including transitive `Axioms/*.ax` includes and $\lambda$-synthesized higher-order connectives) into `Astraea.Arena`.
  * [`Astraea.ProofChecker`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex) — Trusted LCF refutation kernel (`:axiom`, `:refl`, `:symm`, `:trans`, `:resolve`).
  * [`Astraea.Native`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/native.ex) & [`astraea/native/astraea_native/src/lib.rs`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/native/astraea_native/src/lib.rs) — Zero-copy Rustler NIF for KBO ordering and `FVIndex`.

### 3.1 RQ2 Synthesis & Defect Interception Log (Entries #1–#2)

| Target Kernel | Iteration | Gate Triggered | Defect / Observation | Resolution | Final Status |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `astraea_native` (`nif_kbo_compare`, `nif_feature_vector`, `nif_fv_subsumes_batch`) | 1 (`f6b11863`) | **Gate 0 (`rustc`)** | 3 lifetime errors: `atoms::err_invalid_arena().to_term(env)` borrows non-`'static` `Env<'1>` inside `Box<dyn Encoder>` | Replaced `.to_term(env)` with static `Atom` encoder `Box::new(atoms::err_invalid_arena())` in `d5eb664a` | **PASS** (Gates 1–4) |
| `Astraea.NxSimdIndex` (`fv_subsumes_soa_kernel`) | 1 | **Gate 4 (`Codegen` inspection)** | Initial AoS `{1024, 16}` formulation with `Nx.sum(axes: [1])` emitted 3 loops and a `17,408 B` scratch buffer | Transposed feature table to **SoA `{16, N}`** (`:u16`) with unrolled `Nx.logical_and`, yielding a **single fused `#pragma omp simd` loop** with `arena_size == 0` (`88f48fc2`) | **PASS** (Gates 1–4) |

* **Verification Summary (`mix test` on `armix`):**
  * `3 properties, 3 tests, 0 failures` in **0.7 seconds** (including lowering all **50 `TPTP-Smoke` problems** and their included axiom sets into `Astraea.Arena` and cross-checking every `FVIndex` vector between Elixir and Rust).

---

## Entry 004 — RQ1 Hardware Evaluation: Pure Elixir vs. Rustler NIF (AoS) vs. `NxSimd.Compiler` (SoA) (2026-10-26)

* **Commits:** `806dc991`, `88f48fc2`
* **Modules Evaluated:**
  * [`Astraea.Arena`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex) (Pure Elixir Layer-2 Reference Oracle)
  * [`Astraea.Native`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/native.ex) (`astraea_native` Rustler NIF, `rustc 1.97.1 -O3`, LTO thin, Array-of-Structures `u32` layout)
  * [`Astraea.NxSimdIndex`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/nx_simd_index.ex) (`NxFixed.WidthCheck` + `NxSimd.Compiler`, `g++ -O3 -march=native -fopenmp-simd`, Structure-of-Arrays `{16, N}` `:u16` layout)
* **Reproducible Command on `armix`:**
  ```bash
  cd ~/Projects/opensource/Leo-III/astraea && mix gate.4
  ```

### 4.1 Experiment A — KBO Term Ordering on Lowered `TPTP-Smoke` Arena
* **Workload:** 256 higher-order formula/term pair comparisons over a lowered `TPTP-Smoke` arena (`3,952` hash-consed 12-byte nodes = `47,424 B` contiguous binary).

| Implementation | Median Latency | Average Latency | Throughput (`ips`) | BEAM Memory Allocated | Speedup vs. Elixir |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **Pure Elixir Reference (`Arena.kbo_compare/3`)** | `2,126.06 μs` | `2,436.61 μs` | `0.41 K` | `2,369.23 KB` | `1.00x` |
| **Zero-Copy Rustler NIF (`Native.nif_kbo_compare/3`)** | **`107.08 μs`** | **`125.62 μs`** | **`7.96 K`** | **`8.03 KB`** | **19.40x faster** (`295x` less memory) |

### 4.2 Experiment B — 16-Lane `FVIndex` Subsumption Filtering (`1,024` & `16,384` Clauses)
* **Workload:** Filter a clause database of $N \in \{1\,024,\; 16\,384\}$ lowered `TPTP-Smoke` clauses using 16-feature dominance ($\forall k \in 0..15:\; \text{cand}[k] \le \text{target}[k]$), returning the 48 (or 768) subsumable candidates.
* **Correctness Pre-Check:** Verified 100% bitwise match (`48 / 1,024` indices) across all three engines prior to timing.

| Implementation | Clause Bank ($N$) | Median Latency | Average Latency | Throughput (`ips`) | Clauses Scanned / sec | BEAM Memory | Speedup vs. Elixir | Speedup vs. Rustler AoS |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **Elixir Reference** | `1,024` | `155.28 μs` | `183.85 μs` | `5.44 K` | `~5.6 M / s` | `256.78 KB` | `1.00x` | `0.29x` |
| **Rustler NIF (AoS `u32`)** | `1,024` | `45.64 μs` | `52.87 μs` | `18.91 K` | `~19.4 M / s` | `0.75 KB` | `3.48x` | `1.00x` |
| **`NxSimd.Compiler` (SoA `u16`)** | **`1,024`** | **`7.92 μs`** | **`13.10 μs`** | **`76.34 K`** | **`~78.2 M / s`** | **`1.53 KB`** | **`14.03x` (`19.6x` med)** | **`4.04x` (`5.76x` med)** |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Elixir Reference** | `16,384` | `4,332.40 μs` | `4,749.66 μs` | `0.21 K` | `~3.4 M / s` | `4,108.03 KB` | `1.00x` | `0.25x` |
| **Rustler NIF (AoS `u32`)** | `16,384` | `746.65 μs` | `837.31 μs` | `1.19 K` | `~19.5 M / s` | `< 1 KB` | `5.67x` | `1.00x` |
| **`NxSimd.Compiler` (SoA `u16`)** | **`16,384`** | **`130.32 μs`** | **`159.35 μs`** | **`6.28 K`** | **`~102.9 M / s`** | **`1.53 KB`** | **`29.81x` (`33.2x` med)** | **`5.25x` (`5.73x` med)** |

### 4.3 Key Analytical Takeaways for Thesis Chapter 4 (RQ1 & RQ2)
1. **Data Layout Dominates Language Choice (SoA vs. AoS):** A declarative Elixir `Nx` kernel using a transposed **Structure-of-Arrays (`{16, N}` `:u16`)** layout and compiled via `NxSimd.Compiler` outperformed a hand-written Rustler NIF using an Array-of-Structures (`{N, 16}` `u32`) layout by **5.25x–5.76x**, scanning **102.9 million clauses/second** on a single ARM Neoverse-N1 core (`130.32 μs` for 16,384 clauses—faster than Pure Elixir scans 1,024 clauses).
2. **Static Width Verification Enables Narrower SIMD Lanes:** Because `NxFixed.WidthCheck` statically proves that clause feature counts fit in `:u16` (`uint16_t`) and comparison masks fit in `:u8` (`uint8_t`), `NxSimd.Codegen` narrows the memory traffic by 2x compared to `u32` AoS and packs 8 clauses per 128-bit NEON register with zero scratch-buffer allocation (`arena_size == 0`).
3. **Division of Labor Between `NxSimd` and `Rustler`:**
   * **Bulk Tabular / Matrix Operations (`FVIndex` subsumption, SInE premise selection, and `NxSimd.Quantized` `int8` clause scoring):** Best expressed as width-checked `Nx` `defn` graphs compiled via `NxSimd.Compiler`.
   * **Irregular DAG / Tree Traversals (Hash-consing, de Bruijn/combinator reduction, KBO recursive lex comparison, higher-order pattern unification):** Best executed inside zero-copy `Rustler` NIFs operating on the flat 12-byte `Astraea.Arena` slice (**19.4x** faster than Elixir with **295x** less heap allocation).

---

## Entry 005 — Higher-Order Clausifier, LCF-Verified Given-Clause Prover & Empirical `TPTP-Smoke` / `TPTP-Dev` Evaluation (2026-10-26)

* **Commits:** `c6448865`
* **Modules Implemented & Extended:**
  * [`Astraea.Arena`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex) — Added free-variable extraction (`free_vars/2`), capture-avoiding free-variable substitution with $\beta\eta$-normalization (`subst_fvar/3`), occurs-check (`occurs_fvar?/4`), one-way syntactic/symmetric-equality pattern matching (`match_pattern/4`), higher-order pattern/abstraction unification (`unify/4`), loose bound-variable detection (`has_loose_bvar?/3`), subterm abstraction (`abstract_subterm/4`), and double-negation elimination (`~ ~ A -> A`) inside `beta_eta_norm/2`.
  * [`Astraea.ProofChecker`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex) — Expanded the trusted LCF kernel to verify 9 primitive inference rules: `:axiom`, `:refl`, `:symm`, `:trans`, `:subst` (capture-avoiding free-variable instantiation + $\beta\eta$-normalization), `:cong` (higher-order application congruence), `:func_ext` ($\xi$-rule lambda congruence `u = v |- (^ [X]: u) = (^ [X]: v)`), `:paramod` (Leibniz equality subterm replacement + $\beta\eta$-normalization), and `:resolve` (modulo equality symmetry).
  * [`Astraea.Clausifier`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/clausifier.ex) — Implemented multi-pass constant/combinator definition extraction & selective bridge-predicate inlining, Leibniz equality recognition (`! [Q: ty > $o]: (Q @ u => Q @ v)` $\to$ `u = v`), unfolded bi-implication recognition (`(~A | B) & (~B | A)` $\to$ `A = B`), SInE symbol-rarity premise selection (`sine_filter/4`), Boolean domain splitting (`$o` quantifiers over `{$true, $false}`), positive congruence & negative functional extensionality (`FuncExt`), shared-conjunct Boolean equivalence factoring (`(A & S) <=> (B & S)` $\to$ `S => (A <=> B)`), and content-addressed Skolem CNF conversion.
  * [`Astraea.Prover`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/prover.ex) & [`Astraea.TptpCorpus`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/tptp_corpus.ex) — Implemented the discount-style Given-Clause saturation prover and concurrent 14-core OTP split runner (`evaluate_split/2`) with eager unit-clause subsumption resolution (`unit_simplify/2`), equality resolution, factoring, positive $\xi$-extensionality (`:func_ext`), higher-order predicate reflexivity instantiation (`P := ^ [Z]: (Z = u)`), binary resolution, KBO-oriented superposition/paramodulation, and 16-lane `FVIndex` forward subsumption.

### 5.1 RQ2 Synthesis & Defect Interception Log (Entries #3–#6)

| Target Component | Iteration | Gate Triggered | Defect / Observation | Resolution | Final Status |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `Astraea.Clausifier` / `ProofChecker` / `Prover` | 1 | **Gate 1 (`Arena.mk_not/2` & `mk_eq/3` type guards on `NUM793^1`, `ITP175^1`)** | **Tag Enumeration Drift:** Initial drafts used raw integers `4` (`@tag_lam`), `5` (`@tag_app`), `7` (`@tag_forall`), and `9` (`@tag_not`), whereas [`Astraea.Arena`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex) defines `@tag_app = 4`, `@tag_lam = 5`, `@tag_not = 7`, `@tag_forall = 9`. | Standardized symbolic `@tag_*` module attributes across `Arena`, `Clausifier`, `ProofChecker`, and `Prover`. | **PASS** |
| `Astraea.Arena.bind_fvar/4` & `ProofChecker.validate_subst_types/3` & `Clausifier.match_definition/4` | 2 | **Gate 3 (`TPTP-Smoke` evaluation: `SEU559^2`, `SEU893^5`, `SYO088^5`)** | **`@flag_has_bvar` Propagation vs. Escaping De Bruijn Indices:** `Arena.mk_lam/3` propagates `b_flags` (`@flag_has_bvar = 0x01`) from its body so `shift/4` and `subst_bvar/4` know a bound variable exists inside. Checking `band(flags, @flag_has_bvar) == 0` rejected **all closed $\lambda$-abstractions** (`^ [X]: ... X ...`), blocking higher-order definition extraction and predicate instantiation. | Implemented `Arena.has_loose_bvar?(arena, term_id, depth)` (checking `BVar(i)` with `i >= depth`), immediately jumping `TPTP-Smoke` solved theorems from **11/34 to 24/34**. | **PASS** |
| `Astraea.Clausifier.collect_conjuncts/2` | 3 | **Gate 3 (`LCL866^1` modal equivalence factoring)** | **$n$-ary Conjunction Normalization under Double-Negation Elimination:** After `beta_eta_norm/2` eliminated double negations, a 3-way conjunction `(A & B) & C` became `~((~A | ~B) | ~C)` where the left child of `@tag_or` is `@tag_or` rather than `@tag_not`, causing binary `collect_conjuncts` to miss shared conjuncts in `(msym & meuc) <=> (mtrans & msym & meuc)`. | Updated `collect_conjuncts/2` to flatten `or_id` via `collect_disjuncts/2` and negate each disjunct, solving `LCL866^1` in **13 iterations / 127.9 ms**. | **PASS** |
| `Astraea.Prover.try_superposition/2` | 4 | **Gate 3 (`SEU511^2` runtime check)** | **`Enum.reduce_while/3` Early-Refutation Return:** When `unit_simplify/2` inside `paramod_directed/3` derived the empty clause directly (`{:proved, st, empty_id}`), the `with` block inside `try_superposition/2` returned `{:proved, ...}` directly instead of `{:halt, {:proved, ...}}`. | Added `else {:proved, _, _} = proved -> {:halt, proved}` to `try_superposition/2`. | **PASS** |

---

## Entry 006 — RQ2 Defect Catch #7 (Vacuous Higher-Order Abstraction) & Clause Condensation (2026-10-26)

* **Modules Refined:**
  * [`Astraea.Arena.match_fvar_app/4`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex#L510-L538) — Non-vacuous higher-order abstraction guard (`Arena.occurs_bvar?(arena, abstracted_body, 0)`).
  * [`Astraea.Prover.condense_clause/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/prover.ex#L298-L343) — LCF-verified `:subst` clause condensation.

### 6.1 RQ2 Defect Interception #7: Vacuous Higher-Order Abstraction Explosion
* **Discovery Context:** While profiling `LCL621^1` (a modal logic theorem in `TPTP-Smoke` with the `k4` axiom `pos:(X10 @ X13)` where `X10 : $i > $o` is a free predicate variable), we observed that saturation generated `5,978` passive clauses in 306 iterations (`2,510 ms`).
* **Root Cause:** In [`Arena.match_fvar_app/4`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex#L510-L538) (`F @ arg_id =?= other_id`), `abstract_subterm(arena, other_id, arg_id, 0)` replaces occurrences of `arg_id` inside `other_id` with `BVar(0)`. However, when `arg_id` did **not** occur inside `other_id`, `abstract_subterm/4` returned `other_id` unchanged (with no `BVar(0)` occurrence), synthesizing a vacuous constant function `F := ^ [Z]: other_id`. Consequently, any literal of the form `X10 @ X13` unified with **every** literal in every clause across the entire search space!
* **Resolution & Impact:** Added `if occurs_bvar?(arena, abstracted_body, 0)` to `Arena.match_fvar_app/4` (restricting constant-predicate instantiation to the dedicated ground `Prover.match_const_pred/3` rule). On `LCL621^1`, saturation dropped from `306 iterations / 2,510 ms` to **`65–82 iterations / 1,101 ms`** (`2.28x` faster), bringing single-strategy `TPTP-Smoke` within the 2.5s budget to **`26 / 34` (`76.5%`)**.

### 6.2 Clause Condensation (`Prover.condense_clause/2`)
* When `Clausifier.to_nnf_bool_eq/5` expands a negated equivalence `~(A <=> B)` into `(A | B) & (~A | ~B)`, universally quantified subformulas shared between `A` and `B` introduce duplicate literals with distinct free variables (e.g., `SYO444^1` clauses `C4..C7` of size 6).
* Implemented `condense_clause/2`: whenever one-way matching `Arena.match_pattern(arena, a2, a1)` between two same-polarity literals maps a clause onto a strict subset of itself, the prover emits an LCF `:subst` inference step, shrinking `SYO444^1`'s 6-literal clauses to 4 literals automatically.

---

## Entry 007 — WP3 Multi-Strategy OTP Portfolio, WP4 Proof DAG Compression & Final Blind `TPTP-Holdout` Evaluation (2026-10-26)

* **Modules Implemented:**
  * [`Astraea.Portfolio`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/portfolio.ex) (**WP3**) — Concurrent 4-strategy OTP portfolio coordinator over `Astraea.Prover`. Spawns monitored worker processes for four complementary strategy profiles and terminates sibling workers (`Process.exit(pid, :kill)`) the millisecond the first worker constructs an LCF-verified refutation:
    1. `:goal_standard` — `sine_limit: 55, inline_bridges: false, scoring_mode: :goal_directed, max_clause_lits: 6, max_clause_weight: 45`
    2. `:sine_tight_unit` — `sine_limit: 16, inline_bridges: false, scoring_mode: :unit_focused, max_clause_lits: 6, max_clause_weight: 50`
    3. `:full_inline_weight` — `sine_limit: 40, inline_bridges: true, scoring_mode: :weight_first, max_clause_lits: 7, max_clause_weight: 55`
    4. `:broad_breadth` — `sine_limit: 90, inline_bridges: false, scoring_mode: :breadth_first, max_clause_lits: 8, max_clause_weight: 60`
  * [`Astraea.Compressor`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/compressor.ex) (**WP4**) — Post-saturation LCF proof DAG compressor and macro-inference miner. Composes linear `:subst -> :subst` chains (`compose_substitutions/3`) into single LCF `:subst` steps, deduplicates identical DAG nodes with child parent-ID rewiring, prunes unreachable ancestors from `⊥`, and re-verifies every compressed proof through `Astraea.ProofChecker.verify_refutation/2`.

### 7.1 Complete Multi-Tier Evaluation Across `TPTP-Smoke` (50), `TPTP-Dev` (300), and Blind `TPTP-Holdout` (500) on `armix`

* **Reproducible Command on `armix`:**
  ```bash
  cd ~/Projects/opensource/Leo-III/astraea && mix run -e '
    for split <- [:smoke, :dev, :holdout] do
      res = Astraea.Portfolio.evaluate_split(split, timeout_ms: 2500, max_concurrency: 6)
      comp = Astraea.Compressor.summarize_corpus(res.thm_solved)
      IO.inspect({split, Map.drop(res, [:raw_results, :thm_solved]), comp}, limit: :infinity)
    end
  '
  ```

| Benchmark Split | Total Problems | `Theorem` Pool | Single-Strategy Solved | **WP3 Portfolio Solved (`%`)** | **`CSA`/`SAT` Traps Tested** | **`CSA`/`SAT` False Proofs** | **LCF Verification Pass Rate** |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **Tier 1 (`TPTP-Smoke`)** | `50` | `34` | `26 / 34` (`76.5%`) | **`27 / 34` (`79.41%`)** | `15` | **`0` (`0.0%`)** | **`27 / 27` (`100.0%`)** |
| **Tier 2 (`TPTP-Dev`)** | `300` | `237` | `79 / 237` (`33.3%`) | **`82 / 237` (`34.60%`)** | `60` | **`0` (`0.0%`)** | **`82 / 82` (`100.0%`)** |
| **Tier 3 (`TPTP-Holdout`, Blind)** | `500` | `398` | — *(Blind One-Shot)* | **`155 / 398` (`38.94%`)** | `100` | **`0` (`0.0%`)** | **`155 / 155` (`100.0%`)** |
| **Combined Corpus Total** | **`850`** | **`669`** | — | **`264 / 669` (`39.46%`)** | **`175`** | **`0 / 175` (`0.0%`)** | **`264 / 264` (`100.0%`)** |

> **Anti-Overfitting Validation:** On the strictly untouched 500-problem `TPTP-Holdout` split (`SHA-256: f904f43a...c7bb13`), `Astraea.Portfolio` solved **`155 / 398` (`38.94%`)** of the `Theorem` problems across **17 TPTP domains**—exceeding its `34.60%` solve rate on `TPTP-Dev` by **+4.34 percentage points**, while recording **0 false proofs across all 100 `CounterSatisfiable`/`Satisfiable` soundness traps** and **100% LCF kernel verification**.

### 7.2 WP3 Strategy Portfolio Contribution Analysis (RQ3)

| Portfolio Strategy | Key Parameters | `TPTP-Smoke` Wins (`27`) | `TPTP-Dev` Wins (`82`) | `TPTP-Holdout` Wins (`155`) | Total Wins (`264`) | Share (`%`) |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`:goal_standard`** | `sine_limit: 55`, keep bridges, `:goal_directed` | 10 | 33 | 69 | **112** | **42.4%** |
| **`:sine_tight_unit`** | `sine_limit: 16`, keep bridges, `:unit_focused` | 5 | 19 | 31 | **55** | **20.8%** |
| **`:full_inline_weight`** | `sine_limit: 40`, `inline_bridges: true`, `:weight_first` | 6 | 16 | 32 | **54** | **20.5%** |
| **`:broad_breadth`** | `sine_limit: 90`, `max_lits: 8`, `:breadth_first` | 6 | 14 | 23 | **43** | **16.3%** |

* **Qualitative Highlight (`ITP175^1` in `TPTP-Smoke`):** Single-strategy `:goal_standard` solved 26/34 problems on `TPTP-Smoke`. In `Astraea.Portfolio`, the `:broad_breadth` worker (`sine_limit: 90, scoring_mode: :breadth_first, max_clause_lits: 8`) solved the interactive theorem proving export **`ITP175^1`** in `247 iterations / 1,999.68 ms` with a 6-step LCF refutation, raising `TPTP-Smoke` to **`27 / 34` (`79.41%`)**.

### 7.3 Domain Breakdown on Blind `TPTP-Holdout` (`155` Solved Theorems Across 17 Domains)

| TPTP Domain | Domain Description | `TPTP-Smoke` | `TPTP-Dev` | `TPTP-Holdout` (Blind) | Combined Solved |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`SYO`** | Syntactic Higher-Order (Leibniz, Extensionality, Combinators) | 10 | 19 | **42** | **71** |
| **`SEU`** | Set Theory (Mizar / Tarski-Grothendieck HOL) | 6 | 21 | **37** | **64** |
| **`SET`** | Set Theory (Higher-Order Boolean Algebra & Relations) | 0 | 13 | **19** | **32** |
| **`NUM`** | Number Theory (Peano / Landau Higher-Order Arithmetic) | 1 | 4 | **15** | **20** |
| **`LCL`** | Logic Calculi (Modal, Temporal & Intuitionistic HOL Embeddings) | 4 | 5 | **10** | **19** |
| **`SEV`** | Set Theory (Elementary / Verification) | 2 | 2 | **9** | **13** |
| **`SYN`** | Syntactic Benchmark Problems | 0 | 3 | **6** | **9** |
| **`ITP`** | Interactive Theorem Proving Exports (Isabelle/HOL, Coq) | 1 | 3 | **4** | **8** |
| **`AGT`** | Multi-Agent Systems | 2 | 0 | **3** | **5** |
| **`PUZ`** | Higher-Order Epistemic & Logic Puzzles | 0 | 3 | **1** | **4** |
| **`ALG`** | Higher-Order Algebra | 0 | 3 | **0** | **3** |
| **`CSR`** | Commonsense Reasoning | 0 | 2 | **1** | **3** |
| **`PLA`** | Planning | 0 | 2 | **1** | **3** |
| **`SWV`** | Software Verification | 1 | 0 | **2** | **3** |
| **`NLP`** | Natural Language Processing | 0 | 1 | **1** | **2** |
| **`PHI`** | Philosophy / Metaphysics (Higher-Order Modal Ontology) | 0 | 0 | **2** | **2** |
| **`ANA`** | Real / Functional Analysis | 0 | 0 | **1** | **1** |
| **`GEG`** | Geography | 0 | 0 | **1** | **1** |
| **`PRO`** | Process / Protocol Verification | 0 | 1 | **0** | **1** |
| **Total** | **19 Distinct TPTP Domains** | **27** | **82** | **155** | **264** |

### 7.4 WP4 Proof DAG Compression & Macro-Inference Pattern Census (`Astraea.Compressor`)

Across all **264 verified higher-order refutations**, [`Astraea.Compressor.compress_dag/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/compressor.ex) fused linear `:subst -> :subst` chains and deduplicated shared inference steps while preserving 100% compatibility with the 9-rule [`Astraea.ProofChecker`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex) LCF kernel:

| Corpus Split | Theorems Analyzed | Raw LCF Steps | Compressed LCF Steps | Steps Saved (`%`) | `:subst -> :subst` Fusions | Structural Dedup Merges | Mined `inst_resolve` (`:subst -> :resolve`) | Mined `eq_resolution` (`:refl -> :resolve`) | Mined `superposition` (`:subst -> :paramod`) | Mined `ext_paramod` (`:func_ext -> :paramod`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`TPTP-Smoke`** | 27 | 342 | **316** | `26` (**`7.60%`**) | 19 | 10 | 77 | 1 | 0 | 1 |
| **`TPTP-Dev`** | 82 | 1,202 | **1,111** | `91` (**`7.57%`**) | 89 | 32 | 238 | 10 | 15 | 1 |
| **`TPTP-Holdout`** | 155 | 2,015 | **1,875** | `140` (**`6.95%`**) | 104 | 50 | 415 | 27 | 26 | 3 |
| **Total (`264` Proofs)** | **264** | **3,559** | **3,302** | **`257` (`7.22%`)** | **212** | **92** | **730** | **38** | **41** | **5** |

* **Primitive LCF Rule Distribution Across All `3,302` Compressed Steps:**
  * `:resolve` — `1,248` (`37.8%`)
  * `:axiom` — `1,140` (`34.5%`)
  * `:subst` — `801` (`24.3%`)
  * `:paramod` — `72` (`2.2%`)
  * `:refl` — `36` (`1.1%`)
  * `:func_ext` — `5` (`0.15%`)
* **Macro-Inference Takeaway:** Over **91.1%** (`730 / 801`) of the remaining `:subst` steps after `:subst -> :subst` fusion feed directly into `:resolve` (`inst_resolve`) or `:paramod` (`superposition`). Contracting `inst_resolve`, `superposition`, and `eq_resolution` into derived `CompressedRule` macro-steps reduces the logical proof certificate length by an additional **809 steps (`24.5%`)**, yielding a combined two-stage DAG compression ratio of **29.95%** (`3,559` raw steps $\to$ `2,493` macro-compressed steps).

---

## Entry 008: External Prover Integration over MuonTrap Ports & Unsat-Core Reconstruction (2026-10-27)

* **Modules Implemented** (port of Leo-III's `leo.modules.external`):
  * [`Astraea.External`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external.ex): runs E, Vampire, Zipperposition, cvc5, iProver, Satallax, Leo-III and LEO-II as OS processes via `MuonTrap.cmd/3`, on the original TPTP file or on Astraea's clausified clause set. Specs live in [`External.Provers`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external/provers.ex), SZS answers are parsed by [`External.SZS`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external/szs.ex) (TPTP comment lines only).
  * [`External.ThfPrinter`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external/thf_printer.ex) and [`External.TffPrinter`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external/tff_printer.ex): clause sets as THF0, or as first-order TFF0 via applicative encoding with lambda lifting (sound for refutations, deliberately incomplete).
  * [`External.Reconstruct`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/external/reconstruct.ex): Sledgehammer-style reconstruction. The unsat core is read from `file(_, Name)` annotations of the TSTP proof and re-proved by `Astraea.Prover`, so every accepted proof still passes `Astraea.ProofChecker`.
  * `Astraea.Portfolio` `external:` option (whole-problem racers) and `Astraea.Prover` `cooperate:` option (Leo-III style mid-search cooperation; core sub-proofs are spliced onto existing derivations via `seed:`).
* **Process Isolation Findings:**
  * Without cgroups, MuonTrap only signals its direct child; forked prover workers and JVMs survived kills. Fixed with [`priv/process_group.sh`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/priv/process_group.sh), which kills the prover's whole process group.
  * The `oss-cad-suite` cvc5 1.0.1-dev segfaults on 4 of 12 THF smoke problems. As a separate process this is just a failed worker; as a NIF it would have taken down the BEAM. Replaced by cvc5 1.4.2 (`~/tools/cvc5`).
* **Prover Builds on `armix`:** E 3.5.1-ho and E 3.5.1 (`~/tools/eprover-ho`, `~/tools/eprover`), Vampire 5.1.0 (`~/tools/vampire`), cvc5 1.4.2 (`~/tools/cvc5`).

### 8.1 Evaluation on `TPTP-Smoke` and `TPTP-Dev` (2.5 s per problem, 3 problems in parallel)

* **Reproducible Command on `armix`:**
  ```bash
  export PATH=~/tools/eprover-ho/bin:~/tools/eprover/bin:~/tools/vampire/bin:~/tools/cvc5/bin:$PATH
  mix external.eval --split dev --timeout 2500 --concurrency 3 --out /tmp/external_dev.json
  ```

| Split | Configuration | LCF-Verified Solved | of which Externally Assisted | Unverified External Only | `CSA`/`SAT` False Proofs | External Unsound Answers |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| `TPTP-Smoke` (34 `THM`) | Baseline portfolio | `27` | `0` | `0` | `0 / 15` | `0` |
| `TPTP-Smoke` | + racers (E-HO, Vampire, cvc5) | **`30`** | `4` | `4` | `0 / 15` | `0` |
| `TPTP-Smoke` | + mid-search cooperation (E-HO) | `27` | `2` | `0` | `0 / 15` | `0` |
| `TPTP-Dev` (237 `THM`) | Baseline portfolio | `82` (`34.60%`) | `0` | `0` | `0 / 60` | `0` |
| `TPTP-Dev` | + racers (E-HO, Vampire, cvc5) | **`93` (`39.24%`)** | `15` | `60` | `0 / 60` | `0` |
| `TPTP-Dev` | + mid-search cooperation (E-HO) | `88` (`37.13%`) | `13` | `0` | `0 / 60` | `0` |

* The baseline reproduces Entry 007 exactly (`82 / 237` on `TPTP-Dev`).
* External provers find many more refutations than can currently be reconstructed (`60` unverified on `TPTP-Dev`). Reconstruction fails when the core still needs inferences `Astraea.Prover` lacks within the remaining budget, so these are a direct target list for prover improvements.
* `TPTP-Holdout` was not run, per its blind-benchmark policy.
