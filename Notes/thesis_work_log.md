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
