# Master's Thesis Proposal

**Title:** Oracle-Guided Agentic Synthesis of a Modular Higher-Order Micro-Prover: Revisiting Parallel HOL Deduction via Declarative Elixir Specifications and Data-Oriented Native Execution  
**Candidate:** [Your Name]  
**Degree Program:** M.Sc. in Computer Science  
**Planned Duration:** 6 Months (30 ECTS)  
**Keywords:** Automated Theorem Proving, Higher-Order Logic, Leo-III, AVATAR Splitting, Combinatory Superposition, Elixir/BEAM, Rustler, SIMD, Agentic Code Synthesis, Profile-Guided Proof Search, System-One Decision Models, Nx/Axon

---

## Abstract

State-of-the-art Higher-Order Logic (HOL) Automated Theorem Provers (ATPs) such as Leo-III rely on tens of thousands of lines of tightly coupled, pointer-heavy code to balance calculus expressiveness with runtime performance. Earlier efforts in Leo-III to parallelize proof search via fine-grained multi-agent blackboard architectures (`AuctionBlackboard`, `RuleAgent`, and `TreeContext` splitting) encountered severe lock contention and index pollution, leading modern Leo-III to revert to sequential saturation schedules (`SeqLoop` / `ScheduledRun`). Meanwhile, modernizing ATPs toward flat data-oriented memory layouts, SIMD vectorization, incremental SAT/SMT embedding, and adaptive parallel micro-searches incurs prohibitive manual engineering cost and high risk of soundness regressions. While Large Language Model (LLM) coding agents ("vibe coding") accelerate low-level systems prototyping, unverified LLM-generated deduction code is fundamentally untrustworthy due to subtle invariants in binder manipulation, Skolemization, term orderings, and higher-order unification.

This thesis proposes **Astraea**, an oracle-guided agentic synthesis harness and modular parallel micro-prover architecture that picks up where Leo-III's multi-agent architecture left off, incorporating modern insights from Vampire (AVATAR, combinatory superposition), Zipperposition ($\lambda\text{Sup}$), and Lash (integer-indexed C cores). First, we design a flat, index-addressed Intermediate Representation (IR) for classical higher-order logic (THF0)—evaluating binder-free typed combinators ($S, K, I, B, C$) alongside spine/de Bruijn representations—paired with a purely functional reference interpreter and LCF-style proof checker in Elixir. Second, we build a multi-tier verification harness (property-based testing, differential fuzzing against Leo-III, and independent proof-trace validation) to gate an LLM agent synthesizing zero-copy, SIMD-accelerated Rust micro-prover NIFs. Finally, we replace fine-grained rule-locking with coarse-grained Elixir/OTP orchestration: combining top-level goal decomposition, AVATAR-style clause splitting over an incremental SAT NIF, content-addressed Skolemization for safe lemma sharing, and Profile-Guided Optimization (PGO) via parallel shallow probes and native in-loop Nx decision models.

---

## 1. Introduction & Motivation

Automated Theorem Proving in classical Higher-Order Logic (HOL) underpins formal verification, proof assistant automation ("hammers" such as Isabelle's Sledgehammer [BBN16]), and logic embeddings [SB21, GSB17]. Leo-III implements extensional higher-order paramodulation within the Given-Clause saturation loop, cooperating with external first-order ATPs and SMT solvers [SB18, S18].

Examining the architectural evolution of Leo-III and contemporary provers reveals three critical challenges and opportunities:

1. **Lessons from Leo-III's Shelved Blackboard Architecture:** Leo-III was originally conceived around a concurrent multi-agent blackboard architecture [SWB16], where individual calculus rules (`ParamodRule`, `FuncExtRule`, `SubsumptionRule`) operated as concurrent agents over a shared mutable `Blackboard` and branching `TreeContextSet` (archived in Leo-III commit `28a8c43a`). Because single inference steps execute in microseconds and require global forward/backward subsumption, fine-grained agent synchronization caused severe lock contention, while context-trees polluted term indexes. Consequently, Leo-III reverted to sequential strategy schedules (`ScheduledRun`), leaving conjecture/clause splitting as an open architectural goal.
2. **Pointer-Chasing DAGs vs. Data-Oriented Hardware:** Traditional HOL provers represent terms as heap-allocated DAGs with dynamic $\lambda$-binders and de Bruijn index shifting. Recent breakthroughs—such as **Lash**'s compact 32-bit integer term tables [BK22], **Zipperposition**'s pragmatic pattern/fluid unification [BBV21], and **Vampire-HO**'s binder-free *Combinatory Superposition* [BR20]—show that higher-order deduction can be reformulated over flat, applicative data structures amenable to CPU cache locality, SIMD vectorization, and potentially GPU execution.
3. **Monolithic Schedules vs. Profile-Guided Micro-Proving:** Rather than hoping a single sequential saturation loop avoids combinatorial explosion, an outer orchestrator can decompose goals, run dozens of 50–200ms parallel "probe" searches over lock-free native arenas, harvest proof telemetry (watchlists, productive symbol precedences, active rules), and specialize subsequent runs—analogous to Profile-Guided Optimization (PGO) in compilers.

Yet implementing flat-memory, SIMD-accelerated HOL deduction kernels by hand is notoriously error-prone, while naive LLM code generation ("vibe coding") fails because *99% correctness in an ATP equals 0% soundness*.

**Core Thesis Hypothesis:** *By grounding an LLM synthesis agent in a declarative Elixir Reference IR, differential testing against Leo-III, and a small trusted proof-checking kernel, we can safely synthesize lock-free, data-oriented Rust/SIMD micro-prover kernels and orchestrate them in Elixir/OTP to realize Leo-III's original vision of cooperative parallel HOL deduction.*

---

## 2. Background & Architectural Foundations from Modern Provers

This thesis synthesizes four foundational threads from automated reasoning and systems engineering:

* **Extensional Higher-Order Paramodulation & Sound Parallelism (Leo-III):** Steen and Benzmüller [S18, SB21] define Leo-III's calculus (`Rules.scala`), where rules like negative functional extensionality (`FuncExt`, status `SZS_EquiSatisfiable`) dynamically introduce fresh Skolem terms. In parallel proof search with lemma exchange, naive counter-based Skolemization is **unsound** due to symbol collisions across workers. Adopting **content-addressed (structural) Skolemization** (hashing the canonicalized $\lambda$-abstraction, akin to Hilbert's $\epsilon$-operator) makes parallel lemma sharing mathematically sound without central coordination.
* **AVATAR Clause Splitting via Incremental SAT (Vampire):** Rather than tracking case splits inside complex context-indexed term banks (`TreeContext`), Voronkov's **AVATAR** architecture [Vor14] delegates variable-disjoint clause splits ($C_1 \lor C_2$ with $\text{FV}(C_1) \cap \text{FV}(C_2) = \emptyset$) to an in-process incremental SAT solver, keeping each saturation worker's clause set purely conjunctive and fast.
* **Pragmatic Higher-Order & Combinatory Deduction (Zipperposition, Vampire-HO, Lash):** While general Huet pre-unification [Hue75] is undecidable and infinitely branching, *Higher-Order Pattern Unification* is decidable and unitary. Furthermore, translating $\lambda$-abstractions into typed Schönfinkel–Curry combinators ($S, K, I, B, C$) [BR20] eliminates bound variables and de Bruijn index shifting altogether, turning HOL terms into flat applicative arrays ideal for integer-indexed arenas [BK22] and SIMD feature-vector subsumption [Sch13].
* **Watchlists, Iterative Learning & LCF Verification:** E Prover's watchlists and MaLARea/ENIGMA [JU17] demonstrate that intermediate clauses and symbol statistics harvested from short runs strongly guide subsequent saturation searches. Meanwhile, LCF-style proof checking separates untrusted, aggressively optimized native search from a tiny, auditable proof checker.

---

## 3. Research Questions

* **RQ1 (Data-Oriented HOL Representation):** How effectively can monomorphic Higher-Order Logic (THF0)—comparing spine/de Bruijn terms against binder-free typed combinators ($S, K, I, B, C$)—be represented in a contiguous, index-addressed Arena IR that serves both as an executable Elixir specification and a zero-copy layout for Rust/SIMD execution?
* **RQ2 (Oracle-Guided Agentic Synthesis):** Can an automated verification harness—combining `StreamData` property invariants, differential fuzzing against Leo-III, and an LCF-style Elixir proof checker—reliably detect and self-heal soundness and memory-layout bugs during LLM synthesis of native Rust/SIMD deduction kernels?
* **RQ3 (Coarse-Grained Parallelism & Profile-Guided Micro-Proving):** Does replacing Leo-III's sequential `ScheduledRun` (and its former fine-grained `Blackboard`) with Elixir/OTP goal decomposition, stateful AVATAR SAT NIF splitting, and telemetry-guided parallel micro-searches improve solve rates and latency on TPTP THF0 sub-goals?

---

## 4. Proposed System Architecture & Methodology

The proposed system (**Astraea**) resolves Leo-III's historical concurrency bottleneck by strictly separating **macro-level parallel coordination (Elixir/OTP)** from **lock-free micro-level saturation (Rust/SIMD)**:

```
+-------------------------------------------------------------------------+
| Layer 1: Elixir Macro DSL & Parallel Orchestrator (OTP)                 |
| - Sequent goal decomposition (Alpha splits) & SInE premise selection    |
| - AVATAR Split Coordinator backed by stateful Incremental SAT NIF       |
| - Parallel Probe Runner (50-200ms) + PGO Telemetry / Watchlist Compiler |
+------------------------------------+------------------------------------+
                                     | Zero-Copy Flat Binary Arena IR
                                     | + Content-Addressed Skolem Hashes
                                     v
+-------------------------------------------------------------------------+
| Layer 2: Canonical Logic IR & Trusted Kernel (Pure Elixir)              |
| - Flat 32-bit Index-Addressed Term/Clause Arena (Spine vs. Combinators) |
| - Reference Calculus Interpreter (ground-truth oracle for testing)      |
| - LCF-Style Proof Certificate Checker (~300 LOC soundness gate)         |
+------------------------------------+------------------------------------+
                                     |
           +-------------------------+-------------------------+
           | Compile-Time / Synthesis Loop                     | Runtime NIFs
           v                                                   v
+------------------------------------+   +--------------------------------+
| Layer 3: Agentic Synthesis Harness |   | Layer 4: Lock-Free Rust Kernels|
| - LLM Agent generating Rust / SIMD |   | - Isolated per-worker Arenas   |
| - Gate 1: StreamData HOL properties|   | - Pattern/Bounded Unification  |
| - Gate 2: Diff-test vs Elixir &    |   |   & Combinatory Paramodulation |
|           Leo-III                  |   | - SIMD Feature-Vector Index    |
| - Gate 3: Trusted Proof Checker    |   | - Stateful CaDiCaL / Z3 NIFs   |
| - Gate 4: Benchee / Cache Profiler |   +--------------------------------+
+------------------------------------+
```

### 4.1 Canonical Flat Logic IR, Combinators, & Sound Skolemization
* **Contiguous Arena Encoding:** Terms and types in monomorphic THF0 are stored in flat binary/tuple arenas (`<<tag::8, flags::8, type_id::16, left::32, right::32>>`) with structural hash-consing (inspired by Lash [BK22]). We support lowering $\lambda$-terms either to explicit spine/de Bruijn nodes or binder-free $S, K, I, B, C$ combinators [BR20] to evaluate SIMD friendliness.
* **Content-Addressed Skolemization:** Skolem constants introduced during CNF or negative `FuncExt` receive deterministic IDs derived from the cryptographic/structural hash of the canonicalized quantified predicate, guaranteeing soundness when parallel workers exchange unit lemmas.
* **Trusted Proof Checker:** Every refutation returned by a native worker must include a compact derivation DAG verified by a ~300-line pure Elixir kernel (checking substitution instances, reflexivity, congruence, $\beta\eta$/combinator steps, and resolution).

### 4.2 The Verification-Gated "Vibe Coding" Harness
An automated Elixir driver orchestrates an LLM coding agent to synthesize and optimize the Layer 4 Rust (`rustler`) modules under four strict gates:
1. **Property Gate (`StreamData`):** Fuzzes thousands of well-typed HOL terms, testing type preservation, Skolem hash determinism, combinator bracket-abstraction roundtrips, and KBO irreflexivity/transitivity.
2. **Differential Oracle Gate:** Compares normal forms, KBO orientations, and unifiers produced by the Rust NIF directly against the Elixir Reference Interpreter and Leo-III.
3. **Proof-Checked TPTP Soundness Gate:** Executes synthesized kernels on satisfiable (`CSA`/`SAT`) and theorem (`THM`) TPTP THF0 benchmarks; any uncheckable proof or false refutation automatically returns minimal failing AST counterexamples to the agent.
4. **Hardware Telemetry Gate:** Benchmarks instruction throughput and memory allocations, instructing the agent to vectorize feature-vector subsumption (`FVIndex`) using portable SIMD (`std::simd` / NEON / AVX2) without violating Gates 1–3.

### 4.3 Picking Up Leo-III's Parallelism: OTP, AVATAR & PGO Probes
1. **Conjecture Splitting & AVATAR:** Fulfilling Leo-III's open roadmap for an intermediate splitting layer, Elixir decomposes top-level goals ($\forall, \implies, \land$) into AND-parallel sub-goals, while variable-disjoint disjunctive clauses ($C_1 \lor C_2$) are managed via an in-memory CaDiCaL SAT NIF (AVATAR).
2. **Parallel Shallow Probes (50–200ms):** OTP `Task` supervisors spawn isolated, lock-free Rust micro-prover arenas across CPU cores with diverse heuristic configurations.
3. **Profile-Guided Re-Specialization (PGO):** If shallow probes time out without refutation, Elixir aggregates their telemetry:
   * **Lemma / Watchlist Harvesting:** Compact, high-utility unit equalities discovered by any worker are shared and added to a prioritized watchlist.
   * **Dynamic KBO Precedence Re-Weighting:** Symbols frequently participating in simplifying rewrites are promoted in the KBO precedence ordering.
   * **Rule Pruning:** Unused higher-order rules (e.g., Boolean extensionality or primitive substitution on purely applicative sub-goals) are compiled out for a focused follow-up saturation burst.
4. **In-Loop System-One Guidance (Nx / Axon):** Beyond coarse PGO, native `Nx.Defn` decision heads (compiled via `EXLA` / `NxSimd`) provide sub-50µs in-process proof guidance (Given-Clause batch re-ranking, strategy selection, and premise slicing) directly over Astraea's 16-lane feature vector tables without Python or IPC overhead (see detailed architecture in [Notes/nx_proof_guidance_plan.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/nx_proof_guidance_plan.md)).

---

## 5. Scope Management (6-Month Feasibility)

To ensure rigorous completion within 6 months (30 ECTS), deliverables are bounded as follows:

* **In-Scope (Core Deliverables):**
  * Monomorphic classical Higher-Order Logic (**TPTP THF0**: base/function types, application, $\lambda$-abstraction + combinator translation, equality, standard connectives, content-addressed Skolemization).
  * Pure Elixir Reference IR, `StreamData` HOL generators, and LCF-style Proof Certificate Checker.
  * Automated Agentic Synthesis Harness (4-gate loop) with logged synthesis experiments.
  * Lock-free Rustler Micro-Prover NIF (hash-consed flat arena, KBO, pattern/bounded unification, Given-Clause loop, SIMD `FVIndex` subsumption) + stateful CaDiCaL SAT NIF for AVATAR splitting.
  * Multi-core Elixir/OTP orchestrator implementing goal splitting, parallel shallow probes, and watchlist/precedence PGO.
* **Out-of-Scope / Stretch Goals (Optional Extensions):**
  * Full rank-1 polymorphism (TH1), general Axiom of Choice, and modal logic pre-processors.
  * Multi-machine BEAM cluster distribution (architecturally supported via OTP, benchmarked on single multi-core node first; see [Notes/distributed_parallelism_plan.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/distributed_parallelism_plan.md)).
  * In-loop System-One decision models via native `Nx.Defn` / `Axon` for given-clause re-ranking and unification branch selection (see [Notes/nx_proof_guidance_plan.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/nx_proof_guidance_plan.md)).
  * Compiling the binder-free combinator arena directly to WebGPU/WGSL compute shaders.

---

## 6. Evaluation Plan

1. **Calculus & Representation Trade-offs (RQ1):**
   * Compare memory footprint, cache behavior, and throughput of Spine/de Bruijn vs. Combinatory ($S, K, I, B, C$) flat arenas across Pure Elixir, synthesized Rust, and SIMD-enabled Rust, benchmarked against Leo-III (Scala 3 / JVM).
2. **Agentic Harness Autonomy & Defect Interception (RQ2):**
   * Across 5 synthesis targets (Arena/Hash-consing, $\beta\eta$/Combinator Reducer, KBO Ordering, Unifier, SIMD FV-Subsumption), record: iterations to convergence, soundness bugs caught per gate (property vs. differential vs. proof-checker), and required human interventions.
3. **Parallelism, AVATAR & PGO Ablation Study (RQ3):**
   * Evaluate on ~300 THF0 problems from the TPTP v8/v9 library (including both theorems and counter-satisfiable problems to verify soundness).
   * Compare solve rates and wall-clock time across: (a) sequential single-strategy baseline, (b) static parallel portfolio, (c) AVATAR + goal decomposition, and (d) full PGO probe-and-specialize orchestration vs. stock Leo-III `ScheduledRun`.

---

## 7. Proposed Timeline (24 Weeks)

| Phase | Weeks | Milestones & Deliverables |
| :--- | :---: | :--- |
| **WP1: IR, Combinators & Soundness Design** | 1–4 | Literature & Leo-III codebase analysis; TPTP THF0 parser in Elixir; flat Arena IR supporting spine/combinator lowering & content-addressed Skolems. |
| **WP2: Reference Oracle & Proof Kernel** | 5–8 | Implement Elixir Reference Interpreter, `StreamData` well-typed HOL generators, ~300-LOC Trusted Proof Checker, and Leo-III differential runner. |
| **WP3: Agentic Synthesis Harness** | 9–13 | Build automated 4-gate LLM synthesis loop; synthesize & verify Rustler Term Arena, Normalizer, KBO, and Unifier; collect RQ2 synthesis logs. |
| **WP4: Native Micro-Engine, SIMD & AVATAR** | 14–17 | Synthesize lock-free Given-Clause micro-loop and SIMD `FVIndex` subsumption in Rust; integrate stateful CaDiCaL NIF for AVATAR splitting. |
| **WP5: OTP Orchestration & PGO Evaluation** | 18–20 | Implement Elixir sequent splitter, 100ms parallel probes, watchlist/KBO PGO feedback loop; execute full TPTP THF0 ablation benchmarks (RQ1, RQ3). |
| **WP6: Thesis Writing & Defense** | 21–24 | Statistical evaluation of proof search and agent synthesis metrics; write, revise, and submit Master's thesis; prepare defense talk. |

---

## 8. Preliminary References

1. **[SB21]** Steen, A., Benzmüller, C. (2021). *Extensional Higher-Order Paramodulation in Leo-III*. Journal of Automated Reasoning, 65, 775–807.
2. **[S18]** Steen, A. (2018). *Extensional Paramodulation for Higher-Order Logic and its Effective Implementation Leo-III*. PhD Dissertation, Freie Universität Berlin.
3. **[SB18]** Steen, A., Benzmüller, C. (2018). *The Higher-Order Prover Leo-III*. In IJCAR 2018 (LNCS 10900, pp. 108–116). Springer.
4. **[SWB16]** Steen, A., Wisniewski, M., Benzmüller, C. (2016). *Agent-Based HOL Reasoning*. In ICMS 2016 (LNCS 9725). Springer.
5. **[GSB17]** Gleißner, T., Steen, A., Benzmüller, C. (2017). *Theorem Provers for Every Normal Modal Logic*. LPAR-21, EPiC Series 46, 14–30.
6. **[Vor14]** Voronkov, A. (2014). *AVATAR: The Architecture for First-Order Theorem Provers*. In CAV 2014 (LNCS 8559, pp. 696–710). Springer.
7. **[BR20]** Bhayat, A., Reger, G. (2020). *Combinatory Superposition: Full Higher-Order Superposition Without Lambdas*. Journal of Automated Reasoning, 65, 929–963.
8. **[BBV21]** Bentkamp, A., Blanchette, J., Tourret, S., Vukmirović, P., Waldmann, U. (2021). *Superposition with Lambdas*. Journal of Automated Reasoning, 65, 893–940.
9. **[BK22]** Brown, C. E., Kaliszyk, C. (2022). *Lash 1.0 (System Description)*. In IJCAR 2022 (LNCS 13385, pp. 350–358). Springer.
10. **[Sch13]** Schulz, S. (2013). *Simple and Efficient Clause Subsumption with Feature Vector Indexing*. Automated Reasoning and Mathematics, LNCS 7788.
11. **[JU17]** Jakubův, J., Urban, J. (2017). *ENIGMA: Efficient Learning-Based Inference Guiding Machine*. In CICM 2017 (LNCS 10383). Springer.
12. **[BBN16]** Blanchette, J. C., Kaliszyk, C., Paulson, L. C., Urban, J. (2016). *Hammering towards QED*. Journal of Formalized Reasoning, 9(1), 101–148.
13. **[Hue75]** Huet, G. P. (1975). *A Unification Algorithm for Typed $\lambda$-Calculus*. Theoretical Computer Science, 1(1), 27–57.
14. **[Sud21]** Suda, M. (2021). *Vampire with Deep Reinforcement Learning*. In LPAR-23, EPiC Series in Computing 73, 341–357.
