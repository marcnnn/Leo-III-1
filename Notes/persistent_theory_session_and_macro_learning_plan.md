# Architectural Plan: Persistent Theory Session & Incremental Sub-Proof / Macro Learning

## 1. Executive Summary

In real-world verification workflows—such as interactive theorem proving (Isabelle Sledgehammer, Lean 4 hammers, Coq/Rocq) and software verification condition (VC) pipelines (Dafny, F\*, Boogie)—hundreds or thousands of queries share a single massive, invariant background theory. 

Currently, automated provers execute in an isolated "cold-start" mode per problem, incurring severe penalties:
1. **Redundant Preprocessing:** Parsing, type-checking, definition-inlining, and clausifying megabytes of background axioms on every single query.
2. **Amnesiac Search:** Re-discovering the same foundational lemmas (e.g. algebraic properties, list operations, extensionality instances) repeatedly across independent queries.
3. **Unsound Naive Caching:** As proven in our empirical evaluation on branch [`experiment/subproof-macro-caching`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/experiments/macro_caching_eval.exs), 78.7% of intermediate steps in refutations depend on the negated conjecture ($\neg Goal$); caching them naively causes immediate contradictory axioms (`szs: :contradictory_axioms`).

This plan outlines the architecture for **`Astraea.Session`**: a stateful OTP theory coordinator that maintains a pre-warmed background theory in memory, extracts sound conjecture-free sub-proofs from successful refutations, indexes them as directed rewrite rules in the demodulator (preventing clause swamping), and generalizes recurring multi-step inference chains into macro rules.

---

## 2. System Architecture & Dual Protocol Interfaces

```mermaid
flowchart TD
    subgraph ClientPipelines ["Client Verification Pipelines"]
        InteractiveClient["Interactive Proof Assistant (Isabelle / Lean 4 Hammer / Dafny)"]
        BatchClient["CASC LTB Competition / StarExec Batch Runner"]
    end

    subgraph Protocols ["Dual Protocol Ingestion Engine"]
        InteractiveEngine["Astraea.Session.Interactive (Streaming JSON-RPC 2.0 / Stdio)"]
        LtbEngine["Astraea.Session.Ltb (CASC LTB Batch Specification Parser)"]
    end

    subgraph Session ["Astraea.Session (OTP Theory Coordinator)"]
        Theory["Shared Background Theory (Axioms, Definitions, Types)"]
        WarmedArena["Pre-warmed Astraea.Arena & Symbol Registry"]
        DemodCache["Persistent Demodulator (Oriented KBO Rewrite Rules)"]
        MacroIndex["Anti-Unified Macro Rule Cache"]
        LineageTracker["Astraea.Session.Lineage (Sub-Proof Lineage Tracker)"]
    end

    subgraph WorkerPool ["Ephemeral Saturation Worker Pool"]
        W1["Worker 1 (Goal K)"]
        W2["Worker 2 (Goal K+1)"]
    end

    subgraph Verification ["Trusted Kernel Gate"]
        LCF["Astraea.ProofChecker (derive_steps/2)"]
    end

    InteractiveClient <-->|JSON-RPC 2.0| InteractiveEngine
    BatchClient -->|Batch Spec & Problems| LtbEngine

    InteractiveEngine --> Session
    LtbEngine --> Session

    Session --> WarmedArena
    WarmedArena --> DemodCache

    Session -.->|Spawn with Warm State & Demod Rules| W1
    DemodCache -.->|Eager Simplification| W1
    MacroIndex -.->|Macro Rules| W1

    W1 -->|Refutation DAG| LCF
    LCF -->|Verified Steps| LineageTracker
    
    LineageTracker -->|Goal-Dependent Inferences (~Goal \/ C)| Discard["Discard / Local Use Only"]
    LineageTracker -->|Pure Theory Lemmas (Theory |- L)| DemodCache
    LineageTracker -->|Isomorphic Patterns| MacroIndex
    
    W1 -->|SZS Theorem & Certificate| Protocols
```

---

## 3. Core Technical Pillars

### 3.1. Sound Lineage Partitioning (Goal-Free vs. Conditional)
To prevent the conjecture contamination discovered during our empirical evaluation:
* For each verified refutation step $S \in \text{ProofDAG}$, compute its input ancestor set $\text{Ancestors}(S) \cap \text{InputClauses}$.
* If $\text{Ancestors}(S) \cap \text{ConjectureClauses} = \emptyset$:
  * The clause is a **sound global lemma** of the background theory.
  * Extracted and sent to the session cache.
* If $\text{Ancestors}(S) \cap \text{ConjectureClauses} = \{H_1, \dots, H_k\}$:
  * The clause is a **conditional lemma**: $(\bigwedge H_i) \implies S$.
  * Cached in an indexed hypothesis table, reusable only by sibling queries that share the identical local assumptions.

### 3.2. Directed Demodulation over General Resolution (Combating the Utility Problem)
Adding hundreds of arbitrary lemmas to the given-clause passive queue causes combinatorial explosion ("clause swamping").
* Equational lemmas $s = t$ are oriented using KBO precedence:
  $$s \succ_{KBO} t \implies s \to t$$
* Stored strictly in [`Astraea.Engine.Demodulator`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/engine/demodulator.ex).
* **Search Benefit:** Applied deterministically during forward and backward rewriting. They shrink clause size and reduce search depth without adding a single branching alternative to the given-clause queue.

### 3.3. Content-Addressed Structural Skolemization
Cross-query lemma sharing in higher-order logic usually fails due to non-standardized Skolem symbols.
* Astraea's content-addressed Skolem hashing ([`Astraea.Arena.skolem_hash/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/arena.ex)):
  $$\text{skolem\_id} = \text{SHA-256}(\text{Canonicalized De Bruijn Body})$$
* Guarantees that any witness function introduced in Goal 1 has the identical identity and type if introduced in Goal 2, making lemma exchange mathematically sound without symbol alpha-conversion.

### 3.4. Parametric Generalization via Anti-Unification
When sub-proofs share derivation topology but differ in concrete terms:
* Apply higher-order pattern anti-unification ([`PatternAntiUnification.scala`](file:///Users/marcnickert/Projects/opensource/Leo-III/src/main/scala/leo/modules/calculus/AntiUnification.scala)) to compute the least general generalization (LGG).
* Generalize concrete constant applications into quantified variables, producing reusable macro inference templates.

---

## 4. Phase-by-Phase Implementation Roadmap

### Phase 1: Session Core & Dual Protocol Engine (Completed in Entry 013)
* **Module:** [`Astraea.Session`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session.ex) (OTP `GenServer`)
  * Pre-clausifies background theory and builds warm `Astraea.Arena`, `Demodulator`, and symbol tables.
  * Dispatches queries without re-parsing or re-clausifying background axioms.
* **Module:** [`Astraea.Session.Interactive`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session/interactive.ex)
  * Bi-directional streaming JSON-RPC 2.0 interface (`init_theory`, `prove_goal`, `session_stats`).
* **Module:** [`Astraea.Session.Ltb`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session/ltb.ex)
  * Standard CASC Large Theory Batch specification parser and sequential batch execution engine.

### Phase 2: Refutation Lineage Analyzer & Demodulator Cache (Completed in Entry 013)
* **Module:** [`Astraea.Session.Lineage`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session/lineage.ex)
  * Uses [`ProofChecker.derive_steps/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex#L107) to inspect refutation DAGs.
  * Partitions inferences into pure theory lemmas vs. conjecture-dependent steps.
* **Module:** [`Astraea.Session.DemodCache`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session/demod_cache.ex)
  * Evaluates KBO orientability of extracted unit equations and registers them into the active demodulator.

### Phase 3: Macro-Inference Synthesis & Anti-Unification
* **Module:** `Astraea.Calculus.AntiUnify` (Elixir port of `PatternAntiUnification.scala`)
  * Implements higher-order pattern anti-unification for de Bruijn terms.
* **Module:** `Astraea.Session.MacroIndex`
  * Detects recurring multi-step sub-proof patterns across refutations (`inst_resolve`, `superposition`, `ext_paramod`, and custom 3+ step chains).
  * Constructs parametric macro rules that fire as single composite inferences during worker saturation.
* **Deliverable:** Compressing search tree depth by skipping intermediate clause generation for known derivation patterns.

---

## 5. Verification Protocol: The Last CASC LTB Division (CASC-J11 & CASC-28)

To rigorously validate the system under real-world competitive conditions, the implementation will be verified against the benchmark suites and batch specifications of the **last active CASC LTB (Large Theory Batch) competitions**:

### 5.1. Target Competition Corpora
* **CASC-J11 (2022) LTB Division** *(The final active CASC LTB competition before the division went on hiatus in CASC-29)*:
  * **`HOL` Category:** Problems derived from Isabelle/HOL theory libraries with deep axiom dependencies.
  * **`MZR` Category:** Problems translated from the Mizar Mathematical Library (MML).
* **CASC-28 (2021) LTB Division**:
  * Benchmark problems evaluated on StarExec with wall-clock time limits and batch includes.

### 5.2. Verification Execution Setup
* Run via [`Astraea.Session.Ltb.run_batch/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/session/ltb.ex) using the exact CASC batch specification files (`BatchConfiguration`, `BatchIncludes`, `BatchProblems`).
* Execute both sequential ordering (`execution.order ordered`) and parallel batches on `armix`.

### 5.3. Comparison & Metrics to Measure

| Experiment Condition | Description | Primary Metrics |
| :--- | :--- | :--- |
| **Baseline (Cold-Start)** | Stock prover execution per problem (re-parsing axioms from scratch per query). | Baseline solve count, total wall-clock time, average parsing overhead. |
| **Warm Session (No Caching)** | `Astraea.Session` with pre-clausified background theory, but lemma harvesting disabled. | Speedup due to elimination of redundant parsing and clausification. |
| **Full Session (With Sound Lemma Caching)** | `Astraea.Session` with active `Lineage` harvesting and `DemodCache` rewriting. | **Solve-rate lift** (newly solved problems), reduction in saturation iterations, demodulator hit rate. |

* **Verification Acceptance Gates:**
  1. **100% LCF Kernel Pass Rate:** Every emitted refutation certificate passes [`Astraea.ProofChecker.verify_refutation/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex).
  2. **Zero Contradictory Axioms / Soundness Traps:** 0 false proofs across any satisfiability or counter-satisfiable control problems in the batch.
  3. **Positive Throughput Lift:** Warm session must reduce overall batch wall-clock time compared to cold-start.
  4. **Bounded Queue Growth:** Passive clause queue must remain bounded, proving that directed demodulation successfully prevents clause swamping.

---

## 6. Risk Assessment & Mitigations

| Risk | Impact | Mitigation Strategy |
| :--- | :---: | :--- |
| **Conjecture Contamination** | Critical (Unsoundness) | Strict lineage tracking: any clause with $\ge 1$ conjecture ancestor is rejected from global lemma cache. |
| **The Utility Problem (Clause Swamping)** | High (Search Slowdown) | Strict selective admission: 100% of equational lemmas routed to Demodulator (rewriting only); non-equational lemmas capped by weight and limited to unit clauses. |
| **KBO Termination Cycles** | High (Divergence in Rewriter) | Every equational lemma checked against `Ordering.kbo_compare/3` before insertion; non-orientable equations never added to demodulator. |
| **Memory Growth across Long Sessions** | Medium | LRU eviction policy on macro-rule cache; maximum active demodulation rules bounded (e.g. top 500 by firing frequency). |
