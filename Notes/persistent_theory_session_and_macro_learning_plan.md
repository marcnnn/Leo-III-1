# Architectural Plan: Persistent Theory Session & Incremental Sub-Proof / Macro Learning

## 1. Executive Summary

In real-world verification workflows—such as interactive theorem proving (Isabelle Sledgehammer, Lean 4 hammers, Coq/Rocq) and software verification condition (VC) pipelines (Dafny, F\*, Boogie)—hundreds or thousands of queries share a single massive, invariant background theory. 

Currently, automated provers execute in an isolated "cold-start" mode per problem, incurring severe penalties:
1. **Redundant Preprocessing:** Parsing, type-checking, definition-inlining, and clausifying megabytes of background axioms on every single query.
2. **Amnesiac Search:** Re-discovering the same foundational lemmas (e.g. algebraic properties, list operations, extensionality instances) repeatedly across independent queries.
3. **Unsound Naive Caching:** As proven in our empirical evaluation on branch [`experiment/subproof-macro-caching`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/experiments/macro_caching_eval.exs), 78.7% of intermediate steps in refutations depend on the negated conjecture ($\neg Goal$); caching them naively causes immediate contradictory axioms (`szs: :contradictory_axioms`).

This plan outlines the architecture for **`Astraea.Session`**: a stateful OTP theory coordinator that maintains a pre-warmed background theory in memory, extracts sound conjecture-free sub-proofs from successful refutations, indexes them as directed rewrite rules in the demodulator (preventing clause swamping), and generalizes recurring multi-step inference chains into macro rules.

---

## 2. System Architecture

```mermaid
flowchart TD
    subgraph Client ["Client Verification Pipeline (Isabelle / Sledgehammer / Dafny)"]
        Batch["Batch Query Stream: Goal 1, Goal 2, ... Goal N"]
    end

    subgraph Session ["Astraea.Session (OTP Theory Coordinator)"]
        Theory["Shared Background Theory (Axioms, Definitions, Types)"]
        WarmedArena["Pre-warmed Astraea.Arena & Symbol Registry"]
        DemodCache["Persistent Demodulator (Oriented KBO Rewrite Rules)"]
        MacroIndex["Anti-Unified Macro Rule Cache"]
        LineageTracker["Sub-Proof Lineage Tracker"]
    end

    subgraph WorkerPool ["Ephemeral Saturation Worker Pool"]
        W1["Worker 1 (Goal K)"]
        W2["Worker 2 (Goal K+1)"]
    end

    subgraph Verification ["Trusted Kernel Gate"]
        LCF["Astraea.ProofChecker (derive_steps/2)"]
    end

    Batch -->|Initialize Theory| Theory
    Theory --> WarmedArena
    WarmedArena --> DemodCache

    Batch -->|Query Goal K| W1
    WarmedArena -.->|Spawn with Warm State & Demod Rules| W1
    DemodCache -.->|Eager Simplification| W1
    MacroIndex -.->|Macro Rules| W1

    W1 -->|Refutation DAG| LCF
    LCF -->|Verified Steps| LineageTracker
    
    LineageTracker -->|Goal-Dependent Inferences (~Goal \/ C)| Discard["Discard / Local Use Only"]
    LineageTracker -->|Pure Theory Lemmas (Theory |- L)| DemodCache
    LineageTracker -->|Isomorphic Patterns| MacroIndex
    
    W1 -->|SZS Theorem & Certificate| Client
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

### Phase 1: Session Core & Pre-Warmed Theory Server
* **Module:** `Astraea.Session` (OTP `GenServer`)
  * `start_link(background_files, opts)`: Parses and elaborates background axioms once.
  * Builds immutable background `Astraea.Arena`, `Demodulator`, and symbol index.
  * Computes KBO weights and precedences across the shared signature.
* **Module:** `Astraea.Session.Worker`
  * Spawns an isolated prover instance per goal query.
  * Ingests local conjecture, runs SInE only over the local goal against the pre-indexed theory, and seeds search with warm demodulation rules.
* **Deliverable:** Zero-overhead warm query dispatch; eliminate 300ms–1,000ms JVM/parsing overhead per query.

### Phase 2: Refutation Lineage Analyzer & Lemma Harvester
* **Module:** `Astraea.Session.Lineage`
  * Leverages [`ProofChecker.derive_steps/2`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/proof_checker.ex#L107) to reconstruct full clauses for all proof nodes.
  * Identifies `conjecture_dependent?` status for all derived clauses.
  * Filters for unit equalities ($s = t$), unit predicate literals ($P(t)$), and small horn clauses.
* **Module:** `Astraea.Session.DemodCache`
  * Validates KBO orientability of extracted equalities.
  * Dynamically installs new rewrite rules into the shared `Demodulator` state.
* **Deliverable:** Continuous, sound accumulation of rewrite rules across sequential queries.

### Phase 3: Macro-Inference Synthesis & Anti-Unification
* **Module:** `Astraea.Calculus.AntiUnify` (Elixir port of `PatternAntiUnification.scala`)
  * Implements higher-order pattern anti-unification for de Bruijn terms.
* **Module:** `Astraea.Session.MacroIndex`
  * Detects recurring multi-step sub-proof patterns across refutations (`inst_resolve`, `superposition`, `ext_paramod`, and custom 3+ step chains).
  * Constructs parametric macro rules that fire as single composite inferences during worker saturation.
* **Deliverable:** Compressing search tree depth by skipping intermediate clause generation for known derivation patterns.

### Phase 4: Batch Benchmarking & Real-World Evaluation
* **Target Corpora:**
  1. **Isabelle Sledgehammer THF0 Exports (`ITP` Domain):** High-axiom shared library batches.
  2. **Mizar / Set Theory Collections (`SEU` / `SET` Domains):** Deep algebraic and set-theoretic theory hierarchies.
  3. **CASC LTB Batch Harness (`contrib/ltbrun`):** Standard competitive batch protocol.
* **Metrics to Measure:**
  * **Throughput:** Queries proved per minute (cold-start vs. warm session).
  * **Solve-Rate Lift:** Number of previously open/timeout VCs closed by accumulated lemmas.
  * **Search Depth & Iterations:** Reduction in given-clause saturation loops.
  * **Swamping Overhead:** Passive queue memory and forward subsumption latency under growing lemma caches.

---

## 5. Risk Assessment & Mitigations

| Risk | Impact | Mitigation Strategy |
| :--- | :---: | :--- |
| **Conjecture Contamination** | Critical (Unsoundness) | Strict lineage tracking: any clause with $\ge 1$ conjecture ancestor is rejected from global lemma cache. |
| **The Utility Problem (Clause Swamping)** | High (Search Slowdown) | Strict selective admission: 100% of equational lemmas routed to Demodulator (rewriting only); non-equational lemmas capped by weight and limited to unit clauses. |
| **KBO Termination Cycles** | High (Divergence in Rewriter) | Every equational lemma checked against `Ordering.kbo_compare/3` before insertion; non-orientable equations never added to demodulator. |
| **Memory Growth across Long Sessions** | Medium | LRU eviction policy on macro-rule cache; maximum active demodulation rules bounded (e.g. top 500 by firing frequency). |
