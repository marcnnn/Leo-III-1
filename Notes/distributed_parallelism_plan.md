# Astraea: Distributed & Parallel Higher-Order Theorem Proving Plan

**Target Systems:** Single-node multi-core (`armix`, 14 physical ARM64 cores), Distributed HPC cluster (`zib`, NHR@ZIB), and local developer workstations.  
**Branch:** `astraea` (worktree: `.worktree-astraea/`)  
**Associated Context:** [Notes/master_thesis_proposal.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/master_thesis_proposal.md), [Notes/thesis_work_log.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/thesis_work_log.md), [Notes/leo3_baseline.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/leo3_baseline.md).

---

## 1. Executive Summary & Problem Formulation

Leo-III's historical parallel architecture suffered from severe synchronization bottlenecks:
1. **The Sequential Fallback:** Leo-III was forced to retreat to a sequential time-slicing schedule (`ScheduledRun`, running 17 configurations one after another with fractional shares of `MINTIME`) because its fine-grained concurrent Blackboard (agent-based) caused massive lock contention, thread starvation, and synchronization overhead on the JVM.
2. **Cold External Prover Invocations:** In cooperative proving, both Leo-III and Astraea's initial cooperation prototypes snapshot clauses, serialize them to temporary files on disk, launch an external binary (E, Vampire, cvc5) as a fresh OS process, and wait for completion. This incurs process-spawning penalties, repeated parsing/term-bank allocations, and discards all learned lemmas and saturation progress achieved by the external solver.
3. **Soundness Hazards in Parallel Lemma Sharing:** Concurrently introducing Skolem constants (e.g., via negative functional extensionality or CNF) causes symbol ID collisions across independent workers unless synchronized through central state, re-introducing serialization locks.

**The Solution:** Astraea addresses this through a distributed **Elixir/OTP actor hierarchy** coupled with **lock-free local native micro-prover loops (Rust/SIMD)**, **content-addressed (structural) Skolemization**, and **long-lived, incremental external solver sessions**.

---

## 2. Distributed Architecture & System Topology

The system separates **macro-level distributed coordination (Elixir/OTP)** from **micro-level saturation loops (Rust/SIMD)**:

```
                          ┌──────────────────────────────────────────────┐
                          │             Astraea.Coordinator              │
                          │   (TPTP Ingestion, SInE, LCF ProofChecker)   │
                          └──────────────┬───────────────────────────────┘
                                         │
                    ┌────────────────────┼────────────────────┐
                    ▼                    ▼                    ▼
          ┌───────────────────┐┌───────────────────┐┌───────────────────┐
          │   HO Engine Node  ││   HO Engine Node  ││ External ATP Node │
          │  (High CPU Cores) ││  (High CPU Cores) ││  (Fast IO / RAM)  │
          │ ┌───────────────┐ ││ ┌───────────────┐ ││ ┌───────────────┐ │
          │ │Strategy A (HO)│ ││ │Strategy C (HO)│ ││ │cvc5 Session    │ │
          │ └───────────────┘ ││ └───────────────┘ ││ └───────────────┘ │
          │ ┌───────────────┐ ││ ┌───────────────┐ ││ ┌───────────────┐ │
          │ │Strategy B (HO)│ ││ │Strategy D (HO)│ ││ │Vampire Session │ │
          │ └───────────────┘ ││ └───────────────┘ ││ └───────────────┘ │
          └─────────┬─────────┘└─────────┬─────────┘└─────────┬─────────┘
                    │                    │                    │
                    └────────────────────┼────────────────────┘
                                         ▼
                         Distributed Pub/Sub (`:pg` / Delta Mesh)
                        [Content-Addressed Unit Lemmas & Updates]
```

### 2.1 Node Specialization
1. **Coordinator Node (`coordinator@head`):**
   * Preprocessing: Parses TPTP inputs, performs monomorphization (`Astraea.Input.Monomorphizer`), builds initial binary term Arenas (`Astraea.Arena`), and computes structural hashes.
   * Telemetry & Specialization: Manages the shallow probe phase and dynamically allocates deep strategies.
   * Soundness Authority: Hosts the trusted LCF kernel (`Astraea.ProofChecker`) to independently replay and verify any claimed refutation before declaring `SZS_Theorem`.
2. **Higher-Order Worker Nodes (`worker_N@host`):**
   * Multi-core nodes running independent `Astraea.Prover` given-clause loops.
   * Every worker operates over an isolated, contiguous, lock-free memory arena with local Rustler SIMD `FVIndex` subsumption. No worker performs remote memory access or holds distributed locks during inner saturation loops.
3. **External Solver Nodes (`solver_N@host`):**
   * Dedicated nodes hosting stateful external solver daemons (cvc5, Vampire, E-Server) via long-running OTP Port drivers (`Astraea.External.Session`).
   * Eliminates binary cold-start overhead and insulates the cluster from memory consumption or unexpected crashes of external C/C++ binaries.

---

## 3. Concurrency Lifecycle & Execution Strategy

Search progresses through three distinct, coordinated phases:

### Phase 1: Shallow Parallel Probes (PGO Phase, 50–150 ms)
* **Goal:** Probe the problem landscape without committing long static timeouts.
* **Mechanism:** The Coordinator spawns 16–32 lightweight, diversified micro-provers across the cluster. Configurations vary across:
  * SInE premise selection limits (tight `15` vs. broad `90`).
  * Literal selection functions and variable-penalty biases in KBO.
  * Pattern-only unification vs. general pre-unification depth limits.
  * Boolean demodulation and Hilbert choice axiom detection (`detect_axiom`, `FuncSpec`).
* **Instant Win:** If a probe discovers a refutation during this window, the race terminates immediately.
* **Telemetry Extraction:** If unrefuted, the Coordinator harvests runtime telemetry from each probe:
  * Active symbol frequencies and successful superposition attempts.
  * Passive queue expansion rate vs. clause retention ratio.
  * Demodulation and rewriting hit rates.

### Phase 2: Dynamic Heuristic Specialization
* The Coordinator's meta-strategy compiler compiles the harvested probe telemetry into 2–4 specialized deep portfolio profiles:
  * **Equational / Rewriting Heavy:** Deep KBO ordering, aggressive boolean and unit demodulation, generous passive queues.
  * **Choice / Extensionality Heavy:** Enabled `FuncSpec`, axiomatic choice detection (`Astraea.Calculus.Choice`), and special instances quantifier enumeration.
  * **Narrow / Large Axiom Sets:** Tight SInE boundary, unit-preference weighting.

### Phase 3: Cooperative Saturation with Asynchronous Lemma Exchange
Deep internal workers and long-lived external sessions run concurrently, cooperating asynchronously via the **Distributed Lemma Mesh**.

---

## 4. Problem Updating in External Provers (`Astraea.External.Session`)

Rather than treating external ATPs as static one-shot commands, Astraea treats them as **interactive, stateful reasoning services**.

```
  ┌────────────────────────────────────────────────────────────────────────┐
  │                        Astraea.External.Session                        │
  │                           (OTP GenServer)                              │
  └───────┬────────────────────────────────────────────────────────┬───────┘
          │ Stdin Stream                                           │ Stdout Events
          │ (Formula Deltas)                                       │ (SZS, Unsat Cores)
          ▼                                                        ▼
  ┌────────────────────────────────────────────────────────────────────────┐
  │                            OS Process Port                             │
  │   - cvc5: --incremental --lang=smt2                                    │
  │   - Vampire: --mode server (TPTP interactive stream)                   │
  │   - E-Prover: e_prover --server / interactive socket                   │
  └────────────────────────────────────────────────────────────────────────┘
```

### 4.1 Update Protocols & Streaming Formats
1. **Incremental SMT-LIB2 (cvc5 / Z3):**
   * **Initialization:** Process launched once with `--incremental --lang=smt2`. Base sorts, uninterpreted constants, and initial axioms are emitted over stdin.
   * **Incremental Assertion:** As higher-order workers derive unit equalities, eliminate $\lambda$-abstractions, or synthesize choice instances, deltas are pushed non-blocking over stdin:
     ```lisp
     (assert (= (f a b) c))
     (check-sat-assuming (...))
     ```
   * **Non-blocking Polling:** Responses are read line-by-line via asynchronous Port messages (`{port, {:data, line}}`).
2. **Interactive TPTP / Server Mode (Vampire / E-Server):**
   * Vampire is started in server mode (`vampire --mode server`).
   * Newly derived first-order clauses are serialized as TFF0 via `Astraea.External.TffPrinter` and streamed over stdin as new axioms:
     ```tptp
     tff(lemma_42, axiom, f(a, b) = c).
     ```
3. **Delta Deduplication Filter:**
   * Each `Session` maintains a compact 64-bit structural hash set (`sent_hashes`).
   * Lemmas already present in the external solver's session are dropped before serialization, eliminating redundant I/O.

### 4.2 Bidirectional Knowledge Exchange
* **Inward Flow (Internal HO $\to$ External FO):** Higher-order workers simplify complex formulas into first-order unit equations and push them to the external solvers.
* **Outward Flow (External FO $\to$ Internal HO):** When an external solver detects unsatisfiability or derives high-value unit consequences, it emits the unsat core or lemma clauses. The Coordinator receives these, reconstructs their proof trace via `Astraea.External.Reconstruct`, and injects them back into the internal workers.

---

## 5. Distributed Soundness & Mathematical Guarantees

Lemma exchange across asynchronous distributed nodes introduces specific mathematical soundness risks that must be guarded by calculus-level invariants:

### 5.1 Content-Addressed (Structural) Skolemization
* **The Hazard:** In standard ATP implementations, Skolem constants are named via local sequential integers (`sk1`, `sk2`). If Worker A on Node 1 and Worker B on Node 2 independently Skolemize $\exists x.\ P(x)$, their local counters diverge or clash, causing invalid cross-worker deductions.
* **The Invariant:** Skolem constants introduced during CNF, negative `FuncExt`, or choice instantiation must have IDs derived deterministically:
  $$\text{SkolemID} = \text{Hash64}\big(\text{Canonicalize}(\lambda x.\ P(x))\big)$$
* **Guarantee:** Any two workers in the cluster Skolemizing equivalent formulas independently generate identical Skolem constant IDs, making cross-worker lemma sharing globally sound without central coordination.

### 5.2 The Zero-Trust LCF Kernel Gate
* **The Hazard:** External C/C++ binaries can suffer segmentation faults, silent memory corruption, or employ incomplete heuristic approximations.
* **The Invariant:** **No external prover output or distributed worker assertion is ever accepted as true.**
* **Verification Pipeline:**
  1. A worker or external session reporting a proof transmits the full derivation or unsat core back to the Coordinator.
  2. The Coordinator executes `Astraea.ProofChecker.verify_refutation/2` in pure Elixir.
  3. Only upon successful structural reconstruction of the empty clause ($\Box$) does the Coordinator issue `{:proved, szs_status, cert}`.

---

## 6. Implementation Work Packages & Milestones

### WP1: Content-Addressed Cluster Lemma Pool (`Astraea.LemmaPool`)
* [ ] Implement `Astraea.LemmaPool`: local `:ets` caching with decentralized `:pg` (process group) pub/sub.
* [ ] Implement structural content-addressing for Skolem constants during clausification and calculus inferences.
* [ ] Add periodic export/import hooks in `Astraea.Prover.saturation_loop`:
  * Limit broadcast to unit equations ($s = t$, $P \leftrightarrow \$true$) and ground 2-literals.
  * Rate-limit network transmissions to 50 ms batch intervals.

### WP2: Stateful External Prover Sessions (`Astraea.External.Session`)
* [ ] Implement `Astraea.External.Session` GenServer wrapping persistent OS processes through Erlang Ports.
* [ ] Build streaming drivers for:
  * `cvc5` (incremental SMT-LIB2 mode via `--incremental`).
  * `Vampire` (interactive server mode via `--mode server`).
* [ ] Add structural hash deduplication to prevent re-sending previously transmitted clauses.
* [ ] Add graceful port shutdown escalation (`SIGTERM` $\to$ `SIGKILL` via `MuonTrap`).

### WP3: Profile-Guided (PGO) Probe Runner & Specializer
* [ ] Implement `Astraea.PGO.ProbeRunner`: coordinates 50–150 ms parallel probe bursts.
* [ ] Add lightweight telemetry counters in `Astraea.Prover` (loop rate, inference success count, demodulation frequency).
* [ ] Implement `Astraea.PGO.Specializer`: compiles probe telemetry into specialized portfolio configurations.

### WP4: Distributed Coordinator & Cluster Management
* [ ] Implement `Astraea.Coordinator`: handles node registration, problem broadcasting, probe dispatch, and proof resolution.
* [ ] Integrate cluster discovery via `Node.connect/1` and `libcluster`.
* [ ] Implement cluster-wide speculative race abort: broadcast `:abcast` to terminate all remote workers and Ports within 5 ms of proof verification.

### WP5: Soundness Verification & Benchmarking on `armix` & `zib`
* [ ] Run regression suite on `TPTP-Smoke` (34 THM, 15 CSA traps) ensuring 0 false proofs.
* [ ] Benchmark on `TPTP-Dev` (237 THM) measuring gap closure against stock Leo-III baseline.
* [ ] Evaluate scaling efficiency from 1 to 14 cores on `armix`, and multi-node scaling on `zib`.

---

## 7. Failure Modes & Resilience Architecture

| Failure Event | Detection Mechanism | Recovery & Mitigation |
| :--- | :--- | :--- |
| **External Prover Crash (Segfault / OOM)** | Port exit signal (`{:EXIT, port, reason}`) handled by `Session` GenServer | Worker marks the session dead; internal strategies and remaining sessions continue unaffected without taking down the BEAM VM. |
| **Worker Node Disconnection** | Erlang node monitor (`:nodedown`) received by Coordinator | Coordinator detects dropped node, reclaims its assigned strategy slices, and redistributes them to healthy cluster nodes. |
| **External Solver Hangs / Buffers Stdin** | Timeout timer on pending requests in `Session` | Session terminates the hanging child process with `SIGKILL` and restarts a fresh session; search does not stall. |
| **Network Partition (Split-Brain)** | Coordinator node quorum | Only the Coordinator node holding the verified LCF kernel can declare an authoritative SZS result; uncoordinated sub-clusters cannot emit false proofs. |
