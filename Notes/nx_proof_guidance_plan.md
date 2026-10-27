# Astraea: In-Loop System-One Proof Guidance via Native `Nx.Defn` Decision Models

**Target Architecture:** Elixir/OTP, `Nx.Defn` / `Axon` JIT compilation (`EXLA` / `NxSimd`), and lock-free native micro-arenas.  
**Branch:** `astraea`  
**Associated Context:** [Notes/master_thesis_proposal.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/master_thesis_proposal.md), [Notes/thesis_work_log.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/thesis_work_log.md), [Notes/distributed_parallelism_plan.md](file:///Users/marcnickert/Projects/opensource/Leo-III/Notes/distributed_parallelism_plan.md), [Astraea.Engine.Kernels](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/engine/kernels.ex), [Astraea.NxKernel](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/nx_kernel.ex).

---

## 1. Executive Summary & Problem Formulation

Automated theorem proving (ATP) in higher-order logic (HOL) suffers from acute combinatorial search explosions. In saturation algorithms (such as Leo-III's and Astraea's Given-Clause loops), the number of generated passive clauses grows exponentially with search depth. Traditional provers manage this via static heuristics (such as symbol weight, FIFO clause age, or SInE premise selection). While computationally cheap, these heuristics lack semantic awareness of the conjecture.

Recent attempts to apply Machine Learning (ML) and Large Language Models (LLMs) to proof search have encountered a fundamental **latency mismatch**:
1. **The Autoregressive Penalty:** Standard generative LLMs (GPT-4, Claude, Llama) decode tokens autoregressively, taking 500ms to 5,000ms per query. Invoking an LLM inside an inner saturation loop—which must process thousands of clauses per second—destroys prover throughput.
2. **Foreign Process / IPC Overhead:** Running external Python microservices (e.g., PyTorch, HuggingFace, FastAPI) over HTTP or Unix sockets introduces 20ms to 50ms serialization and network roundtrip latency per batch.
3. **Grammar & Parsing Failures:** Free-form or JSON-constrained generative outputs require complex error handling, retry loops, and token budget management.

**The Solution:** Astraea adopts the **"System One" Typed Decision Model** paradigm (inspired by TypeSafe Jev, Kev, and jevlike), implemented **natively in Elixir using `Nx` and `Axon`**. Instead of generating syntax, the model computes strongly typed decisions—**`Choice`** (categorical action), **`Score`** (ordinal priority), and **`Noul`** (binary probability)—in a single forward pass over compiled numerical tensors.

By running entirely within the BEAM runtime via `Nx.Defn` and native JIT execution (`EXLA` / `NxSimd`), decision latency drops from **50 milliseconds to under 50 microseconds**, enabling semantic machine-learned guidance directly inside the inner saturation loop.

---

## 2. Decision Model Topology & Calculus Integration

```
                         ┌──────────────────────────────────────────────┐
                         │              TPTP Input Problem              │
                         │             (Conjecture + Axioms)            │
                         └──────────────────────┬───────────────────────┘
                                                │
                                                ▼
                         ┌──────────────────────────────────────────────┐
                         │          Macro Strategy Selection            │
                         │      (Nx Choice Head: K RunStrategies)       │
                         └──────────────────────┬───────────────────────┘
                                                │
                                                ▼
                         ┌──────────────────────────────────────────────┐
                         │           Axiom Slicing & Premise            │
                         │       (Nx Score Head: Keep if Score > θ)     │
                         └──────────────────────┬───────────────────────┘
                                                │
                                                ▼
                 ┌──────────────────────────────────────────────────────────────┐
                 │                Astraea Inner Saturation Loop                 │
                 │                                                              │
                 │   Passive Queue (Unprocessed)           Active Clause Store  │
                 │   ┌────────────────────────┐            ┌────────────────┐   │
                 │   │ Clause 1 (fv: 16-lane) │            │ Active Set     │   │
                 │   │ Clause 2 (fv: 16-lane) │            │ (Paramod Index)│   │
                 │   │ ...                    │            └───────┬────────┘   │
                 │   │ Clause K (fv: 16-lane) │                    │            │
                 │   └───────────┬────────────┘                    │            │
                 │               │                                 │            │
                 │   Batched     ▼                                 │            │
                 │   Candidate Slice {16, N}                       │            │
                 │               │                                 │            │
                 │               ▼                                 │            │
                 │   ┌───────────────────────────┐                 │            │
                 │   │  Astraea.NxKernel         │                 │            │
                 │   │  Guidance Defn (<50µs)    │                 │            │
                 │   │  Bilinear Option-Attention│                 │            │
                 │   └───────────┬───────────────┘                 │            │
                 │               │                                 │            │
                 │   Priorities  ▼                                 │            │
                 │   Score(c_i) ∈ [0, 1]                           │            │
                 │   Noul(c_i)  < 0.05 ────► Early Prune / Discard │            │
                 │               │                                 │            │
                 │               ▼                                 │            │
                 │       Pop Best Given Clause ────────────────────┘            │
                 │                                                              │
                 └──────────────────────────────────────────────────────────────┘
```

The system partitions guidance into three distinct granularity tiers:

| Tier | Decision Primitive | Target Operation | Cadence / Budget | Input Representation |
| :--- | :---: | :--- | :--- | :--- |
| **Macro** | `Choice[K]` | Select initial `RunStrategy` (parameters: `primSubst`, `uniDepth`, `boolExt`, `choice`, `ordering`) | 1× per problem (< 1ms) | Global problem signature features |
| **Meso** | `Score` / `Noul` | Premise selection & incremental external solver handoff (E / Vampire / cvc5) | Every 100ms burst (< 200µs) | Conjecture vector $\otimes$ Axiom vectors |
| **Micro** | `Score` (batched) | Re-ranking candidate given clauses in `PassiveQueue` | Every 10–32 given loops (< 50µs) | Conjecture $\mathbf{q} \in \mathbb{R}^{16} \otimes$ Candidate block $\mathbf{C} \in \mathbb{R}^{16 \times N}$ |
| **Micro** | `Choice[M]` | Higher-order pre-unification branch selection (Imitation vs. $k$-Projections) | On flex-rigid disagreement (< 10µs) | Disagreement pair AST features |

---

## 3. Mathematical & Algorithmic Formulation in `Nx.Defn`

Astraea's [`Astraea.Engine.Kernels`](file:///Users/marcnickert/Projects/opensource/Leo-III/astraea/lib/astraea/engine/kernels.ex) already structures clause feature vectors into contiguous `{16, n}` `:u16` Structure-of-Arrays tables for SIMD subsumption. The guidance engine reuses this representation directly without intermediate memory translation.

### 3.1. Bilinear Option-Attention Scoring Head

Let $\mathbf{q} \in \mathbb{R}^{16}$ be the normalized feature vector of the negated conjecture, and $\mathbf{C} \in \mathbb{R}^{16 \times N}$ be the block of $N$ candidate clauses from the passive queue.

We project both into a shared latent semantic space $\mathbb{R}^d$ ($d = 32$) using a learned parameter matrix $\mathbf{W} \in \mathbb{R}^{16 \times d}$:
$$\mathbf{z}_q = \mathbf{q}^T \mathbf{W} \quad (\in \mathbb{R}^{d})$$
$$\mathbf{Z}_c = \mathbf{C}^T \mathbf{W} \quad (\in \mathbb{R}^{N \times d})$$

The attention priority score for each candidate clause $i \in \{1, \dots, N\}$ is given by the scaled dot-product:
$$\text{Score}(c_i) = \sigma\left(\frac{\mathbf{Z}_c[i] \cdot \mathbf{z}_q}{\sqrt{d}} + b\right)$$

In Elixir `Nx.Defn`, this compiles into a single fused vector kernel:

```elixir
defmodule Astraea.Calculus.GuidanceKernel do
  @moduledoc """
  JIT-compiled Nx.Defn decision kernels for proof steering.
  Compiled by NxSimd.Compiler or EXLA and cached in :persistent_term.
  """
  import Nx.Defn

  @lanes 16
  @embed_dim 32

  @doc """
  Scores N candidate clauses against conjecture q in a single forward pass.
  q: {16}, candidates: {16, N}, w_proj: {16, 32}, b: {1}
  Returns {N} tensor of scores in [0.0, 1.0].
  """
  defn score_candidates(q, candidates, w_proj, b) do
    # Project conjecture: {32}
    q_lat = Nx.dot(q, w_proj)

    # Project candidates: {N, 16} . {16, 32} -> {N, 32}
    cand_t = Nx.transpose(candidates)
    c_lat = Nx.dot(cand_t, w_proj)

    # Scaled dot product: {N}
    logits = (Nx.dot(c_lat, q_lat) / Nx.sqrt(@embed_dim)) + b
    Nx.sigmoid(logits)
  end

  @doc """
  Evaluates binary retention probability (Noul).
  Scores below threshold (e.g. 0.05) are pruned immediately.
  """
  defn prune_mask(scores, threshold) do
    scores >= threshold
  end

  @doc """
  Predicts categorical RunStrategy Choice[K] given global problem features.
  """
  defn predict_strategy(problem_features, w_strat, b_strat) do
    logits = Nx.dot(problem_features, w_strat) + b_strat
    Nx.exp(logits) / Nx.sum(Nx.exp(logits))
  end
end
```

---

## 4. Proof Recording & Ground-Truth Extraction

To train the guidance heads without manual supervision, Astraea leverages the **self-supervised refutation loop**: every successful refutation produces an exact ground-truth certificate.

```
                         Successful Saturation Refutation
                                        │
                                        ▼
                         TSTP Derivation DAG ($false)
                                        │
                    ┌───────────────────┴───────────────────┐
                    ▼                                       ▼
         Positive Ancestor Set                   Negative Trajectory Set
          (All nodes in DAG)                   (Processed clauses not in DAG)
               Label: 1                                   Label: 0
                    │                                       │
                    └───────────────────┬───────────────────┘
                                        ▼
                        Balanced Pairwise Training Set
                      (1 Positive : 4 Hard Negatives)
```

### 4.1. Sound Lineage Extraction
1. **Positive Clauses ($y = 1$):** Traverse the refutation DAG backwards from the empty clause `$false` via parent annotations (`ClauseAnnotation.InferredFrom`). Every clause in this transitive closure was strictly necessary for the proof.
2. **Hard Negatives ($y = 0$):** Clauses that were selected as the Given Clause and expanded into the active set during the search, but do not belong to the refutation DAG.
3. **Easy Negatives (Pruning Targets):** Clauses generated into the passive queue that were never selected before the proof finished.

### 4.2. Feature Extraction Schema
Each clause is serialized to an integer feature vector $\mathbf{v} \in \mathbb{N}^{16}$:
1. Total symbol weight.
2. Number of literals.
3. Maximum literal depth.
4. Number of positive literals.
5. Number of negative literals.
6. Number of free higher-order variables.
7. Number of applied $\lambda$-abstractions / combinator applications.
8. Maximum term order (base type = 1, predicate on individuals = 2, etc.).
9. Presence of primitive equality (`=`).
10. Presence of higher-order choice operators (`@+`, `@-`).
11. Presence of Boolean extensionality literals.
12. Number of de Bruijn bound occurrences.
13. Content-addressed Skolem dependency hash.
14. Depth in inference tree from input axioms.
15. Age (generation timestamp bucket).
16. Unification complexity class (0: first-order, 1: pattern, 2: general flex-rigid).

---

## 5. Native Training Pipeline with `Axon`

Training is executed natively within the BEAM ecosystem using `Axon` and `EXLA`, completely removing external Python/PyTorch dependencies.

```elixir
defmodule Astraea.Guidance.Model do
  @moduledoc """
  Axon model definitions for proof guidance.
  """
  require Axon

  def build_scorer do
    # Input: Concatenated conjecture features and candidate features: {batch, 32}
    Axon.input("features", shape: {nil, 32})
    |> Axon.dense(64, activation: :mish)
    |> Axon.layer_norm()
    |> Axon.dropout(rate: 0.1)
    |> Axon.dense(32, activation: :mish)
    |> Axon.dense(1, activation: :sigmoid)
  end

  def train_from_proof_logs(dataset_stream, epochs \\ 10) do
    model = build_scorer()
    loss = &Axon.Losses.binary_cross_entropy/2
    optimizer = Polaris.Optimizers.adamw(learning_rate: 1e-3, weight_decay: 1e-4)

    model
    |> Axon.Loop.trainer(loss, optimizer)
    |> Axon.Loop.metric(&Axon.Metrics.accuracy(&1, &2, threshold: 0.5), "accuracy")
    |> Axon.Loop.run(dataset_stream, %{}, epochs: epochs, compiler: EXLA)
  end
end
```

---

## 6. Runtime Integration into `Astraea.Engine.PassiveQueue`

To integrate guidance with zero per-clause synchronization overhead:

```elixir
defmodule Astraea.Engine.PassiveQueue.Guided do
  @moduledoc """
  Priority queue augmented with batched Nx decision guidance.
  """
  alias Astraea.Calculus.GuidanceKernel
  alias Astraea.NxKernel

  @batch_size 32

  def pop_given(%{passive_table: table, conjecture_fv: q_fv} = state) do
    # 1. Take top-32 candidate clause IDs from fast heuristic bucket
    case take_candidates(table, @batch_size) do
      {:empty, state} ->
        {:empty, state}

      {:ok, candidates, rest_table} ->
        # 2. Pack feature vectors into {16, 32} :u16 binary tensor
        cand_block = pack_feature_tensor(candidates)

        # 3. Call cached JIT runner (< 50 microseconds)
        runner = NxKernel.runner(&GuidanceKernel.score_candidates/4, [
          Nx.template({16}, :f32),
          Nx.template({16, @batch_size}, :f32),
          Nx.template({16, 32}, :f32),
          Nx.template({1}, :f32)
        ])

        scores = runner.(q_fv, cand_block, state.weights, state.bias)
                 |> Nx.to_flat_list()

        # 4. Select clause with maximum predicted utility
        {best_clause, _score} = 
          Enum.zip(candidates, scores)
          |> Enum.max_by(fn {_c, s} -> s end)

        {:ok, best_clause, %{state | passive_table: rest_table}}
    end
  end
end
```

---

## 7. Empirical Evaluation & Verification Protocol

The evaluation adheres to the anti-leakage manifests locked in [`benchmarks/manifests/manifest_lock.json`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/manifest_lock.json):

1. **Training Split:** Trained exclusively on refutations obtained from [`tptp_thf0_dev.txt`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/tptp_thf0_dev.txt) (300 problems).
2. **Blind Holdout:** Evaluated on [`tptp_thf0_holdout.txt`](file:///Users/marcnickert/Projects/opensource/Leo-III/benchmarks/manifests/tptp_thf0_holdout.txt) (500 problems, zero model exposure).
3. **Core Metrics:**
   * **Contraction Ratio ($CR$):**
     $$CR = \frac{\text{Given Clauses Expanded (Guided)}}{\text{Given Clauses Expanded (Standard Heuristic)}}$$
     Target: $CR < 0.60$ (at least 40% reduction in search space on solved problems).
   * **Inference Overhead:** Total time spent inside `NxKernel` relative to total proof search time. Target: $< 5\%$ of CPU budget.
   * **Net Theorem Gain:** Number of previously unsolved theorems solved within the 10s budget on `armix` due to prioritized proof paths.
