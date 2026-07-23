# ARA — Analysis of Randomized Algorithms in Lean 4

A framework where a randomized algorithm is written **once** and that single definition serves for example (depending on the abstract source of randomness):

* an **executable program** (`IO`, real randomness — `#eval` it),
* a **distribution** (`PMF`, the mathematical specification),
* a **timed algorithm** (`TimeMT ℕ M`, cost accumulated per `tick`),
* a **benchmark** (`TimeMT ℕ IO`, executable with a clock).

Correctness and expected-complexity proofs then follow a fixed recipe in
which everything except the *mathematics of the algorithm itself* is
tried to be automated by the framework.

Author: Antoine du Fresne von Hohenesche.

Helped by Claude code: Opus and Fable models were used.

## Start here

**[`ARA/Algorithms/Tutorial.lean`](ARA/Algorithms/Tutorial.lean)** is a
tutorial to formalize a toy algorithm (`RandMax`) which is verified 
end-to-end in six numbered steps.

For the choice and consequences of our design (why shallow embedding, `PMF`/Giry monad, correctness tiers, known limitations): see [`DESIGN.md`](DESIGN.md).

## Layout — three layers

```
ARA/
├── Infrastructure/
│   ├── Randomness/     the semantic layer: what a random program *means*
│   │   ├── LawfulRandMonad.lean   `RandMonad` (uniform `randFin`) + `toPMF`
│   │   │                          semantics, 𝒟[e | M], post-processing lemmas
│   │   ├── Prob.lean              the probability core: `expVal`, `𝔼[·]`, the
│   │   │                          event algebra `prob`, Markov, and the
│   │   │                          output notation ℙ[e = v | M] / ℙ[e ∈ S | M]
│   │   ├── RandVec.lean           list, 0/1 and finite-grid entropy sources
│   │   │                          (`randIdx`, `randBit`/`randVec`,
│   │   │                          `randElem`/`randVecOn`) with the counting
│   │   │                          principles #accepting / #choices
│   │   └── Geometric.lean         geometric + `geometricTrials` laws (retry
│   │                              cost), 𝔼 = q/(1−q) failures, 1/p trials
│   ├── Complexity/     proving what it costs
│   │   ├── TimeMT.lean            cost transformer over any monad
│   │   ├── MonadCost.lean         abstract `tick` (no-op by default)
│   │   ├── TimedSemantics.lean    clock erasure, `LawfulRandMonad (TimeMT ℕ M)`,
│   │   │                          `LawfulMonadCost` (ticks invisible to `toPMF`)
│   │   ├── ExpectedCost.lean      𝔼_runtime[e | M], cost_step, uniform-step
│   │   │                          lemmas, `costPMF` (the cost law itself)
│   │   ├── SamplerCosts.lean      the samplers are free (cost-tier facts
│   │   │                          about `Randomness/RandVec`'s samplers)
│   │   ├── Variance.lean          `variance`, Var = E[g²] − E[g]², Chebyshev
│   │   └── TailBounds.lean        ℙ_runtime[e > k | M]: Markov and Chebyshev
│   │                              tail bounds on the running time
│   ├── Correctness/    proving what comes out
│   │   ├── Correctness.lean       Dirac / distributional / support recipes,
│   │   │                          `toPMF_step`, `dirac_finish`, `@[spec_transport]`
│   │   └── Amplify.lean           `amplify best k m`: k independent runs, keep
│   │                              the best — ℙ[success] ≥ 1 − (1−p)^k
│   ├── SimpAttr.lean          the registered simp sets
│   └── Tactics.lean           PMF bridges, `pmf_simp_attr`, derived lemmas
├── Helpers/            shared mathematics (Mathlib-only)
│   ├── Partition.lean         pivot-partition lemmas, `pivotLT`/`pivotGE`,
│   │                          rank reindexing `nodup_partition_sum₂`
│   ├── MultiGraph.lean        executable multigraphs: cuts, contraction,
│   │                          degree/handshake — Karger's graph theory
│   ├── Counting.lean          involution pairing (½-soundness counts)
│   └── HarmonicSums.lean      prefix sums Σ H_r, Σ r·H_r, Σ (r+1)·H_r
└── Algorithms/
    ├── Tutorial.lean          ← start here
    ├── Quicksort/             Quickselect/       Karger/
    ├── ReservoirSampling/     Freivalds/         Treap/
    ├── FisherYates/           SchwartzZippel/    CouponCollector/
    │
    │   Each algorithm folder holds X.lean (the formal development)
    │   and X.md — the same algorithm in plain English and standard
    │   LaTeX mathematics. This is to compare the English ↔ Lean translation.
```

## Verified algorithms

Each case study exercises a different *tier* of randomized-algorithm
analysis; together they are the proof that the framework is usable.

| Algorithm | Correctness | Complexity |
|---|---|---|
| **Quicksort** | Dirac: always the sorted permutation | exact `2(n+1)H(n) − 4n`; $\leq$ `C(n,2)` for duplicates; Markov tail `ℙ[cost > k] ≤ C(n,2)/(k+1)` |
| **Quickselect** | Dirac: always the k-th order statistic | exact Knuth 1971 bivariate-harmonic formula; `≤ 4n`; $\leq$  `C(n,2)` for duplicates |
| **Karger** | returns an actual **minimum cut** with prob. `≥ 2/(n(n−1))` (`karger_finds_min`); one-sided error (support) | amplified: `k` runs fail with prob. `≤ (1−2/(n(n−1)))^k`; cost `≤ (n−2)·m` |
| **Reservoir sampling** | exact output distribution: `P[a] = count a / n` | exactly `n − 1` coins on every run (cost law), single pass |
| **Fisher–Yates** | exact output distribution: uniform over all `n!` permutations | free — a sampler, no ticks |
| **Schwartz–Zippel** | complete + sound (`≤ deg/\|S\|`, any integral domain) | one wholesale evaluation |
| **Coupon collector** | (cost-law case study) | exactly `n·H(n)` expected draws |
| **Freivalds** | complete + sound (`≤ 1/2`, any `CommRing`) | exactly `3n²` on every run (cost law), vs `n³` |
| **Treap** | every output a valid BST | **`E[height] ≤ 3·log₂(n+3) + 4`** via `E[2^H] ≤ C(n+3,3)` |

All proofs rely (after "#print axioms") only on `propext`,
`Classical.choice`, `Quot.sound`.

## Notation used throughout some algorithm

```lean
𝒟[Quicksort L | M]              -- output distribution at random monad M
𝔼_runtime[Quicksort L | M]      -- expected runtime (ℝ≥0∞) at random monad M
𝔼ℝ_runtime[Quicksort L | M]     -- the same, as a real number
ℙ_runtime[Quicksort L > k | M]  -- tail probability; ≤ 𝔼_runtime[…]/(k+1) by Markov
ℙ[Karger g = g.minCutValue | M] -- output probability (correctness twin of 𝔼_runtime)
ℙ[reservoir L ∈ S | M]          -- probability of an event
expVal (toPMF (treap L)) g      -- E[g(output)]
𝔼[couponCollector n]            -- mean of a ℕ-valued law (e.g. a cost law)
x ⊖ y                           -- |x − y| in ℝ≥0∞ (Chebyshev deviations)
pivotLT L i, pivotGE L i        -- the two sides of a pivot partition
```

## Building

```
lake build          # builds the whole framework (root manifest ARA.lean)
lake exe axiom_audit # checks the trusted base of every ARA declaration
```

The audit ([scripts/AxiomAudit.lean](scripts/AxiomAudit.lean)) reads the built
`.olean` files and fails if any declaration depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. CI runs it, plus a `sorry` grep, on every
push and pull request.

Toolchain: `leanprover/lean4 v4.31.0`, Mathlib `v4.31.0`,
[cslib](https://github.com/leanprover/cslib) `v4.31.0` (provides `TimeM`).
