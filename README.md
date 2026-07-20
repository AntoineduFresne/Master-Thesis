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

```lean
theorem randMax_correct ... :
    𝒟[RandMax L | M] = PMF.pure (listMax L) := by
  dirac_correct RandMax   -- ← the framework does everything except
                          --   the @[spec_transport] lemma (the math)
```

Design rationale (why shallow embedding, `PMF`/Giry monad, correctness
tiers, known limitations): see [`DESIGN.md`](DESIGN.md).

## Layout — three layers

```
ARA/
├── Infrastructure/
│   ├── Randomness/     the semantic layer: what a random program *means*
│   │   ├── LawfulRandMonad.lean   `RandMonad` (uniform `randFin`) + `toPMF`
│   │   │                          semantics, 𝒟[e | M], post-processing lemmas
│   │   ├── TimedSemantics.lean    clock erasure, `LawfulRandMonad (TimeMT ℕ M)`,
│   │   │                          `LawfulMonadCost` (ticks invisible to `toPMF`)
│   │   ├── RandVec.lean           0/1 and finite-grid entropy sources
│   │   │                          (`randBit`/`randVec`, `randElem`/`randVecOn`)
│   │   │                          with the counting principles #accepting / |grid|
│   │   └── Geometric.lean         the geometric law (retry cost), E = q/(1−q)
│   ├── Correctness/    proving what comes out
│   │   ├── Correctness.lean       Dirac / distributional / support recipes,
│   │   │                          `toPMF_step`, `dirac_finish`, `@[spec_transport]`
│   │   └── Amplify.lean           `amplify best k m`: k independent runs, keep
│   │                              the best — ℙ[success] ≥ 1 − (1−p)^k
│   ├── Complexity/     proving what it costs
│   │   ├── TimeMT.lean            cost transformer over any monad
│   │   ├── MonadCost.lean         abstract `tick` (no-op by default)
│   │   ├── ExpectedCost.lean      𝔼_runtime[e | M], cost_step, uniform-step
│   │   │                          lemmas, `expVal`, `costPMF` (the cost law)
│   │   ├── TailBounds.lean        the event algebra `prob`, ℙ[e = v | M],
│   │   │                          ℙ_runtime[e > k | M] + Markov's inequality
│   │   └── Variance.lean          `variance`, Var = E[g²] − E[g]², Chebyshev
│   ├── SimpAttr.lean          the registered simp sets
│   └── Tactics.lean           `pmf_simp`, PMF bridges, derived lemmas
├── Helpers/            shared mathematics
│   ├── Partition.lean         pivot-partition lemmas, `pivotLT`/`pivotGE`,
│   │                          rank reindexing `nodup_partition_sum₂`
│   └── HarmonicSums.lean      prefix sums Σ H_r, Σ r·H_r, Σ (r+1)·H_r
└── Algorithms/
    ├── Tutorial.lean          ← start here
    ├── Quicksort/             Quickselect/       Karger/
    ├── ReservoirSampling/     Freivalds/         Treap/
    ├── FisherYates/           SchwartzZippel/    CouponCollector/
    │
    │   Each algorithm folder holds X.lean (the formal development)
    │   and X.md — the same algorithm in plain English and standard
    │   LaTeX mathematics, with no reference to Lean: problem,
    │   algorithm, correctness and complexity proofs. The pair is the
    │   English ↔ Lean translation exhibit the framework is measured by.
```

## Verified algorithms

Each case study exercises a different *tier* of randomized-algorithm
analysis; together they are the proof that the framework is usable.

| Algorithm | Correctness | Complexity |
|---|---|---|
| **Quicksort** | Dirac: always the sorted permutation | exact `2(n+1)H(n) − 4n`; `C(n,2)` for duplicates |
| **Quickselect** | Dirac: always the k-th order statistic | exact Knuth 1971 bivariate-harmonic formula; `≤ 4n`; `C(n,2)` |
| **Karger** | one-sided error (support) | success probability `≥ 2/(n(n−1))`; amplified: `k` runs fail with prob. `≤ (1−2/(n(n−1)))^k`; cost `≤ (n−2)·m` |
| **Reservoir sampling** | exact output distribution: `P[a] = count a / n` | exactly `n − 1` coins, single pass |
| **Fisher–Yates** | exact output distribution: uniform over all `n!` permutations | free — a sampler, no ticks |
| **Schwartz–Zippel** | complete + sound (`≤ deg/\|S\|`, any integral domain) | one wholesale evaluation |
| **Coupon collector** | (cost-law case study) | exactly `n·H(n)` expected draws |
| **Freivalds** | complete + sound (`≤ 1/2`, any `CommRing`) | exactly `3n²` vs `n³` |
| **Treap** | every output a valid BST | **`E[height] ≤ 3·log₂(n+3) + 4`** via `E[2^H] ≤ C(n+3,3)` |

All proofs rely (after "#print axioms") only on `propext`,
`Classical.choice`, `Quot.sound`.

## Notation

```lean
𝒟[Quicksort L | M]              -- output distribution at random monad M
𝔼_runtime[Quicksort L | M]      -- expected runtime (ℝ≥0∞) at random monad M
𝔼ℝ_runtime[Quicksort L | M]     -- the same, as a real number
ℙ_runtime[Quicksort L > k | M]  -- tail probability; ≤ 𝔼_runtime[…]/(k+1) by Markov
expVal (toPMF (treap L)) g      -- E[g(output)]
pivotLT L i, pivotGE L i        -- the two sides of a pivot partition
```

## Building

```
lake build          # builds the whole framework (root manifest ARA.lean)
```

Toolchain: `leanprover/lean4 v4.31.0`, Mathlib `v4.31.0`,
[cslib](https://github.com/leanprover/cslib) `v4.31.0` (provides `TimeM`).
