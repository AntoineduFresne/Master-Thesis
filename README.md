# ARA — Analysis of Randomized Algorithms in Lean 4

A framework where a randomized algorithm is written **once** and that single
definition serves as:

* an **executable program** (`IO`, real randomness — `#eval` it),
* a **distribution** (`PMF`, the mathematical specification),
* a **timed algorithm** (`TimeMT ℕ M`, cost accumulated per `tick`),
* a **benchmark** (`TimeMT ℕ IO`, executable with a clock).

Correctness and expected-complexity proofs then follow a fixed recipe in
which everything except the *mathematics of the algorithm itself* is
automated by the framework.

Author: Antoine du Fresne von Hohenesche (ETHZ, master's thesis).

## Start here

**[`ARA/Algorithms/Tutorial.lean`](ARA/Algorithms/Tutorial.lean)** is a
copy-me template: a toy algorithm (`RandMax`) verified end-to-end in six
numbered steps. The inductive case of its correctness proof is one tactic
(`dirac_finish`), and its exact expected cost follows the uniform-pivot
recipe in a dozen lines.

```lean
theorem Correctness_RandMax ... := by
  induction L using RandMax.induct with
  | case1 => rw [RandMax.eq_1]; simp only [LawfulRandMonad.toPMF_pure]; rfl
  | case2 head tail ih =>
    rw [randMax_eq_bind]
    refine toPMF_randIdx_bind_dirac fun i => ?_
    unfold randMax_branch
    dirac_finish        -- ← the framework does the rest
```

## Layout — three layers

```
ARA/
├── Infrastructure/     the engine (a user never edits this)
│   ├── TimeMT.lean            cost transformer over any monad
│   ├── MonadCost.lean         abstract `tick` (no-op by default)
│   ├── LawfulRandMonad.lean   `RandMonad` (uniform `randFin`) + `toPMF` semantics
│   ├── ExpectedCost.lean      𝔼_runtime[e | M], cost_step, uniform-step lemmas,
│   │                          `expVal` (expectations of output functionals)
│   ├── Correctness.lean       Dirac / distributional / support correctness recipes,
│   │                          `dirac_step`, `dirac_finish`, `@[spec_transport]`
│   ├── SimpAttr.lean          the registered simp sets
│   └── Tactics.lean           `pmf_simp`, PMF bridges, derived lemmas
├── Helpers/            shared mathematics
│   └── Partition.lean         pivot-partition lemmas, `pivotLT`/`pivotGE`,
│                              rank reindexing `nodup_partition_sum₂`
└── Algorithms/         the case studies (and the Tutorial)
    ├── Tutorial.lean          ← start here
    ├── Quicksort.lean         Quickselect.lean   Karger.lean
    ├── ReservoirSampling.lean Freivalds.lean     Treap.lean
```

## Verified algorithms

Each case study exercises a different *tier* of randomized-algorithm
analysis; together they are the proof that the framework is usable.

| Algorithm | Correctness | Complexity |
|---|---|---|
| **Quicksort** | Dirac: always the sorted permutation | exact `2(n+1)H(n) − 4n`; `C(n,2)` for duplicates |
| **Quickselect** | Dirac: always the k-th order statistic | exact Knuth 1971 bivariate-harmonic formula; `≤ 4n`; `C(n,2)` |
| **Karger** | one-sided error (support) | success probability `≥ 2/(n(n−1))`; cost `≤ (n−2)·m` |
| **Reservoir sampling** | exact output distribution: `P[a] = count a / n` | exactly `n − 1` coins, single pass |
| **Freivalds** | complete + sound (`≤ 1/2`, any `CommRing`) | exactly `3n²` vs `n³` |
| **Treap** | every output a valid BST | **`E[height] ≤ 3·log₂(n+3) + 4`** via `E[2^H] ≤ C(n+3,3)` |

All proofs are `sorry`-free; the axiom audit shows only `propext`,
`Classical.choice`, `Quot.sound`.

## The recipe (what a new algorithm costs you)

1. **Define it once**, polymorphic over
   `{M} [Monad M] [RandMonad M] [MonadCost ℕ M]`; draw randomness with
   `randIdx`/`randFin`, charge cost with `MonadCost.tick`.
2. **Instances for free** — four one-liners (`IO`, `PMF`, timed ×2).
3. **Decompose** — one branch `abbrev` + two one-line `_eq_bind` lemmas.
4. **The mathematics** — spec-transport lemmas, tagged `@[spec_transport]`.
   *This is the only part that is genuinely about your algorithm.*
5. **Correctness** — `induction … using f.induct`, collapse with
   `toPMF_randIdx_bind_dirac`, close with `dirac_finish`. (Monte-Carlo:
   `support_toPMF_randIdx_bind` / `le_toPMF_randIdx_bind` instead.)
6. **Cost** — branch cost by `cost_step`; the recurrence
   `E = (1/n)·Σᵢ E[branchᵢ]` by `expected_cost_uniform_step`; upper bounds
   stay in `ℝ≥0∞`, exact formulas descend to `ℝ` via `toReal_uniform_avg`.
   Structural output measures (tree height, …) use `expVal`.

## Notation

```lean
𝔼_runtime[Quicksort L | M]      -- expected runtime (ℝ≥0∞) at random monad M
𝔼ℝ_runtime[Quicksort L | M]     -- the same, as a real number
expVal (toPMF (treap L)) g      -- E[g(output)] for structural measures
pivotLT L i, pivotGE L i        -- the two sides of a pivot partition
```

## Building

```
lake build          # builds the whole framework (root manifest ARA.lean)
```

Toolchain: `leanprover/lean4 v4.31.0`, Mathlib `v4.31.0`,
[cslib](https://github.com/leanprover/cslib) `v4.31.0` (provides `TimeM`).
Intended upstreaming target: cslib.
