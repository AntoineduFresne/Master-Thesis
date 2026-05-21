# Master Thesis — ARA: Analysis of Randomized Algorithms

A Lean 4 framework for analyzing randomized algorithms. Author:
Antoine du Fresne von Hohenesche (ETHZ).

## Primary objective

Design a foundational framework in Lean 4 where a randomized algorithm is
written **once** and re-used for all the things one wants to do with it:

* run it (in `IO`, with real randomness),
* reason about its output distribution (in `PMF`),
* reason about its cost distribution (in `TimeMT ℕ PMF`),
* benchmark it (in `TimeMT ℕ IO`).

The ultimate goal is to make Lean 4 proofs of complexity and probability
bounds read about as concisely as a LaTeX proof.

## Framework architecture

```
TimeM.lean                          deterministic cost monad +
                                    TimeMT cost-transformer
        ↑
ARA/MonadCost.lean                  `MonadCost C M`: abstract cost ticks
                                    (no-op default, accumulating on TimeMT)
        ↑
ARA/LawfulRandMonad.lean            `RandMonad`, `LawfulRandMonad`:
                                    abstract uniform-randomness primitive
                                    with `toPMF` semantics
        ↑
ARA/Tactics.lean                    `pmf_simp_attr`, `pmf_simp`, `pmf_norm`
                                    (concrete probability computation)
        ↑
ARA/ExpectedCost.lean               `expected_cost`, `runtime`, `runtime_ℝ`,
                                    notation `𝔼_runtime[·]`, `𝔼ℝ_runtime[·]`,
                                    `expected_cost_simp` attribute and
                                    `cost_step` / `runtime_simp` tactics
        ↑
ARA/QuickSort.lean                  demo algorithm + correctness proof +
                                    expected complexity proof for `Nodup`
                                    lists and an upper-bound theorem for
                                    arbitrary lists
```

## Key contributions

1. **Single-source algorithms.** One `def QuickSort` is polymorphic in
   `[Monad M] [RandMonad M] [MonadCost ℕ M]` and instantiates to:
   * `IO`              — executable, real randomness, no cost tracking
   * `PMF`             — output distribution, noncomputable spec
   * `TimeMT ℕ IO`     — executable + cost tracking
   * `TimeMT ℕ PMF`    — joint distribution over outputs and costs
2. **Cost tracking via monad transformer.** `TimeMT T M` is a writer-style
   transformer that threads a cost through any base monad. The
   `MonadCost` typeclass keeps the algorithm code agnostic to whether
   the running monad actually accumulates cost.
3. **Cost automation.** The `expected_cost_simp` simp set tags the bridge
   lemmas (`expected_cost_toPMF_tick_bind`, `…_pure_bind`, `…_lift_bind`,
   `expected_cost_toPMF_pure`, etc.) so `cost_step` mechanically peels
   `TimeMT` combinators off an expected-cost expression.
4. **Closed-form QuickSort complexity.** For `L : List ℕ` with
   `L.Nodup`, the expected number of comparisons is exactly
   `2(n+1)H(n) − 4n`. For arbitrary lists, the expected cost is bounded
   by `(n choose 2)` (statement only; proof TODO).

## Usage

```lean
import ARA.QuickSort

open ARA Cslib.Algorithms.Lean

-- Correctness for any LawfulRandMonad, free for the PMF instance:
#check Correctness_Quicksort

-- Exact expected complexity for Nodup lists:
example {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    𝔼ℝ_runtime[(QuickSort L : TimeMT ℕ M _)] =
      expected_qs_cost L.length :=
  Expected_Complexity_Quicksort L hnd
```

## File map

* `ARA.lean` — top-level imports (Mathlib).
* `TimeM.lean` — `TimeM` / `TimeMT` (cslib-shaped, predates this work).
* `ARA/SimpAttr.lean` — registers `pmf_simp_attr` and `expected_cost_simp`.
* `ARA/Tactics.lean` — `pmf_simp` / `pmf_norm` for PMF computations.
* `ARA/MonadCost.lean` — `MonadCost C M` typeclass + default instances.
* `ARA/LawfulRandMonad.lean` — `RandMonad` / `LawfulRandMonad` typeclasses.
* `ARA/ExpectedCost.lean` — expected-cost analysis + `cost_step` tactic.
* `ARA/QuickSort.lean` — demo algorithm + theorems.
* `archive/` — earlier exploratory material kept for reference (not built).

## Toolchain

Built with `leanprover/lean4 v4.27.0` against Mathlib `v4.27.0`.
Intended target for upstreaming: [cslib](https://github.com/leanprover/cslib).
