/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Randomness.RandVec
import ARA.Infrastructure.Complexity.SamplerCosts
import ARA.Infrastructure.Correctness.Correctness
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Schwartz–Zippel polynomial identity testing

Test whether a multivariate polynomial is identically zero by
evaluating it at a **uniformly random point of a grid** `Sⁿ`: always
accept the zero polynomial, and accept a nonzero one with probability
at most `totalDegree / #S` — the canonical Monte-Carlo algorithm of
algebraic complexity, and the natural successor of `Freivalds`
(matrix-product verification is the bilinear special case
`xᵀ(AB − C)y` on the grid `{0,1}ⁿ`).

## Architecture

The sampler is `randVecOn S n` from `ARA.Infrastructure.Randomness.RandVec`
(uniform on the grid; `toPMF_randVecOn_true` turns any acceptance
probability into a grid count). The mathematical core — the
Schwartz–Zippel counting bound — comes from Mathlib
(`MvPolynomial.schwartz_zippel_totalDegree`, stated in `ℚ≥0`); the
bridge to the framework's `ℝ≥0∞` probabilities is a single
cross-multiplication (`ennreal_div_le_div_nat`).

## Main results

* `schwartzZippel_complete` — the zero polynomial is always accepted.
* `schwartzZippel_sound` — a nonzero `P` is accepted with probability
  at most `P.totalDegree / #S`, over any integral domain.
* `schwartzZippel_cost_exact` — exactly one (wholesale-ticked)
  polynomial evaluation per run, and `schwartzZippel_costPMF` — the
  cost *law* is the point mass at `1`: deterministic, not just in
  expectation.
-/

namespace ARA

open Cslib.Algorithms.Lean
open scoped ENNReal

variable {R : Type} [CommRing R] [DecidableEq R] {n : ℕ}

/-! ## Algorithm -/

/-- Polynomial identity tester: evaluate at a uniformly random point
of the grid `Sⁿ` and accept iff the value is `0` (one wholesale tick
for the evaluation). -/
noncomputable def schwartzZippel {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (P : MvPolynomial (Fin n) R) (S : Finset R) (hS : S.Nonempty) :
    M Bool := do
  MonadCost.tick 1
  let r ← randVecOn S hS n
  pure (decide (MvPolynomial.eval r P = 0))

-- PMF specification instance (the sampler enumerates an abstract
-- `Finset`, so the algorithm is noncomputable — no `IO` demo).
noncomputable example (P : MvPolynomial (Fin 3) ℤ) :
    PMF Bool := schwartzZippel P {0, 1, 2} (by simp)

/-! ## Correctness -/

/-- **Completeness.** The zero polynomial is always accepted. -/
theorem schwartzZippel_complete
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (S : Finset R) (hS : S.Nonempty) :
    ℙ[schwartzZippel (0 : MvPolynomial (Fin n) R) S hS = true | M] = 1 := by
  rw [schwartzZippel, toPMF_tick_bind, toPMF_randVecOn_true]
  rw [show ((Fintype.piFinset fun _ : Fin n => S).filter
      fun f => decide (MvPolynomial.eval f (0 : MvPolynomial (Fin n) R) = 0)) =
      Fintype.piFinset fun _ : Fin n => S from
    Finset.filter_true_of_mem fun f _ => by simp]
  rw [Fintype.card_piFinset_const, Nat.cast_pow]
  exact ENNReal.div_self (pow_ne_zero n (by exact_mod_cast hS.card_pos.ne'))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- **Soundness (Schwartz–Zippel).** Over an integral domain, a
*nonzero* polynomial is accepted with probability at most
`totalDegree / #S`: one-sided error, tunable via the size of the
evaluation set. -/
theorem schwartzZippel_sound [IsDomain R]
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    {P : MvPolynomial (Fin n) R} (hP : P ≠ 0) (S : Finset R)
    (hS : S.Nonempty) :
    ℙ[schwartzZippel P S hS = true | M] ≤
      (P.totalDegree : ℝ≥0∞) / (S.card : ℝ≥0∞) := by
  rw [schwartzZippel, toPMF_tick_bind, toPMF_randVecOn_true]
  -- Align the accepting count with Mathlib's Schwartz–Zippel form.
  rw [show ((Fintype.piFinset fun _ : Fin n => S).filter
      fun f => decide (MvPolynomial.eval f P = 0)) =
      (Fintype.piFinset fun _ : Fin n => S).filter
        fun f => MvPolynomial.eval f P = 0 from
    Finset.filter_congr fun f _ => by simp]
  -- Mathlib's `ℚ≥0` bound crosses to `ℝ≥0∞` in one bridge call.
  have h := ennreal_div_le_div_of_nnrat (pow_pos hS.card_pos n) hS.card_pos
    (by exact_mod_cast MvPolynomial.schwartz_zippel_totalDegree hP S)
  rw [Nat.cast_pow] at h
  exact h

/-! ## Complexity -/

/-- **Exact cost.** One wholesale-ticked polynomial evaluation per
run (the sampler is free). -/
theorem schwartzZippel_cost_exact
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (P : MvPolynomial (Fin n) R) (S : Finset R) (hS : S.Nonempty) :
    𝔼_runtime[schwartzZippel P S hS | M] = 1 := by
  rw [schwartzZippel]
  cost_step

/-- **Deterministic cost.** The cost law is a point mass: *every* run
costs exactly one evaluation, not merely one on average. -/
theorem schwartzZippel_costPMF
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (P : MvPolynomial (Fin n) R) (S : Finset R) (hS : S.Nonempty) :
    costPMF (schwartzZippel P S hS : TimeMT ℕ M Bool) = PMF.pure 1 := by
  rw [schwartzZippel, MonadCost.tick_timeMT, costPMF_tick_bind,
    costPMF_eq_pure_zero (by rw [expected_cost_toPMF_bind_pure]; exact expected_cost_randVecOn ..),
    PMF.pure_map]

/-! ## Named corollaries at `M = PMF` -/

/-- Completeness at `M = PMF`. -/
theorem schwartzZippel_complete_pmf (S : Finset R) (hS : S.Nonempty) :
    (schwartzZippel (0 : MvPolynomial (Fin n) R) S hS : PMF Bool) true = 1 :=
  schwartzZippel_complete (M := PMF) S hS

/-- Soundness at `M = PMF`. -/
theorem schwartzZippel_sound_pmf [IsDomain R]
    {P : MvPolynomial (Fin n) R} (hP : P ≠ 0) (S : Finset R)
    (hS : S.Nonempty) :
    (schwartzZippel P S hS : PMF Bool) true ≤
      (P.totalDegree : ℝ≥0∞) / (S.card : ℝ≥0∞) :=
  schwartzZippel_sound (M := PMF) hP S hS

end ARA
