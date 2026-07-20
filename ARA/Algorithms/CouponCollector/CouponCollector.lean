/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Randomness.Geometric
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The coupon collector

`n` coupon types, uniform independent draws: collecting every type
takes `n·H(n)` draws in expectation — the classical harmonic-number
bound, exactly.

## Modelling

"Draw until a new type appears" is a retry loop that terminates only
*almost surely*, so it is not a structurally terminating program —
the program-level loop is exactly the Las-Vegas construct that awaits
a sub-probability layer. Its **cost law**, however, is a perfectly
well-defined distribution: stage `m` (with `m` types still missing)
is a `geometric` number of draws with success probability `m/n`, and
the stages compose by `bind`. `couponCollector n` *is* that law — the
first case study of the cost-distribution tier (`costPMF`-shaped: a
`PMF ℕ` of running times with no output attached).

## Main results

* `couponCollector_expected` — `E[draws] = Σ_{r<n} n/(r+1)`, exactly,
  in `ℝ≥0∞`.
* `couponCollector_expected_real` — the classical form
  `E[draws] = n·H(n)` in `ℝ`.
-/

namespace ARA

open ENNReal

/-! ## The cost law -/

/-- Stage decomposition: with `missing` types still missing out of
`n`, one geometric stage (success probability `missing/n`, counted as
`k + 1` draws), then the rest. -/
noncomputable def couponCollectorAux (n : ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | m + 1 =>
      (geometric (1 - ((m + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) (by
        refine ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_
        simp [ENNReal.div_eq_zero_iff])).bind fun k =>
        (couponCollectorAux n m).bind fun rest => PMF.pure (k + 1 + rest)

/-- The coupon-collector cost law: total draws to collect all `n`
types. -/
noncomputable def couponCollector (n : ℕ) : PMF ℕ := couponCollectorAux n n

/-! ## Expected number of draws -/

private lemma expVal_couponCollectorAux (n : ℕ) :
    ∀ m : ℕ, m ≤ n →
      expVal (couponCollectorAux n m) (fun k => (k : ℝ≥0∞)) =
        ∑ r ∈ Finset.range m, (n : ℝ≥0∞) / ((r : ℝ≥0∞) + 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [couponCollectorAux]
    simp
  | succ m ih =>
    intro hmn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      have h : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hmn
      exact_mod_cast h.ne'
    rw [couponCollectorAux, expVal_bind]
    simp only [expVal_bind, expVal_pure]
    set p : ℝ≥0∞ := ((m + 1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) with hp
    have hp0 : p ≠ 0 := by
      rw [hp]
      simp [ENNReal.div_eq_zero_iff]
    have hptop : p ≠ ⊤ := by
      rw [hp]
      simp [ENNReal.div_eq_top, hn0]
    have hp1 : p ≤ 1 := by
      rw [hp, ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top n), one_mul]
      exact_mod_cast hmn
    have hsub : 1 - (1 - p) = p :=
      ENNReal.sub_sub_cancel ENNReal.one_ne_top hp1
    have hstage : (1 - p) * p⁻¹ + 1 = p⁻¹ := by
      have h1 : (1 - p) * p⁻¹ + 1 = (1 - p) * p⁻¹ + p * p⁻¹ := by
        rw [ENNReal.mul_inv_cancel hp0 hptop]
      rw [h1, ← add_mul, tsub_add_cancel_of_le hp1, one_mul]
    have hpinv : p⁻¹ = (n : ℝ≥0∞) / ((m : ℝ≥0∞) + 1) := by
      rw [hp, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
          (Or.inl (ENNReal.natCast_ne_top _)),
        inv_inv, mul_comm, ← div_eq_mul_inv]
      push_cast
      rfl
    have hinner : ∀ k : ℕ, expVal (couponCollectorAux n m)
        (fun rest => ((k + 1 + rest : ℕ) : ℝ≥0∞)) =
        (k : ℝ≥0∞) + (1 + ∑ r ∈ Finset.range m, (n : ℝ≥0∞) / ((r : ℝ≥0∞) + 1)) := by
      intro k
      rw [show (fun rest : ℕ => ((k + 1 + rest : ℕ) : ℝ≥0∞)) =
          (fun rest : ℕ => ((k : ℝ≥0∞) + 1) + (rest : ℝ≥0∞)) from
        funext fun rest => by push_cast; ring,
        expVal_add, expVal_const, ih (Nat.le_of_succ_le hmn), add_assoc]
    simp only [hinner]
    rw [expVal_add, expVal_const, expVal_geometric, hsub,
      Finset.sum_range_succ, ← add_assoc, hstage, hpinv]
    exact add_comm _ _

/-- **The coupon collector, exactly** (in `ℝ≥0∞`): collecting all `n`
types takes `Σ_{r<n} n/(r+1)` draws in expectation. -/
theorem couponCollector_expected (n : ℕ) :
    expVal (couponCollector n) (fun k => (k : ℝ≥0∞)) =
      ∑ r ∈ Finset.range n, (n : ℝ≥0∞) / ((r : ℝ≥0∞) + 1) :=
  expVal_couponCollectorAux n n le_rfl

/-- **The coupon collector, classically**: `n·H(n)` expected draws. -/
theorem couponCollector_expected_real (n : ℕ) :
    (expVal (couponCollector n) (fun k => (k : ℝ≥0∞))).toReal =
      ((n * harmonic n : ℚ) : ℝ) := by
  rw [couponCollector_expected,
    ENNReal.toReal_sum fun r _ => by simp [ENNReal.div_eq_top]]
  have hterm : ∀ r : ℕ, ((n : ℝ≥0∞) / ((r : ℝ≥0∞) + 1)).toReal =
      (n : ℝ) / ((r : ℝ) + 1) := by
    intro r
    rw [ENNReal.toReal_div,
      ENNReal.toReal_add (ENNReal.natCast_ne_top r) ENNReal.one_ne_top]
    simp
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  push_cast [harmonic]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

end ARA
