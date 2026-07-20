/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Randomness.Prob

/-!
# The geometric distribution

The law of the number of **failures before the first success** of a
Bernoulli process with failure probability `q < 1`:
`P(k) = qᵏ(1 − q)`. It is the cost law of a retry-until-success loop —
the loop itself terminates only almost surely, so it is not a
structurally terminating program, but its cost distribution is a
perfectly well-defined `PMF` (total mass `1`). `CouponCollector` is
the first client; a sub-probability layer for the program-level loop
is future work.

Everything is proved directly in `ℝ≥0∞` (Mathlib's geometric
distribution is measure-theoretic and real-valued; the expectation
computation below — the layer-cake exchange — needs no summability
side conditions at all).

## Main declarations

* `geometric q hq` — the geometric law on `ℕ`
* `expVal_geometric` — `E = q/(1 − q)` failures, i.e. `1/(1 − q)`
  trials
-/

namespace ARA

open ENNReal

private lemma geometric_mass (q : ℝ≥0∞) (hq : q < 1) :
    HasSum (fun k : ℕ => q ^ k * (1 - q)) 1 := by
  have htsum : ∑' k : ℕ, q ^ k * (1 - q) = 1 := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ENNReal.inv_mul_cancel (tsub_pos_of_lt hq).ne'
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  convert ENNReal.summable.hasSum
  exact htsum.symm

/-- The geometric distribution: `k` failures before the first success,
`P(k) = qᵏ(1 − q)`, for failure probability `q < 1`. -/
noncomputable def geometric (q : ℝ≥0∞) (hq : q < 1) : PMF ℕ :=
  ⟨fun k => q ^ k * (1 - q), geometric_mass q hq⟩

@[simp] lemma geometric_apply (q : ℝ≥0∞) (hq : q < 1) (k : ℕ) :
    geometric q hq k = q ^ k * (1 - q) := rfl

/-- **Expectation of the geometric law**: `q/(1 − q)` expected
failures before the first success (hence `1/(1 − q)` expected trials).
Proved by the layer-cake exchange `k = #{j | j < k}`; in `ℝ≥0∞` the
double-sum swap is unconditional. -/
theorem expVal_geometric (q : ℝ≥0∞) (hq : q < 1) :
    expVal (geometric q hq) (fun k => (k : ℝ≥0∞)) = q * (1 - q)⁻¹ := by
  have h0 : (1 - q) ≠ 0 := (tsub_pos_of_lt hq).ne'
  have htop : (1 - q) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  -- `k` as a sum of indicators.
  have hk : ∀ k : ℕ, (k : ℝ≥0∞) = ∑' j : ℕ, if j < k then 1 else 0 := by
    intro k
    rw [tsum_eq_sum (s := Finset.range k) fun j hj =>
      if_neg fun h => hj (Finset.mem_range.mpr h)]
    rw [Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj)]
    simp
  unfold expVal
  calc ∑' k, geometric q hq k * (k : ℝ≥0∞)
      = ∑' k, ∑' j, if j < k then q ^ k * (1 - q) else 0 := by
        refine tsum_congr fun k => ?_
        rw [hk k, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun j => by
          rw [mul_ite, mul_one, mul_zero, geometric_apply]
    _ = ∑' j, ∑' k, if j < k then q ^ k * (1 - q) else 0 := ENNReal.tsum_comm
    _ = ∑' j : ℕ, ∑' i : ℕ, q ^ (i + (j + 1)) * (1 - q) := by
        refine tsum_congr fun j => ?_
        have hsplit := Summable.sum_add_tsum_nat_add'
          (f := fun k => if j < k then q ^ k * (1 - q) else 0) (k := j + 1)
          ENNReal.summable
        rw [← hsplit,
          Finset.sum_eq_zero fun i hi =>
            if_neg (by have := Finset.mem_range.mp hi; omega),
          zero_add]
        exact tsum_congr fun i => if_pos (by omega)
    _ = ∑' j : ℕ, q ^ (j + 1) := by
        refine tsum_congr fun j => ?_
        rw [tsum_congr fun i => show q ^ (i + (j + 1)) * (1 - q) =
              q ^ (j + 1) * (q ^ i * (1 - q)) from by rw [pow_add]; ring,
          ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          ENNReal.tsum_geometric, ENNReal.inv_mul_cancel h0 htop, mul_one]
    _ = q * (1 - q)⁻¹ := ENNReal.tsum_geometric_add_one q

end ARA
