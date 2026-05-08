import ARA.Basic

/-!
# Expected cost

This file contains:
1. The `TimedResult` type and `expected_cost` definition
2. Linearity of expectation lemmas
-/

namespace ARA

/-- A result paired with a time cost. Isomorphic to `TimeM ℕ α` from TimeM.lean. -/
@[ext] structure TimedResult (α : Type) where
  val : α
  cost : ℕ

open ENNReal

/-- Expected time cost of a computation described by a PMF over timed outcomes.
Using `ENNReal` avoids all summability concerns. -/
noncomputable def expected_cost {α : Type} (p : PMF (TimedResult α)) : ENNReal :=
  ∑' (res : TimedResult α), p res * (res.cost : ENNReal)

@[simp] lemma expected_cost_pure_zero {α : Type} (a : α) :
    expected_cost (PMF.pure ⟨a, 0⟩) = 0 := by
  unfold expected_cost; aesop

@[simp] lemma expected_cost_pure_val {α : Type} (a : α) (t : ℕ) :
    expected_cost (PMF.pure ⟨a, t⟩) = (t : ENNReal) := by
  simp [expected_cost]

/-- Linearity of expected cost through a PMF bind. -/
lemma expected_cost_bind {A : Type} {β : Type} (d : PMF A) (f : A → PMF (TimedResult β)) :
    expected_cost (d >>= f) = ∑' a, d a * expected_cost (f a) := by
  unfold expected_cost
  have h_bind : ∀ res : TimedResult β, (d >>= f) res = ∑' a : A, d a * (f a) res := by aesop
  simp +decide only [h_bind, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_comm]
  simp +decide only [← mul_assoc, ENNReal.tsum_mul_right]

/-- Expected cost under uniform pivot selection. -/
lemma expected_cost_uniform_bind {n : ℕ} [NeZero n] {β : Type}
    (f : Fin n → PMF (TimedResult β)) :
    expected_cost (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, expected_cost (f i) := by
  rw [expected_cost_bind]
  simp +decide [Finset.mul_sum _ _ _, PMF.uniformOfFintype_apply, mul_comm]

end ARA
