/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.ExpectedCost

/-!
# Random 0/1 vectors

The generic `0/1` entropy source for Monte-Carlo algorithms: a uniform
random bit (`randBit`), a uniform random bit vector (`randVec`), and
the counting principle `toPMF_randVec_true` — testing **any** predicate
on a random `0/1` vector accepts with probability
`#{accepting bit choices} / 2^n`. This is the shape every
hashing/fingerprinting-style analysis needs; `Freivalds` is the first
client.

Only `Zero R` and `One R` are assumed — the vector entries just need
the two labels. Neither sampler ticks (`expected_cost_randVec`).
-/

namespace ARA

open Cslib.Algorithms.Lean

variable {R : Type} [Zero R] [One R] {n : ℕ}

/-- Sample a single uniform `0/1` entry of `R`. -/
def randBit {M} [Monad M] [RandMonad M] : M R := do
  let b ← RandMonad.randFin 2
  return if b = 0 then 0 else 1

/-- Sample a uniformly random `0/1` vector `r : Fin n → R`. -/
def randVec {M} [Monad M] [RandMonad M] : (n : ℕ) → M (Fin n → R)
  | 0 => return fun i => i.elim0
  | n + 1 => do
      let b ← (randBit : M R)
      let rest ← randVec n
      return Fin.cons b rest

/-- Interpret a bit choice as a `0/1` vector of `R`. -/
def bitVec (v : Fin n → Fin 2) : Fin n → R :=
  fun i => if v i = 0 then 0 else 1

lemma bitVec_cons (i : Fin 2) (v : Fin n → Fin 2) :
    (bitVec (Fin.cons i v) : Fin (n + 1) → R) =
      Fin.cons (if i = 0 then (0 : R) else 1) (bitVec v) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [bitVec, Fin.cons_zero]
  · simp [bitVec, Fin.cons_succ]

/-- **Acceptance probability as a count.** Testing any predicate on a
random `0/1` vector accepts with probability
`#{accepting bit choices} / 2^n`. -/
lemma toPMF_randVec_true
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (n : ℕ) (p : (Fin n → R) → Bool),
    inst.toPMF ((randVec n : M (Fin n → R)) >>= fun r => pure (p r)) true =
      (∑ v : Fin n → Fin 2, if p (bitVec v) then (1 : ENNReal) else 0) /
        2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro p
    haveI : Subsingleton (Fin 0 → R) := ⟨fun a b => funext fun i => i.elim0⟩
    rw [randVec, pure_bind, inst.toPMF_pure, pmf_pure_eq, PMF.pure_apply,
      Fintype.sum_eq_single (fun i : Fin 0 => i.elim0)
        (fun b hb => absurd (Subsingleton.elim b _) hb),
      pow_zero, div_one,
      show (bitVec (fun i : Fin 0 => i.elim0) : Fin 0 → R) = fun i => i.elim0 from
        Subsingleton.elim _ _]
    split_ifs with ha hb <;> simp_all
  | succ n ih =>
    intro p
    rw [randVec, randBit]
    simp only [bind_assoc, pure_bind]
    rw [inst.toPMF_bind, inst.toPMF_randFin, pmf_bind_eq, PMF.bind_apply,
      tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum]
    simp only [ih]
    -- Reindex the `2^(n+1)` bit choices by first bit × rest.
    rw [show (∑ w : Fin (n + 1) → Fin 2,
          if p (bitVec w) then (1 : ENNReal) else 0) =
        ∑ i : Fin 2, ∑ v : Fin n → Fin 2,
          if p (Fin.cons (if i = 0 then (0 : R) else 1) (bitVec v)) then
            (1 : ENNReal) else 0 from by
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ => Fin 2)
        (fun w => if p (bitVec w) then (1 : ENNReal) else 0),
        Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => by
        rw [show (Fin.consEquiv fun _ => Fin 2) (i, v) = Fin.cons i v from rfl,
          bitVec_cons]]
    -- `2⁻¹ · Σᵢ (Tᵢ / 2ⁿ) = (Σᵢ Tᵢ) / 2^(n+1)`.
    have h2 : ((2 : ENNReal) ^ (n + 1))⁻¹ = (2 ^ n)⁻¹ * 2⁻¹ := by
      rw [pow_succ, ENNReal.mul_inv (Or.inl (by positivity))
        (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
    simp only [ENNReal.div_eq_inv_mul]
    rw [← Finset.mul_sum, h2]
    ring

/-! ## Costs: the samplers are free -/

/-- `randBit` performs no ticks. -/
lemma expected_cost_randBit
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_runtime[(randBit : TimeMT ℕ M R)] = 0 := by
  unfold randBit
  cost_step

/-- `randVec` performs no ticks. -/
lemma expected_cost_randVec
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ n : ℕ,
    𝔼_runtime[(randVec n : TimeMT ℕ M (Fin n → R))] = 0 := by
  intro n
  induction n with
  | zero =>
    rw [randVec, expected_cost_toPMF_pure]
  | succ n ih =>
    rw [show (randVec (n + 1) : TimeMT ℕ M (Fin (n + 1) → R)) =
      (randBit : TimeMT ℕ M R) >>= fun b =>
        (randVec n : TimeMT ℕ M (Fin n → R)) >>= fun rest =>
          pure (Fin.cons b rest) from rfl]
    unfold TimedPMF
    rw [expected_cost_toPMF_bind]
    have h2 : ∀ b : R, expected_cost (inst.toPMF
        (((randVec n : TimeMT ℕ M (Fin n → R)) >>= fun rest =>
          (pure (Fin.cons b rest) : TimeMT ℕ M (Fin (n + 1) → R))).run)) = 0 :=
        fun b => by
      rw [expected_cost_toPMF_bind_pure]
      exact ih
    simp only [expected_cost_randBit, h2, mul_zero, tsum_zero, add_zero]

end ARA
