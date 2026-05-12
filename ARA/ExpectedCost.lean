import ARA.Basic
import TimeM
import ARA.LawfulRandMonad
import ARA.MonadCost

/-!
# Expected Cost

This module defines the expected cost of a randomized computation
described by a `PMF` over `TimeM ℕ α` outcomes, and provides the
bridge lemmas that connect operational `TimeMT` code to
combinatorial cost analysis.

## Design

The expected cost is defined directly over `PMF (TimeM ℕ α)`,
using the `.time` field of `TimeM`. This avoids any intermediate
types or isomorphisms — `TimeM ℕ α` is the single canonical
representation of a timed result.

## Main declarations

* `expected_cost` — expected time cost of a `PMF (TimeM ℕ α)`
* Linearity lemmas for `expected_cost` through `bind` and uniform
  distributions
* Bridge lemmas connecting `TimeMT` combinators (`tick`, `lift`,
  `pure`, `bind`) composed with `LawfulRandMonad.toPMF` to
  `expected_cost` arithmetic
* `TimeMT` erasure lemmas for correctness-from-timed proofs
-/

namespace ARA

open Cslib.Algorithms.Lean
open ENNReal

/-!
## Core definition
-/

/-- Expected time cost of a computation described by a PMF over
`TimeM ℕ α` outcomes. Using `ENNReal` avoids all summability
concerns. -/
noncomputable def expected_cost {α : Type} (p : PMF (TimeM ℕ α)) : ENNReal :=
  ∑' (res : TimeM ℕ α), p res * (res.time : ENNReal)

/-!
## Basic lemmas
-/

@[simp] lemma expected_cost_pure_zero {α : Type} (a : α) :
    expected_cost (PMF.pure ⟨a, 0⟩) = 0 := by
  unfold expected_cost; aesop

@[simp] lemma expected_cost_pure_val {α : Type} (a : α) (t : ℕ) :
    expected_cost (PMF.pure ⟨a, t⟩ : PMF (TimeM ℕ α)) = (t : ENNReal) := by
  simp [expected_cost]

/-!
## Linearity
-/

/-- Linearity of expected cost through a PMF bind. -/
lemma expected_cost_bind {A : Type} {β : Type} (d : PMF A) (f : A → PMF (TimeM ℕ β)) :
    expected_cost (d >>= f) = ∑' a, d a * expected_cost (f a) := by
  unfold expected_cost
  have h_bind : ∀ res : TimeM ℕ β, (d >>= f) res = ∑' a : A, d a * (f a) res := by aesop
  simp +decide only [h_bind, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_comm]
  simp +decide only [← mul_assoc, ENNReal.tsum_mul_right]

/-- Expected cost under uniform pivot selection. -/
lemma expected_cost_uniform_bind {n : ℕ} [NeZero n] {β : Type}
    (f : Fin n → PMF (TimeM ℕ β)) :
    expected_cost (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, expected_cost (f i) := by
  rw [expected_cost_bind]
  simp +decide [Finset.mul_sum _ _ _, PMF.uniformOfFintype_apply, mul_comm]

/-!
## Bridge lemmas: `toPMF`-composed helpers

These lemmas decompose `expected_cost (toPMF (… : TimeMT).run)`
through the various `TimeMT` combinators.
-/

/-- The marginal return distribution of `(TimeMT.lift m).run`
is just `toPMF m`. -/
lemma toPMF_map_ret_lift
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (m : M α) :
    inst.toPMF
      (TimeM.ret <$> (TimeMT.lift m : TimeMT ℕ M α).run) =
      inst.toPMF m := by
  rw [TimeMT.run_lift, ← Functor.map_map]; simp

/-
`expected_cost` of a `TimeMT.lift` is `0` (no ticks).
-/
lemma expected_cost_lift
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (m : M α) :
    expected_cost
      (inst.toPMF (TimeMT.lift m : TimeMT ℕ M α).run) =
      0 := by
  rw [expected_cost]
  have h_zero : ∀ res : TimeM ℕ α,
      (inst.toPMF (TimeMT.lift m).run) res * (res.time : ENNReal) = 0 := by
    intro res
    by_cases h : res.time = 0 <;> simp_all +decide [TimeMT.lift]
    rw [inst.toPMF_map]; erw [PMF.map_apply]; aesop
  aesop

/-- `expected_cost` of `TimeMT.tick t` is `t`. -/
lemma expected_cost_tick
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (t : ℕ) :
    expected_cost
      (inst.toPMF (TimeMT.tick t : TimeMT ℕ M Unit).run) =
      (t : ENNReal) := by
  convert expected_cost_pure_val () t
  exact inst.toPMF_pure _

/-
Shifting all time values by a constant `c` shifts the
expected cost by `c`.
-/
lemma expected_cost_shift
    {β : Type} (p : PMF (TimeM ℕ β)) (c : ℕ) :
    expected_cost
      (p >>= fun tm => PMF.pure ⟨tm.ret, c + tm.time⟩) =
      (c : ENNReal) + expected_cost p := by
  convert expected_cost_bind p _
  simp +decide [expected_cost]
  simp +decide [mul_add, Summable.tsum_add]
  simp +decide [mul_comm, ENNReal.tsum_mul_left]

/-- Core decomposition: expected cost through a `TimeMT ℕ M`
bind equals the cost of the first part plus the continuation
cost, weighted by the distribution of the first part. -/
lemma expected_cost_toPMF_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    expected_cost (inst.toPMF (m >>= f).run) =
      expected_cost (inst.toPMF m.run) +
        ∑' (tm : TimeM ℕ α),
          (inst.toPMF m.run) tm *
            expected_cost
              (inst.toPMF (f tm.ret).run) := by
  have h1 : inst.toPMF (m >>= f).run =
      (inst.toPMF m.run) >>= fun tm1 =>
        (inst.toPMF (f tm1.ret).run) >>= fun tm2 =>
          PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩ := by
    convert inst.toPMF_bind _ _ using 1
    congr! 1; ext ⟨a, t1⟩; simp +decide
    convert inst.toPMF_map _ _ using 1
    any_goals exact (f a).run
    rotate_left; exact TimeM ℕ β
    exact fun tm => ⟨tm.ret, t1 + tm.time⟩
    constructor <;> intro h
      <;> simp_all +decide [PMF.ext_iff]
    · grind +suggestions
    · convert h _ using 1
      convert h _ |> Eq.symm using 1
  convert expected_cost_bind (inst.toPMF m.run)
    (fun tm1 =>
      (inst.toPMF (f tm1.ret).run) >>= fun tm2 =>
        PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) using 1
  · grind
  · have h2 : ∀ tm1 : TimeM ℕ α,
        expected_cost
          (inst.toPMF (f tm1.ret).run >>= fun tm2 =>
            PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) =
          tm1.time +
            expected_cost (inst.toPMF (f tm1.ret).run) := by
      intro tm1; apply expected_cost_shift
    simp +decide only [h2]
    simp +decide [mul_add, ENNReal.tsum_add, expected_cost]

/-- `expected_cost` of `pure a` in `TimeMT` is `0`. -/
lemma expected_cost_toPMF_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (a : α) :
    expected_cost
      (inst.toPMF (pure a : TimeMT ℕ M α).run) = 0 := by
  convert inst.toPMF_pure a
  constructor <;> intro h <;> simp_all +decide
  · exact inst.toPMF_pure a
  · convert expected_cost_pure_val a 0
    · convert inst.toPMF_pure _
    · norm_num

/-- When the first computation is a `lift m` (zero cost),
the expected cost of the bind is the weighted sum over the
return distribution of `m`. -/
lemma expected_cost_toPMF_lift_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) (f : α → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF (TimeMT.lift m >>= f).run) =
      ∑' (a : α), (inst.toPMF m) a *
        expected_cost (inst.toPMF (f a).run) := by
  simp +zetaDelta at *
  grind +suggestions

/-- When the first computation is `tick t`, the expected cost
is `t` plus the expected cost of the continuation. -/
lemma expected_cost_toPMF_tick_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {β : Type} (t : ℕ) (f : Unit → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF (TimeMT.tick t >>= f).run) =
      (t : ENNReal) +
        expected_cost (inst.toPMF (f ()).run) := by
  have := @expected_cost_toPMF_bind
  specialize @this M ‹_› ‹_› ‹_› Unit β (TimeMT.tick t)
  convert this f using 1
  rw [show (inst.toPMF (TimeMT.tick t).run) =
    PMF.pure (⟨(), t⟩ : TimeM ℕ Unit) from ?_]
  · simp +decide [expected_cost, PMF.pure_apply]
  · exact inst.toPMF_pure _

/-- When the first computation is `pure a`, the expected cost
of the bind is the expected cost of `f a`. -/
lemma expected_cost_toPMF_pure_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (a : α) (f : α → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF
        ((pure a : TimeMT ℕ M α) >>= f).run) =
      expected_cost (inst.toPMF (f a).run) := by
  simp +zetaDelta at *

/-!
## Generic `TimeMT` erasure lemmas

Erasing time (`TimeM.ret <$> ·`) distributes through
`bind`, `pure`, `tick`, and `lift`.
-/

@[simp] lemma TimeMT_erase_bind
    {M} [Monad M] [LawfulMonad M] {α β}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    TimeM.ret <$> (m >>= f).run =
      (TimeM.ret <$> m.run) >>=
        fun a => TimeM.ret <$> (f a).run := by
  simp only [TimeMT.run_bind, map_bind]
  simp_all only [map_pure, bind_pure_comp, bind_map_left]

@[simp] lemma TimeMT_erase_pure
    {M} [Monad M] [LawfulMonad M] {α} (a : α) :
    TimeM.ret <$> (pure a : TimeMT ℕ M α).run =
      pure a := by
  simp only [TimeMT.run_pure, map_pure]

@[simp] lemma TimeMT_erase_tick
    {M} [Monad M] [LawfulMonad M] (t : ℕ) :
    TimeM.ret <$>
      (TimeMT.tick t : TimeMT ℕ M Unit).run =
      pure () := by
  simp only [TimeMT.run_tick, map_pure]

@[simp] lemma TimeMT_erase_lift
    {M} [Monad M] [LawfulMonad M] {α} (m : M α) :
    TimeM.ret <$>
      (TimeMT.lift m : TimeMT ℕ M α).run = m := by
  rw [TimeMT.run_lift, ← Functor.map_map]
  simp_all only [Functor.map_map, id_map']

end ARA
