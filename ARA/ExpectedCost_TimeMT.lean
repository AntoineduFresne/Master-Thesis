import TimeM
import ARA.ExpectedCost
import ARA.LawfulRandMonad
import ARA.MonadCost

/-!
# Expected Cost for `TimeMT`

This module bridges the `TimeMT` monad transformer (which pairs a
computation with a `ℕ`-valued time cost inside a base monad `M`)
to the `expected_cost` infrastructure defined over `TimedResult`.

## Main declarations

* `toTimedResult` / `toTimeM` — isomorphism between `TimeM ℕ α`
  and `TimedResult α`
* `expected_cost_tm` — expected cost of a `PMF (TimeM ℕ α)`
* Linearity, shift, tick, pure, lift, and bind lemmas for
  `expected_cost_tm` composed with `LawfulRandMonad.toPMF`

These are the "bridge lemmas" that connect operational `TimeMT`
code to the combinatorial cost analysis, and are not specific to
any particular algorithm.
-/

namespace ARA

open Cslib.Algorithms.Lean
open ENNReal

/-!
### `TimeM ↔ TimedResult` isomorphism
-/

/-- Convert `TimeM ℕ α` to `TimedResult α`. -/
def toTimedResult {α : Type} (tm : TimeM ℕ α) : TimedResult α :=
  ⟨tm.ret, tm.time⟩

/-- Convert `TimedResult α` to `TimeM ℕ α`. -/
def toTimeM {α : Type} (tr : TimedResult α) : TimeM ℕ α :=
  ⟨tr.val, tr.cost⟩

@[simp] lemma toTimedResult_toTimeM
    {α : Type} (tr : TimedResult α) :
    toTimedResult (toTimeM tr) = tr := rfl

@[simp] lemma toTimeM_toTimedResult
    {α : Type} (tm : TimeM ℕ α) :
    toTimeM (toTimedResult tm) = tm := by ext <;> rfl

/-!
### `expected_cost_tm`
-/

/-- Expected time cost of a `PMF` over `TimeM ℕ α` outcomes,
defined by mapping through `toTimedResult`. -/
noncomputable def expected_cost_tm
    {α : Type} (p : PMF (TimeM ℕ α)) : ENNReal :=
  expected_cost (p.map toTimedResult)

@[simp] lemma expected_cost_tm_pure_val
    {α : Type} (a : α) (t : ℕ) :
    expected_cost_tm (PMF.pure ⟨a, t⟩ : PMF (TimeM ℕ α)) =
      (t : ENNReal) := by
  simp only [expected_cost_tm, PMF.pure_map, toTimedResult]
  exact expected_cost_pure_val a t

/-!
### Linearity through `PMF.bind`
-/

/-- `expected_cost_tm` is linear through a `PMF.bind`. -/
lemma expected_cost_tm_bind
    {A : Type} {β : Type}
    (d : PMF A) (f : A → PMF (TimeM ℕ β)) :
    expected_cost_tm (d >>= f) =
      ∑' a, d a * expected_cost_tm (f a) := by
  simp only [expected_cost_tm]
  rw [show PMF.map toTimedResult (d >>= f) =
    d.bind (fun a => PMF.map toTimedResult (f a))
    from PMF.map_bind d f toTimedResult]
  exact expected_cost_bind d _

/-- `expected_cost_tm` under uniform pivot selection. -/
lemma expected_cost_tm_uniform_bind
    {n : ℕ} [NeZero n] {β : Type}
    (f : Fin n → PMF (TimeM ℕ β)) :
    expected_cost_tm
      (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
      (n : ENNReal)⁻¹ *
        ∑ i : Fin n, expected_cost_tm (f i) := by
  simp only [expected_cost_tm]
  rw [show PMF.map toTimedResult
      (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    PMF.uniformOfFintype (Fin n) >>=
      fun i => PMF.map toTimedResult (f i)
    from PMF.map_bind _ _ _]
  exact expected_cost_uniform_bind _

/-!
### `toPMF`-composed helpers

These lemmas decompose `expected_cost_tm (toPMF (… : TimeMT).run)`
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

/-- `expected_cost_tm` of a `TimeMT.lift` is `0` (no ticks). -/
lemma expected_cost_tm_lift
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (m : M α) :
    expected_cost_tm
      (inst.toPMF (TimeMT.lift m : TimeMT ℕ M α).run) =
      0 := by
  simp [expected_cost_tm]
  unfold expected_cost
  simp +decide [PMF.map]
  intro i; by_cases hi : i.cost = 0
    <;> simp_all +decide [toTimedResult]
  rintro ⟨a, t⟩ rfl
  simp_all +decide [LawfulRandMonad.toPMF_map]
  erw [PMF.map_apply]; aesop

/-- `expected_cost_tm` of `TimeMT.tick t` is `t`. -/
lemma expected_cost_tm_tick
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (t : ℕ) :
    expected_cost_tm
      (inst.toPMF (TimeMT.tick t : TimeMT ℕ M Unit).run) =
      (t : ENNReal) := by
  convert expected_cost_tm_pure_val () t
  exact inst.toPMF_pure _

/-- Shifting all time values by a constant `c` shifts the
expected cost by `c`. -/
lemma expected_cost_tm_shift
    {β : Type} (p : PMF (TimeM ℕ β)) (c : ℕ) :
    expected_cost_tm
      (p >>= fun tm => PMF.pure ⟨tm.ret, c + tm.time⟩) =
      (c : ENNReal) + expected_cost_tm p := by
  unfold expected_cost_tm
  generalize_proofs at *; (
  convert expected_cost_bind p
    (fun tm => PMF.pure ⟨tm.ret, c + tm.time⟩) using 1
  generalize_proofs at *; (
  congr! 2
  generalize_proofs at *; (
  convert PMF.map_bind _ _ _ using 1
  generalize_proofs at *; (
  unfold PMF.map; aesop;)));
  unfold expected_cost; simp +decide [mul_add]; ring_nf;
  rw [ENNReal.tsum_add];
  congr! 1;
  · rw [ENNReal.tsum_mul_left,
      show ∑' a : TimeM ℕ β, p a = 1 from ?_]
    · norm_num
    · convert p.tsum_coe
  · rw [← tsum_eq_tsum_of_ne_zero_bij];
    use fun x => toTimeM x.val;
    · intro x y; aesop;
    · intro x hx
      use ⟨toTimedResult x, by aesop⟩; aesop;
    · intro x
      erw [tsum_eq_single (toTimeM x.val)] <;> aesop;)

/-- Core decomposition: expected cost through a `TimeMT ℕ M`
bind equals the cost of the first part plus the continuation
cost, weighted by the distribution of the first part. -/
lemma expected_cost_tm_toPMF_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    expected_cost_tm (inst.toPMF (m >>= f).run) =
      expected_cost_tm (inst.toPMF m.run) +
        ∑' (tm : TimeM ℕ α),
          (inst.toPMF m.run) tm *
            expected_cost_tm
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
  convert expected_cost_tm_bind (inst.toPMF m.run)
    (fun tm1 =>
      (inst.toPMF (f tm1.ret).run) >>= fun tm2 =>
        PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) using 1
  · grind
  · have h2 : ∀ tm1 : TimeM ℕ α,
        expected_cost_tm
          (inst.toPMF (f tm1.ret).run >>= fun tm2 =>
            PMF.pure ⟨tm2.ret, tm1.time + tm2.time⟩) =
          tm1.time +
            expected_cost_tm (inst.toPMF (f tm1.ret).run) := by
      intro tm1; apply expected_cost_tm_shift
    simp +decide only [h2]
    simp +decide [mul_add, ENNReal.tsum_add, expected_cost_tm]
    unfold expected_cost
    rw [← Equiv.tsum_eq
      (Equiv.ofBijective
        (fun tm : TimeM ℕ α => ⟨tm.ret, tm.time⟩)
        ⟨fun tm => ?_, fun tm => ?_⟩)]
    all_goals norm_num [TimeM.ext_iff]
    · congr! 2; ext ⟨a, t⟩; simp [toTimedResult]
      rw [tsum_eq_single ⟨a, t⟩] <;> aesop
    · exact ⟨⟨tm.val, tm.cost⟩, rfl⟩

/-- `expected_cost_tm` of `pure a` in `TimeMT` is `0`. -/
lemma expected_cost_tm_toPMF_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (a : α) :
    expected_cost_tm
      (inst.toPMF (pure a : TimeMT ℕ M α).run) = 0 := by
  convert inst.toPMF_pure a
  constructor <;> intro h <;> simp_all +decide
  · exact inst.toPMF_pure a
  · convert expected_cost_tm_pure_val a 0
    · convert inst.toPMF_pure _
    · norm_num

/-- When the first computation is a `lift m` (zero cost),
the expected cost of the bind is the weighted sum over the
return distribution of `m`. -/
lemma expected_cost_tm_toPMF_lift_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : M α) (f : α → TimeMT ℕ M β) :
    expected_cost_tm
      (inst.toPMF (TimeMT.lift m >>= f).run) =
      ∑' (a : α), (inst.toPMF m) a *
        expected_cost_tm (inst.toPMF (f a).run) := by
  simp +zetaDelta at *
  grind +suggestions

/-- When the first computation is `tick t`, the expected cost
is `t` plus the expected cost of the continuation. -/
lemma expected_cost_tm_toPMF_tick_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {β : Type} (t : ℕ) (f : Unit → TimeMT ℕ M β) :
    expected_cost_tm
      (inst.toPMF (TimeMT.tick t >>= f).run) =
      (t : ENNReal) +
        expected_cost_tm (inst.toPMF (f ()).run) := by
  have := @expected_cost_tm_toPMF_bind
  specialize @this M ‹_› ‹_› ‹_› Unit β (TimeMT.tick t)
  convert this f using 1
  rw [show (inst.toPMF (TimeMT.tick t).run) =
    PMF.pure (toTimeM ⟨(), t⟩) from ?_]
  · simp +decide [expected_cost_tm, PMF.pure_apply]
  · exact inst.toPMF_pure _

/-- When the first computation is `pure a`, the expected cost
of the bind is the expected cost of `f a`. -/
lemma expected_cost_tm_toPMF_pure_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (a : α) (f : α → TimeMT ℕ M β) :
    expected_cost_tm
      (inst.toPMF
        ((pure a : TimeMT ℕ M α) >>= f).run) =
      expected_cost_tm (inst.toPMF (f a).run) := by
  simp +zetaDelta at *

/-!
### Generic `TimeMT` erasure lemmas

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
