/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
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

/-- RandMonad lifts through `TimeMT` via `monadLift`, so any
randomized algorithm can be run in timed mode. -/
instance instRandMonadTimeMT {M} [Monad M] [RandMonad M] :
    RandMonad (TimeMT ℕ M) where
  randFin n := TimeMT.lift (RandMonad.randFin n)

/-- In `TimeMT`, `randIdx` is a lifted `randIdx` of the base monad.
Exposes the `TimeMT.lift` for erasure/bridge lemma application. -/
@[simp] lemma TimeMT_randIdx_run
    {M} [Monad M] [RandMonad M] {α : Type*}
    (L : List α) (h : 0 < L.length) :
    (randIdx L h : TimeMT ℕ M (Fin L.length)).run =
    (TimeMT.lift (randIdx L h : M (Fin L.length))).run := rfl

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

@[simp, expected_cost_simp] lemma expected_cost_pure_zero {α : Type} (a : α) :
    expected_cost (PMF.pure ⟨a, 0⟩) = 0 := by
  unfold expected_cost; aesop

@[simp, expected_cost_simp] lemma expected_cost_pure_val {α : Type} (a : α) (t : ℕ) :
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

/-- Averaging bound: if a total of `n` branch costs is at most `n * c`,
then the uniform average over the `n` branches is at most `c`.
This is the standard closing step of a uniform-pivot cost analysis.

Stated with `le_trans` in mind rather than `calc`: unifying against a
concrete sum `S` is a cheap metavariable assignment. -/
lemma uniform_avg_le {n : ℕ} (hn : n ≠ 0) {S c : ENNReal}
    (h : S ≤ n * c) :
    (n : ENNReal)⁻¹ * S ≤ c := by
  refine le_trans (mul_le_mul' le_rfl h) ?_
  rw [← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n),
    one_mul]

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
@[expected_cost_simp] lemma expected_cost_lift
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
@[expected_cost_simp] lemma expected_cost_tick
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
    simp only [TimeMT.run_bind, inst.toPMF_bind, inst.toPMF_pure]
    rfl
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
@[expected_cost_simp] lemma expected_cost_toPMF_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α : Type} (a : α) :
    expected_cost
      (inst.toPMF (pure a : TimeMT ℕ M α).run) = 0 := by
  rw [TimeMT.run_pure, inst.toPMF_pure]
  exact expected_cost_pure_zero a

/-- When the first computation is a `lift m` (zero cost),
the expected cost of the bind is the weighted sum over the
return distribution of `m`. -/
@[expected_cost_simp] lemma expected_cost_toPMF_lift_bind
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
@[expected_cost_simp] lemma expected_cost_toPMF_tick_bind
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
@[expected_cost_simp] lemma expected_cost_toPMF_pure_bind
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (a : α) (f : α → TimeMT ℕ M β) :
    expected_cost
      (inst.toPMF
        ((pure a : TimeMT ℕ M α) >>= f).run) =
      expected_cost (inst.toPMF (f a).run) := by
  simp +zetaDelta at *

/-- Pure post-processing costs nothing: `E[m >>= (pure ∘ g)] = E[m]`.
Lets `cost_step` erase the trailing `return (f x)` of a branch. -/
@[expected_cost_simp] lemma expected_cost_toPMF_bind_pure
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    {α β : Type} (m : TimeMT ℕ M α) (g : α → β) :
    expected_cost
      (inst.toPMF (m >>= fun a => (pure (g a) : TimeMT ℕ M β)).run) =
      expected_cost (inst.toPMF m.run) := by
  rw [expected_cost_toPMF_bind]
  simp only [expected_cost_toPMF_pure, mul_zero, tsum_zero, add_zero]

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

/-!
## Notation and wrappers for expected runtime

We provide user-friendly wrappers and notation so that the expected runtime
of a timed computation can be written concisely.

* `TimedPMF m`     — distribution over `(value, time)` pairs obtained by
  interpreting `m : TimeMT ℕ M α` via a `LawfulRandMonad`.
* `runtime m`      — `expected_cost (TimedPMF m) : ENNReal`, named API.
* `runtime_ℝ m`    — `(runtime m).toReal : ℝ`, named API. Convenient for
  stating closed-form bounds like `2(n+1)H(n) − 4n`.
* `𝔼_cost[p]`      — notation for `expected_cost p`.
* `𝔼_runtime[m]`   — notation for `expected_cost (TimedPMF m)` (defeq
  to `runtime m`). Expands to the underlying form so `simp`/`rw` can
  match bridge lemmas without unfolding hints.
* `𝔼ℝ_runtime[m]`  — notation for `(𝔼_runtime[m]).toReal`.

### Usage with polymorphic algorithms

When the algorithm `f` is polymorphic in its monad (the typical case in
this framework, e.g. `Quicksort`), Lean cannot infer which monad to
instantiate from context. Use a type ascription:

```
𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)] = expected_qs_cost L.length
```

The instances `instRandMonadTimeMT` and `instMonadCostTimeMT` are picked
up automatically by priority resolution. -/

/-- The distribution over `(value, time)` pairs obtained by interpreting
a timed computation `m : TimeMT ℕ M α` via a `LawfulRandMonad` instance.
This is the object whose expected cost we analyze. -/
noncomputable abbrev TimedPMF
    {M : Type → Type} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] {α : Type}
    (m : TimeMT ℕ M α) : PMF (TimeM ℕ α) :=
  inst.toPMF m.run

/-- Expected runtime of a timed computation, as `ENNReal`. -/
noncomputable abbrev runtime
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α : Type} (m : TimeMT ℕ M α) : ENNReal :=
  expected_cost (TimedPMF m)

/-- Expected runtime of a timed computation, as a real number.
Convenient for stating closed-form complexity bounds. -/
noncomputable abbrev runtime_ℝ
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α : Type} (m : TimeMT ℕ M α) : ℝ :=
  (runtime m).toReal

/-- `𝔼_cost[p]` ≡ `expected_cost p`, where `p : PMF (TimeM ℕ α)`. -/
scoped notation "𝔼_cost[" p "]" => expected_cost p

/-- `𝔼_runtime[m]` ≡ `expected_cost (TimedPMF m)`, the expected runtime
of `m` as `ENNReal`. Expands to the underlying form so `simp`/`rw` can
match bridge lemmas like `expected_cost_toPMF_bind`. -/
scoped notation "𝔼_runtime[" m "]" => expected_cost (TimedPMF m)

/-- `𝔼ℝ_runtime[m]` ≡ `(𝔼_runtime[m]).toReal`, the expected runtime of `m`
as `ℝ`. Use type ascription `(f L : TimeMT ℕ M _)` when `f` is polymorphic. -/
scoped macro "𝔼ℝ_runtime[" m:term "]" : term =>
  `((expected_cost (TimedPMF $m)).toReal)

/-- `𝔼_runtime[e | M]` — expected runtime (`ℝ≥0∞`) of the
monad-polymorphic algorithm `e`, instantiated at the random monad `M`
and timed via `TimeMT ℕ M`. Sugar for the type ascription
`𝔼_runtime[(e : TimeMT ℕ M _)]`; both elaborate to the same term. -/
scoped macro "𝔼_runtime[" e:term " | " M:term "]" : term =>
  `(expected_cost (TimedPMF ($e : TimeMT ℕ $M _)))

/-- `𝔼ℝ_runtime[e | M]` — real-valued expected runtime of the
monad-polymorphic algorithm `e` at the random monad `M`. -/
scoped macro "𝔼ℝ_runtime[" e:term " | " M:term "]" : term =>
  `((expected_cost (TimedPMF ($e : TimeMT ℕ $M _))).toReal)

/-!
### Arithmetic cleanups in `expected_cost_simp`

After peeling a `pure` reduces a continuation to `0`, the surrounding
`mul_zero / tsum_zero / add_zero` should collapse automatically so
that `cost_step` produces a clean form.
-/

attribute [expected_cost_simp] mul_zero zero_mul add_zero zero_add
attribute [expected_cost_simp] tsum_zero

/-!
## Automation tactics

These tactics chain the bridge lemmas (`expected_cost_toPMF_pure`,
`…_pure_bind`, `…_tick_bind`, `…_lift_bind`, `expected_cost_tick`,
`expected_cost_lift`) tagged with `@[expected_cost_simp]`. They peel
off `TimeMT` combinators from the head of a computation until either
the cost is fully computed or only an opaque recursive call remains
(to be handled by induction).

### Example

```
lemma my_algo_cost : 𝔼_runtime[(myAlgo n : TimeMT ℕ M _)] = ... := by
  rw [myAlgo.eq_def]   -- unfold the algorithm
  cost_step            -- peel `tick`/`lift`/`pure`/`bind` away
  ...                  -- handle the recursive part
```
-/

/-- `cost_step` peels one or more `TimeMT` combinators off the head of
an `𝔼_runtime[·]` expression by chaining the `expected_cost_simp` set.

This rewrites:
* `𝔼_runtime[tick t >>= f]`  ↦  `t + 𝔼_runtime[f ()]`
* `𝔼_runtime[lift m >>= f]`  ↦  `∑' a, toPMF m a * 𝔼_runtime[f a]`
* `𝔼_runtime[pure a >>= f]`  ↦  `𝔼_runtime[f a]`
* `𝔼_runtime[pure a]`        ↦  `0`
* `𝔼_runtime[tick t]`        ↦  `t`
* `𝔼_runtime[lift m]`        ↦  `0`

When an extra rewrite is needed (e.g. unfolding a recursive call),
combine with `simp only [expected_cost_simp, my_lemma]` directly. -/
scoped macro "cost_step" : tactic =>
  `(tactic| simp only [expected_cost_simp])

/-- `runtime_simp` is the combined normalizer: peels `TimeMT` combinators
with `expected_cost_simp`, then cleans up arithmetic/`PMF` weights via
`pmf_simp_attr`. Intended for fully-closed cost computations. -/
scoped macro "runtime_simp" : tactic =>
  `(tactic| (simp only [expected_cost_simp, pmf_simp_attr]; try norm_num))

/-!
## Uniform-pivot recipes

The two lemmas below package the algorithm-independent steps of a
uniform-pivot cost analysis, so that a new algorithm's *step lemma* is
one `rw` plus its branch decomposition:

```
lemma expected_cost_myAlgo_step ... :
    𝔼_runtime[(myAlgo (x :: xs) : TimeMT ℕ M _)] =
    ((x :: xs).length : ENNReal)⁻¹ * ∑ i, (branch cost i) := by
  rw [myAlgo_timed_eq_bind, expected_cost_uniform_step]
  congr 1
  exact Finset.sum_congr rfl fun i _ => expected_cost_myAlgo_branch ..
```
-/

/-- **Uniform-pivot step.** The expected cost of
`lift (randIdx L) >>= branch` is the uniform average of the branch
costs: the one-step recurrence `E = (1/n) · Σᵢ E[branch i]`. -/
lemma expected_cost_uniform_step
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → TimeMT ℕ M β) :
    𝔼_runtime[TimeMT.lift (randIdx L hL : M _) >>= f] =
    (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, 𝔼_runtime[f i] := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  show expected_cost (inst.toPMF
    (TimeMT.lift (randIdx L hL : M _) >>= f).run) = _
  cost_step
  rw [inst.toPMF_randIdx, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-- Distribute `toReal` through a uniform average of finite branch
costs. Feed the `≠ ⊤` side conditions from the algorithm's ENNReal
upper bound. -/
lemma toReal_uniform_avg {n : ℕ} {S : Fin n → ENNReal}
    (h : ∀ i, S i ≠ ⊤) :
    ((n : ENNReal)⁻¹ * ∑ i, S i).toReal = (n : ℝ)⁻¹ * ∑ i, (S i).toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun i _ => h i]

end ARA
