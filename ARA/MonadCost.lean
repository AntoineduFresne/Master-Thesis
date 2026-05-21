/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import TimeM

/-!
# MonadCost

A typeclass for monads that can track computational cost.

## Design

`MonadCost C M` provides a single operation `tick : C → M Unit` that
records a cost increment. By varying the instance, the same algorithm
can run in cost-free mode (where `tick` is a no-op) or in timed mode
(where `tick` accumulates cost).

This eliminates the need to write each algorithm twice (untimed and
timed), reducing code duplication and ensuring the control-flow logic
is verified exactly once.

## Main declarations

* `MonadCost` — the typeclass
* `MonadCost.instDefault` — blanket no-op instance (low priority)
* `MonadCost.instTimeMT` — `TimeMT` instance that accumulates cost
-/

namespace ARA

open Cslib.Algorithms.Lean

/-- A typeclass for monads that can track computational cost.
`tick c` records a cost of `c`. -/
class MonadCost (C : Type) (M : Type → Type) where
  /-- Record a cost increment of `c`. -/
  tick : C → M Unit

/-- Default instance: ticking is a no-op (`pure ()`).
This is used when running the algorithm without cost tracking.
Low priority so that the `TimeMT` instance takes precedence. -/
instance (priority := 100) instMonadCostDefault
    {C} {M} [Monad M] : MonadCost C M where
  tick _ := pure ()

/-- `TimeMT` instance: ticking accumulates cost via `TimeMT.tick`.
Higher priority than the default no-op instance. -/
instance (priority := 1000) instMonadCostTimeMT
    {M} [Monad M] : MonadCost ℕ (TimeMT ℕ M) where
  tick := TimeMT.tick

/-! ### Simp lemmas for MonadCost -/

@[simp] lemma MonadCost.tick_default
    {C} {M} [Monad M] (c : C) :
    @MonadCost.tick C M instMonadCostDefault c = pure () := rfl

@[simp] lemma MonadCost.tick_timeMT
    {M} [Monad M] (c : ℕ) :
    @MonadCost.tick ℕ (TimeMT ℕ M) instMonadCostTimeMT c =
    TimeMT.tick c := rfl

end ARA
