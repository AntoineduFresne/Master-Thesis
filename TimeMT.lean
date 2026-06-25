/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Cslib.Algorithms.Lean.TimeM

/-!
# TimeMT: Time Complexity Monad Transformer

The base time-complexity monad `TimeM` (and the `Cslib.Lint` linter) are
provided by `cslib` (`Cslib.Algorithms.Lean.TimeM`). This file adds the
`TimeMT` monad transformer, which threads a time cost `T` through an
arbitrary base monad `M`, so that the same algorithm can run in a plain
monad or in a randomized monad (e.g. `PMF`) while accumulating cost.

`TimeMT` is the object the `ARA` framework analyzes.
-/

namespace Cslib.Algorithms.Lean

/-- Monad transformer that threads a time cost `T` through an
    arbitrary base monad `M`. -/

@[ext]
structure TimeMT (T : Type u) (M : Type (max u v) → Type w) (α : Type v) : Type w where
  run : M (TimeM T α)

namespace TimeMT

variable {T : Type} {M : Type → Type} {α β : Type}

/-! ## Core operations -/

protected def pure [Zero T] [Pure M] (a : α) : TimeMT T M α :=
  ⟨Pure.pure ⟨a, 0⟩⟩

protected def bind [Add T] [Monad M]
    (m : TimeMT T M α) (f : α → TimeMT T M β) : TimeMT T M β := ⟨do
    let ⟨a, t1⟩ ← m.run
    let ⟨b, t2⟩ ← (f a).run
    pure ⟨b, t1 + t2⟩⟩


  --⟨m.run >>= fun ⟨a, t1⟩ => (f a).run >>= fun ⟨b, t2⟩ => pure ⟨b, t1 + t2⟩⟩

instance [Zero T] [Add T] [Monad M] : Monad (TimeMT T M) where
  pure := TimeMT.pure
  bind := TimeMT.bind

/-! ## Lifting and costing -/

def lift [Zero T] [Functor M] (ma : M α) : TimeMT T M α :=
  ⟨(fun a => (⟨a, 0⟩ : TimeM T α)) <$> ma⟩

instance [Zero T] [Add T] [Monad M] : MonadLift M (TimeMT T M) where
  monadLift := lift

def tick [Monad M] (t : T) : TimeMT T M Unit :=
  ⟨Pure.pure ⟨(), t⟩⟩

instance [Functor M] : Functor (TimeMT T M) where
  map f m := ⟨(fun ⟨a, t⟩ => ⟨f a, t⟩) <$> m.run⟩

instance [Zero T] [Pure M] : Pure (TimeMT T M) where
  pure := TimeMT.pure

instance [Add T] [Monad M] : Bind (TimeMT T M) where
  bind := TimeMT.bind

-- Seq needs both since it combines two timed computations
instance [Zero T] [Add T] [Monad M] : Applicative (TimeMT T M) where
  pure := TimeMT.pure
  seq mf mx := ⟨do
    let ⟨f, t1⟩ ← mf.run
    let ⟨x, t2⟩ ← (mx ()).run
    pure ⟨f x, t1 + t2⟩⟩

instance [Zero T] [Add T] [Monad M] : Monad (TimeMT T M) where
  bind := TimeMT.bind

/-! ## Simp lemmas -/

@[simp] theorem run_pure [Zero T] [Pure M] (a : α) :
    (pure a : TimeMT T M α).run = pure ⟨a, 0⟩ := rfl

@[simp] theorem run_bind [Add T] [Monad M] (m : TimeMT T M α) (f : α → TimeMT T M β) :
    (m >>= f).run =
      m.run >>= fun ⟨a, t1⟩ => (f a).run >>= fun ⟨b, t2⟩ => pure ⟨b, t1 + t2⟩ := rfl

@[simp] theorem run_map [Functor M] (f : α → β) (m : TimeMT T M α) :
    (f <$> m).run = (fun ⟨a, t⟩ => (⟨f a, t⟩ : TimeM T β)) <$> m.run := rfl

@[simp]
theorem run_tick [Zero T] [Monad M] (t : T) :
    (tick t : TimeMT T M Unit).run = Pure.pure ⟨(), t⟩ := rfl

@[simp]
theorem run_lift [Zero T] [Functor M] (ma : M α) :
    (lift ma : TimeMT T M α).run = (fun a => (⟨a, 0⟩ : TimeM T α)) <$> ma := rfl

@[simp]
theorem run_monadLift [Zero T] [Add T] [Monad M] (ma : M α) :
    (monadLift ma : TimeMT T M α).run = (fun a => (⟨a, 0⟩ : TimeM T α)) <$> ma := rfl



end TimeMT

end Cslib.Algorithms.Lean
