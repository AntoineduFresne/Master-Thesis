import Mathlib.Init
import Mathlib.Tactic.Common
import Batteries.Tactic.Lint.Basic
import Lean.Message
import Mathlib.Algebra.Group.Defs

namespace Cslib.Lint

/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

open Lean Meta Std Batteries.Tactic.Lint

/-- Compatibility helper for older `isImplicitReducible` behavior.
Skips declarations that are explicitly reducible (e.g. many `abbrev`-style defs). -/
private meta def isImplicitReducibleCompat (declName : Name) : MetaM Bool := do
  pure ((← getReducibilityStatus declName) == .reducible)

/-- A linter for checking that new declarations fall under some preexisting namespace. -/
@[env_linter]
public meta def topNamespace : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declarations are outside a namespace."
  errorsFound := "TOP LEVEL DECLARATIONS:"
  test declName := do
    if ← isAutoDecl declName then return none
    let env ← getEnv
    if ← isImplicitReducibleCompat declName then return none
    let nss := env.getNamespaceSet
    let top := nss.fold (init := (∅ : NameSet)) fun tot n =>
      match n.components with
      | r::_::_ => tot.insert r
      | _ => tot
    if top.contains declName.components[0]! then
      return none
    else
      return m!"is not namespaced."

end Cslib.Lint


section

/-!

# TimeM: Time Complexity Monad
`TimeM T α` represents a computation that produces a value of type `α` and tracks its time cost.

`T` is usually instantiated as `ℕ` to count operations, but can be instantiated as `ℝ` to count
actual wall time, or as more complex types in order to model more general costs.

## Design Principles
1. **Pure inputs, timed outputs**: Functions take plain values and return `TimeM` results
2. **Time annotations are trusted**: The `time` field is NOT verified against actual cost.
   You must manually ensure annotations match the algorithm's complexity in your cost model.
3. **Separation of concerns**: Prove correctness properties on `.ret`, prove complexity on `.time`

## Cost Model
**Document your cost model explicitly** Decide and be consistent about:
- **What costs 1 unit?** (comparison, arithmetic operation, etc.)
- **What is free?** (variable lookup, pattern matching, etc.)
- **Recursive calls:** Do you charge for the call itself?

## Notation
- **`✓`** : A tick of time, see `tick`.
- **`⟪tm⟫`** : Extract the pure value from a `TimeM` computation (notation for `tm.ret`)

## References

See [Danielsson2008] for the discussion.
-/
namespace Cslib.Algorithms.Lean

/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai, Eric Wieser
-/

/-- A monad for tracking time complexity of computations.
`TimeM T α` represents a computation that returns a value of type `α`
and accumulates a time cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure TimeM (T : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : T

namespace TimeM

/-- Lifts a pure value into a `TimeM` computation with zero time cost.

Prefer to use `pure` instead of `TimeM.pure`. -/
protected def pure [Zero T] {α} (a : α) : TimeM T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (TimeM T) where
  pure := TimeM.pure

/-- Sequentially composes two `TimeM` computations, summing their time costs.

Prefer to use the `>>=` notation. -/
protected def bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

instance [Add T] : Bind (TimeM T) where
  bind := TimeM.bind

instance : Functor (TimeM T) where
  map f x := ⟨f x.ret, x.time⟩

instance [Add T] : Seq (TimeM T) where
  seq f x := ⟨f.ret (x ()).ret, f.time + (x ()).time⟩

instance [Add T] : SeqLeft (TimeM T) where
  seqLeft x y := ⟨x.ret, x.time + (y ()).time⟩

instance [Add T] : SeqRight (TimeM T) where
  seqRight x y := ⟨(y ()).ret, x.time + (y ()).time⟩

instance [AddZero T] : Monad (TimeM T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp, grind =] theorem ret_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).ret = a := rfl
@[simp, grind =] theorem ret_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp, grind =] theorem ret_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).ret = f x.ret := rfl
@[simp] theorem ret_seqRight {α} (x : TimeM T α) (y : Unit → TimeM T β) [Add T] :
    (SeqRight.seqRight x y).ret = (y ()).ret := rfl
@[simp] theorem ret_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).ret = x.ret := rfl
@[simp] theorem ret_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).ret = f.ret (x ()).ret := rfl

@[simp, grind =] theorem time_bind {α β} [Add T] (m : TimeM T α) (f : α → TimeM T β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl
@[simp, grind =] theorem time_pure {α} [Zero T] (a : α) : (pure a : TimeM T α).time = 0 := rfl
@[simp, grind =] theorem time_map {α β} (f : α → β) (x : TimeM T α) : (f <$> x).time = x.time := rfl
@[simp] theorem time_seqRight {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqRight.seqRight x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seqLeft {α} [Add T] (x : TimeM T α) (y : Unit → TimeM T β) :
    (SeqLeft.seqLeft x y).time = x.time + (y ()).time := rfl
@[simp] theorem time_seq {α β} [Add T] (f : TimeM T (α → β)) (x : Unit → TimeM T α) :
    (Seq.seq f x).time = f.time + (x ()).time := rfl

/-- `TimeM` is lawful so long as addition in the cost is associative and absorbs zero. -/
instance [AddMonoid T] : LawfulMonad (TimeM T) := .mk'
  (id_map := fun x => rfl)
  (pure_bind := fun _ _ => by ext <;> simp)
  (bind_assoc := fun _ _ _ => by ext <;> simp [add_assoc])
  (seqLeft_eq := fun _ _ => by ext <;> simp)
  (bind_pure_comp := fun _ _ => by ext <;> simp)

/-- Creates a `TimeM` computation with a time cost. -/
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩

@[simp, grind =] theorem ret_tick (c : T) : (tick c).ret = () := rfl
@[simp, grind =] theorem time_tick (c : T) : (tick c).time = c := rfl

/-- `✓[c] x` adds `c` ticks, then executes `x`. -/
macro "✓[" c:term "]" body:doElem : doElem => `(doElem| do TimeM.tick $c; $body:doElem)

/-- `✓ x` is a shorthand for `✓[1] x`, which adds one tick and executes `x`. -/
macro "✓" body:doElem : doElem => `(doElem| ✓[1] $body)

/-- Notation for extracting the return value from a `TimeM` computation: `⟪tm⟫` -/
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

end TimeM

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
