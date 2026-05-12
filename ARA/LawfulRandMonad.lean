import ARA.Tactics

/-!
# LawfulRandMonad

A typeclass for monads with lawful randomness:
a monad `M` equipped with a `RandMonad` instance and an
interpretation into `PMF` that respects `pure`, `bind`,
and maps `randFin` to the uniform distribution.

## Architectural note

The primitive entropy source is `randFin n`, which generates
a uniform random element of `Fin n`. This is decoupled from
any particular data structure. Derived helpers like `randIdx`
for lists are provided as convenience functions.

## Main declarations

* `RandMonad` — typeclass with primitive `randFin`
* `randIdx` — derived helper for random list indexing
* `LawfulRandMonad` — the lawful typeclass with `toPMF`
* `LawfulRandMonad PMF` — canonical instance for `PMF`
-/

namespace ARA

/-!
### `RandMonad`: primitive entropy source
-/

/-- A monad with access to uniform random generation over `Fin n`.
Every finite discrete choice is isomorphic to `Fin n`, making this
the universal primitive for finite randomness. -/
class RandMonad (M : Type → Type) [Monad M] where
  /-- Generate a uniform random element of `Fin n`. -/
  randFin (n : ℕ) [NeZero n] : M (Fin n)

/-- Derived polymorphic helper: pick a random valid index into a
nonempty list. -/
def randIdx {M} [Monad M] [RandMonad M] {α}
    (L : List α) (h : 0 < L.length := by grind) : M (Fin L.length) :=
  have : NeZero L.length := ⟨h.ne'⟩
  RandMonad.randFin L.length

/-!
### Mathematical Specification
-/

/-- A `LawfulRandMonad` is a lawful monad with an
interpretation `toPMF` into `PMF` satisfying three axioms:
1. `pure` maps to `PMF.pure`
2. `bind` distributes
3. `randFin` maps to the uniform distribution -/
class LawfulRandMonad
    (M : Type → Type) [Monad M] [LawfulMonad M]
    extends RandMonad M where
  /-- Interpret an `M`-computation as a probability distribution. -/
  toPMF : ∀ {α}, M α → PMF α
  /-- `pure a` maps to the Dirac mass at `a`. -/
  toPMF_pure : ∀ {α} (a : α), toPMF (pure a) = pure a
  /-- `bind` distributes through `toPMF`. -/
  toPMF_bind : ∀ {α β} (x : M α) (f : α → M β),
    toPMF (x >>= f) =
      (toPMF x) >>= (fun a => toPMF (f a))
  /-- `randFin n` maps to the uniform distribution on `Fin n`. -/
  toPMF_randFin :
    ∀ (n : ℕ) [NeZero n],
      toPMF (randFin n) =
        (have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
         PMF.uniformOfFintype (Fin n))

/-- Derived: `toPMF` maps `randIdx` to the uniform distribution. -/
lemma LawfulRandMonad.toPMF_randIdx
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hne : 0 < L.length) :
    inst.toPMF (randIdx L hne) =
      (have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
       PMF.uniformOfFintype (Fin L.length)) := by
  unfold randIdx
  have : NeZero L.length := ⟨hne.ne'⟩
  exact inst.toPMF_randFin L.length

/-- Derived: `toPMF` respects `Functor.map`. -/
lemma LawfulRandMonad.toPMF_map
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α β} (f : α → β) (x : M α) :
    LawfulRandMonad.toPMF (f <$> x) =
      f <$> LawfulRandMonad.toPMF x := by
  rw [map_eq_bind_pure_comp, LawfulRandMonad.toPMF_bind]
  simp [LawfulRandMonad.toPMF_pure, map_eq_bind_pure_comp]

/-!
### Canonical instance: `PMF` itself
-/

/-- `PMF` is trivially a `LawfulRandMonad` via the identity. -/
noncomputable instance : RandMonad PMF where
  randFin n :=
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    PMF.uniformOfFintype (Fin n)

noncomputable instance : LawfulRandMonad PMF where
  toPMF := id
  toPMF_pure _ := rfl
  toPMF_bind _ _ := rfl
  toPMF_randFin _ := rfl

end ARA
