import ARA.Tactics

/-!
# LawfulRandMonad

A typeclass for monads with lawful randomness:
a monad `M` equipped with a `RandMonad` instance and an
interpretation into `PMF` that respects `pure`, `bind`,
and maps `randIdx` to the uniform distribution.

## Main declarations

* `LawfulRandMonad` — the typeclass
* `LawfulRandMonad.toPMF_map` — derived functorial law
* `LawfulRandMonad PMF` — canonical instance for `PMF`
-/

namespace ARA

/-
We re-state `RandMonad` here so that downstream files can
import this module without pulling in QuickSort.
-/
class RandMonad (M : Type → Type) [Monad M] where
  /-- Given a nonempty list, pick a random valid index. -/
  randIdx {α} :
    (L : List α) → 0 < L.length → M (Fin L.length)

/-!
### Mathematical Specification
-/

/-- A `LawfulRandMonad` is a lawful monad with an
interpretation `toPMF` into `PMF` satisfying three axioms:
1. `pure` maps to `PMF.pure`
2. `bind` distributes
3. `randIdx` maps to the uniform distribution -/
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
  /-- `randIdx` maps to the uniform distribution on `Fin n`. -/
  toPMF_randIdx :
    ∀ (L : List ℕ) (hne : 0 < L.length),
      toPMF (randIdx L hne) =
        (have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
         PMF.uniformOfFintype (Fin L.length))

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
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
    PMF.uniformOfFintype (Fin L.length)

noncomputable instance : LawfulRandMonad PMF where
  toPMF := id
  toPMF_pure _ := rfl
  toPMF_bind _ _ := rfl
  toPMF_randIdx _ _ := rfl

end ARA
