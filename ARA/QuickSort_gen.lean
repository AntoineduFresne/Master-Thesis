import ARA.Tactics
import TimeM

class RandMonad (M : Type → Type) [Monad M] where
  -- Given a nonempty list, pick a random valid index
  randIdx {α} : (L : List α) → 0 < L.length → M (Fin L.length)

def QuickSort [Monad M] [RandMonad M] : List ℕ → M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      let S1 ← QuickSort L1
      let S2 ← QuickSort L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
decreasing_by all_goals grind

instance : RandMonad IO where
  randIdx L hne := do
    let i ← IO.rand 0 (L.length - 1)
    return ⟨i % L.length, Nat.mod_lt i hne⟩

noncomputable instance : RandMonad PMF where
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
    PMF.uniformOfFintype (Fin L.length)

-- IO version (executable)
def QuickSort_IO : List ℕ → IO (List ℕ) := QuickSort

#eval QuickSort_IO [5,4,2,1,3]

-- PMF version (noncomputable specification)
noncomputable def QuickSort_PMF : List ℕ → PMF (List ℕ) := QuickSort

open Cslib.Algorithms.Lean
#check TimeMT

/-- RandMonad lifts automatically through TimeMT via monadLift -/
instance {M} [Monad M] [RandMonad M] : RandMonad (TimeMT ℕ M) where
  randIdx L h := TimeMT.lift (RandMonad.randIdx L h)

def QuickSortTimed [Monad M] [RandMonad M] :
    List ℕ → TimeMT ℕ M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      -- each element of `rest` is compared once against pivot
      TimeMT.tick rest.length
      let S1 ← QuickSortTimed L1
      let S2 ← QuickSortTimed L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
decreasing_by all_goals grind

-- IO version (executable)
def QuickSortT_Rand: List ℕ → TimeMT ℕ IO (List ℕ) := QuickSortTimed

#eval (QuickSortT_Rand [5,4,2,1,3,6,10,29,0]).run

noncomputable def QuickSortT_Rand_PMF: List ℕ → TimeMT ℕ PMF (List ℕ) := QuickSortTimed
