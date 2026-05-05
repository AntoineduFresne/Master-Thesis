import ARA.Tactics
import TimeM

/-!
# QuickSort

This module implement a modular versions of QuickSort
using typeclasses to abstract over the type of randomness.
-/

namespace ARA

class RandMonad (M : Type → Type) [Monad M] where
  -- Given a nonempty list, pick a random valid index
  randIdx {α} : (L : List α) → 0 < L.length → M (Fin L.length)

def QuickSort {M : Type → Type} [Monad M] [RandMonad M] : List ℕ → M (List ℕ)
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

-- Differente instance of "randomness"

-- IO: real computable (pseudo-)randomness
instance : RandMonad IO where
  randIdx L hne := do
    let i ← IO.rand 0 (L.length - 1)
    return ⟨i % L.length, Nat.mod_lt i hne⟩

-- PMF: noncomputable randomness uniform distribution over valid indices
noncomputable instance : RandMonad PMF where
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
    PMF.uniformOfFintype (Fin L.length)

-- IO version (executable)
def QuickSort_IO: List ℕ → IO (List ℕ) := QuickSort

#eval QuickSort_IO [0,1,22,43,46,45,43,45,45,67,89,789,8,656]

-- PMF version (noncomputable specification)
noncomputable def QuickSort_PMF : List ℕ → PMF (List ℕ) := QuickSort

-- ----------------------------------------------------
-- Correctness proof of the PMF version
-- (and hence of all versions because the code is the ?)
-- ----------------------------------------------------

/-! ### Helper lemmas -/

open List

/-- Two sorted ℕ-permutations are equal. -/
lemma eq_of_sortedLE_perm {l1 l2 : List ℕ}
    (h1 : l1.SortedLE) (h2 : l2.SortedLE) (hp : l1.Perm l2) : l1 = l2 :=
  hp.eq_of_pairwise (fun _ _ _ _ hab hba => Nat.le_antisymm hab hba)
    (sortedLE_iff_pairwise.mp h1) (sortedLE_iff_pairwise.mp h2)

/-- Concatenation `S1 ++ [p] ++ S2` is sorted when `S1 < p ≤ S2` and both sublists sorted. -/
lemma sorted_concat_pivot {S1 S2 : List ℕ} {p : ℕ}
    (h1 : S1.SortedLE) (h2 : S2.SortedLE)
    (hb1 : ∀ x ∈ S1, x < p) (hb2 : ∀ x ∈ S2, p ≤ x) :
    (S1 ++ [p] ++ S2).SortedLE := by
  rw [sortedLE_iff_pairwise]; apply pairwise_append.mpr
  refine ⟨?_, sortedLE_iff_pairwise.mp h2, fun x hx y hy => by grind⟩
  rw [← sortedLE_iff_pairwise, sortedLE_iff_pairwise]; grind

/-! eraseIdx gives back a permutation -/
lemma perm_getElem_cons_eraseIdx (L : List ℕ) (i : Fin L.length) :
    L.Perm (L[i] :: L.eraseIdx i) := by
  induction' i with i ih;
  induction' L with hd tl ih generalizing i ; aesop;
  rcases i with ( _ | i ) <;> simp_all +decide [ List.eraseIdx ];
  exact List.Perm.trans
    (List.Perm.cons _ ( ih _ <| by simpa using ‹i + 1 < List.length ( hd :: tl ) › ) )
    ( List.Perm.swap .. )

/-- Filter-partition around a pivot permutes the original list. -/
lemma perm_filter_partition (L : List ℕ) (i : Fin L.length) :
    ((L.eraseIdx i).filter (fun x => decide (x < L[i])) ++ [L[i]] ++
     (L.eraseIdx i).filter (fun x => decide (x ≥ L[i]))).Perm L := by
  have hc : (L.eraseIdx i).filter (fun x => !(decide (x < L[i]))) =
            (L.eraseIdx i).filter (fun x => decide (x ≥ L[i])) := by grind
  have hf := filter_append_perm (fun x => decide (x < L[i])) (L.eraseIdx i)
  rw [hc] at hf
  have hmid : ((L.eraseIdx i).filter (fun x => decide (x < L[i])) ++ [L[i]] ++
               (L.eraseIdx i).filter (fun x => decide (x ≥ L[i]))).Perm
              (L[i] :: ((L.eraseIdx i).filter (fun x => decide (x < L[i])) ++
                        (L.eraseIdx i).filter (fun x => decide (x ≥ L[i])))) := by
    simp only [append_assoc]; grind
  exact hmid.trans ((Perm.cons _ hf).trans (perm_getElem_cons_eraseIdx L i).symm)

/-!
###  Abbreviation
of the partition-and-recurse step (at given pivot index) to make the code cleaner.
-/

private noncomputable abbrev qs_branch (M : Type → Type) [Monad M] [RandMonad M] (L : List ℕ) (i : Fin L.length) : PMF (List ℕ) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  let S1 ← QuickSort (rest.filter (· < pivot))
  let S2 ← QuickSort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

/-!
### Main correctness lemma
-/

lemma Correctness_Quicksort_PMF : ∀ L : List ℕ, ∃ Output : List ℕ,
    QuickSort_PMF L = PMF.pure Output ∧ Output.SortedLE ∧ Output.Perm L := by
  apply QuickSort.induct
  -- Base case
  · exact ⟨[], by {simp [QuickSort.eq_1, QuickSort_PMF] ; rfl}, by simp [sortedLE_iff_pairwise], by simp⟩
  -- Inductive case
  · intro head tail ihL1 ihL2
    let L := head :: tail
    -- For each pivot, build a correct output from the IH
    have h_step : ∀ i : Fin L.length, ∃ Out,
        qs_branch PMF L i = PMF.pure Out ∧ Out.SortedLE ∧ Out.Perm L := by
      intro i
      obtain ⟨O1, h1, s1, p1⟩ := ihL1 i
      obtain ⟨O2, h2, s2, p2⟩ := ihL2 i
      use O1 ++ [L[i]] ++ O2
      split_ands
      · unfold qs_branch; unfold_do; simp [QuickSort_PMF] at h1 h2; sorry
      · apply sorted_concat_pivot s1 s2 <;> grind
      · exact (Perm.append (Perm.append p1 (.refl _)) p2).trans (perm_filter_partition L i)
    -- All pivots yield the same output (uniqueness of sorted permutation)
    obtain ⟨Output, h0, hS, hP⟩ := h_step ⟨0, by grind⟩
    refine ⟨Output, ?_, hS, hP⟩
    have : Nonempty (Fin L.length) := ⟨⟨0, by grind⟩⟩
    calc QuickSort_PMF L
        = (PMF.uniformOfFintype (Fin L.length)).bind (qs_branch PMF L) := by
          unfold qs_branch; simpa [L, ← PMF.bind_pure_comp] using QuickSort.eq_2 head tail
      _ = (PMF.uniformOfFintype (Fin L.length)).bind fun _ => PMF.pure Output := by
          congr 1; funext i
          obtain ⟨Oi, hi, si, pi⟩ := h_step i
          rwa [eq_of_sortedLE_perm si hS (pi.trans hP.symm)] at hi
      _ = PMF.pure Output := PMF.bind_const _ _

end ARA
