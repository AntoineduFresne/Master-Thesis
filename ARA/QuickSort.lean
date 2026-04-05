import ARA.Phase2
import ARA.Tactics

/-!
# QuickSort Correctness Proof

This module proves that QuickSort_A always returns a sorted permutation of its input.

The proof uses the custom induction principle QuickSort_A.induct and relies on
a few helper lemmas: uniqueness of sorted permutations, sorted concatenation around
a pivot, eraseIdx gives a permutation of the original list, and the filter-partition
permutation property.
-/

namespace ARA

open PMF List

/-! ### Helper lemmas -/

/-- The partition-and-recurse step for a given pivot index. -/
private noncomputable abbrev qs_branch (L : List ℕ) (i : Fin L.length) : PMF (List ℕ) :=
  (QuickSort_A ((L.eraseIdx i).filter (· < L[i]))).bind fun S1 =>
  (QuickSort_A ((L.eraseIdx i).filter (· ≥ L[i]))).bind fun S2 =>
  PMF.pure (S1 ++ [L[i]] ++ S2)

private noncomputable abbrev qs_branch' (L : List ℕ) (i : Fin L.length) : PMF (List ℕ) :=
   (QuickSort_A ((L.eraseIdx i).filter (· < L[i]))).bind fun S1 =>
   (QuickSort_A ((L.eraseIdx i).filter (· ≥ L[i]))).bind fun S2 =>
   PMF.pure (S1 ++ [L[i]] ++ S2)

lemma qs_br_eq: qs_branch = qs_branch' := by rfl
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

/-! ### Correctness Proof -/

lemma Correctness_Quicksort_A : ∀ L : List ℕ, ∃ Output : List ℕ,
    QuickSort_A L = PMF.pure Output ∧ Output.SortedLE ∧ Output.Perm L := by
  apply QuickSort_A.induct
  -- Base case
  · exact ⟨[], by simp [QuickSort_A.eq_1], by simp [sortedLE_iff_pairwise], by simp⟩
  -- Inductive case
  · intro head tail _ ihL1 ihL2
    let L := head :: tail
    -- For each pivot, build a correct output from the IH
    have h_step : ∀ i : Fin L.length, ∃ Out,
        qs_branch L i = PMF.pure Out ∧ Out.SortedLE ∧ Out.Perm L := by
      intro i
      obtain ⟨O1, h1, s1, p1⟩ := ihL1 i
      obtain ⟨O2, h2, s2, p2⟩ := ihL2 i
      use O1 ++ [L[i]] ++ O2
      split_ands
      · grind only [= PMF.pure_bind]
      · apply sorted_concat_pivot s1 s2 <;> grind
      · exact (Perm.append (Perm.append p1 (.refl _)) p2).trans (perm_filter_partition L i)
    -- All pivots yield the same output (uniqueness of sorted permutation)
    obtain ⟨Output, h0, hS, hP⟩ := h_step ⟨0, by grind⟩
    refine ⟨Output, ?_, hS, hP⟩
    calc QuickSort_A L
        = (PMF.uniformOfFintype (Fin L.length)).bind (qs_branch L) := by
          unfold qs_branch; simpa [L, ← PMF.bind_pure_comp] using QuickSort_A.eq_2 head tail
      _ = (PMF.uniformOfFintype (Fin L.length)).bind fun _ => PMF.pure Output := by
          congr 1; funext i
          obtain ⟨Oi, hi, si, pi⟩ := h_step i
          rwa [eq_of_sortedLE_perm si hS (pi.trans hP.symm)] at hi
      _ = PMF.pure Output := PMF.bind_const _ _

end ARA
