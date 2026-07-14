/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Mathlib.Tactic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pivot-partition helpers

Shared list lemmas for pivot-partitioning algorithms (`Quicksort`,
`Quickselect`, …).

These lemmas are purely about lists and finite sums. Each is stated at
its weakest natural generality: plain `α` for pure list-structure
facts, `PartialOrder α` where only antisymmetry/transitivity of `≤` is
used, and `LinearOrder α` where totality (`¬ x < p ↔ p ≤ x`) or
trichotomy is genuinely needed.
-/

namespace ARA

open List

variable {α : Type*}

/-! ### Pure list structure (no order) -/

/-- `eraseIdx` gives back a permutation. -/
lemma perm_getElem_cons_eraseIdx
    (L : List α) (i : Fin L.length) :
    L.Perm (L[i] :: L.eraseIdx i) := by
  induction' i with i ih
  induction' L with hd tl ih generalizing i
  · aesop
  · rcases i with (_ | i) <;>
      simp_all +decide [List.eraseIdx]
    exact List.Perm.trans
      (List.Perm.cons _
        (ih _ <| by simpa using
          ‹i + 1 < List.length (hd :: tl)›))
      (List.Perm.swap ..)

/-! ### Sortedness (antisymmetry and transitivity) -/

section PartialOrder

variable [PartialOrder α]

/-- Two sorted permutations of each other are equal. -/
lemma eq_of_sortedLE_perm
    {l1 l2 : List α}
    (h1 : l1.SortedLE) (h2 : l2.SortedLE)
    (hp : l1.Perm l2) : l1 = l2 :=
  hp.eq_of_pairwise
    (fun _ _ _ _ hab hba =>
      le_antisymm hab hba)
    (sortedLE_iff_pairwise.mp h1)
    (sortedLE_iff_pairwise.mp h2)

/-- Concatenation `S1 ++ [p] ++ S2` is sorted when
`∀ x ∈ S1, x < p` and `∀ x ∈ S2, p ≤ x` and both
sublists are sorted. -/
lemma sorted_concat_pivot
    {S1 S2 : List α} {p : α}
    (h1 : S1.SortedLE) (h2 : S2.SortedLE)
    (hb1 : ∀ x ∈ S1, x < p)
    (hb2 : ∀ x ∈ S2, p ≤ x) :
    (S1 ++ [p] ++ S2).SortedLE := by
  rw [sortedLE_iff_pairwise]
  apply pairwise_append.mpr
  refine ⟨?_, sortedLE_iff_pairwise.mp h2,
    fun x hx y hy => ?_⟩
  · apply pairwise_append.mpr
    refine ⟨sortedLE_iff_pairwise.mp h1, pairwise_singleton _ _,
      fun x hx y hy => ?_⟩
    rw [mem_singleton.mp hy]
    exact (hb1 x hx).le
  · rcases mem_append.mp hx with hx1 | hxp
    · exact le_trans (hb1 x hx1).le (hb2 y hy)
    · rw [mem_singleton.mp hxp]; exact hb2 y hy

end PartialOrder

/-! ### Pivot partition (totality) -/

section LinearOrder

variable [LinearOrder α]

/-- Filtering a list by `(· < p)` and `(· ≥ p)` gives complementary
sub-lists. -/
lemma length_filter_lt_ge (l : List α) (p : α) :
    (l.filter (· < p)).length + (l.filter (· ≥ p)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : hd < p
    · rw [List.filter_cons_of_pos (by simpa using h),
        List.filter_cons_of_neg (by simpa using not_le.mpr h)]
      show (tl.filter (· < p)).length + 1 +
        (tl.filter (· ≥ p)).length = tl.length + 1
      omega
    · rw [List.filter_cons_of_neg (by simpa using h),
        List.filter_cons_of_pos (by simpa using not_lt.mp h)]
      show (tl.filter (· < p)).length +
        ((tl.filter (· ≥ p)).length + 1) = tl.length + 1
      omega

/-- Filter-partition around a pivot permutes the
original list. -/
lemma perm_filter_partition
    (L : List α) (i : Fin L.length) :
    ((L.eraseIdx i).filter
        (fun x => decide (x < L[i])) ++
      [L[i]] ++
      (L.eraseIdx i).filter
        (fun x => decide (x ≥ L[i]))).Perm L := by
  have hc :
    (L.eraseIdx i).filter
      (fun x => !(decide (x < L[i]))) =
    (L.eraseIdx i).filter
      (fun x => decide (x ≥ L[i])) := by
    apply List.filter_congr
    intro x _
    by_cases h : x < L[i.val]
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  have hf := filter_append_perm
    (fun x => decide (x < L[i])) (L.eraseIdx i)
  rw [hc] at hf
  have hmid :
    ((L.eraseIdx i).filter
        (fun x => decide (x < L[i])) ++
      [L[i]] ++
      (L.eraseIdx i).filter
        (fun x => decide (x ≥ L[i]))).Perm
    (L[i] ::
      ((L.eraseIdx i).filter
          (fun x => decide (x < L[i])) ++
        (L.eraseIdx i).filter
          (fun x =>
            decide (x ≥ L[i])))) := by
    simp only [append_assoc]
    exact perm_middle
  exact hmid.trans
    ((Perm.cons _ hf).trans
      (perm_getElem_cons_eraseIdx L i).symm)

/-!
### Partition size lemma for distinct lists

When the list `L` has no duplicates, the rank function
`i ↦ |{j ≠ i : L[j] < L[i]}|` is a bijection on `Fin L.length`.
This lets us reindex any sum over pivot choices by rank.

The proof uses `Finset.sum_equiv` with an equivalence constructed
from the injective rank function on a finite type.
-/

/-- The rank of element `i` in a nodup list: number of elements
strictly less than `L[i]`, excluding position `i`. -/
private noncomputable def rank (L : List α) (i : Fin L.length) : Fin L.length :=
  ⟨((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card,
   by
    calc ((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card
        ≤ (Finset.univ.erase i).card := Finset.card_filter_le _ _
      _ = L.length - 1 := by simp [Finset.card_erase_of_mem]
      _ < L.length := Nat.sub_lt (Fin.pos i) Nat.one_pos⟩

/-- The rank function equals the filter-length on the erased list. -/
private lemma rank_eq_filter_length (L : List α) (hnd : L.Nodup) (i : Fin L.length) :
    ((L.eraseIdx i).filter (· < L[i])).length = (rank L i).val := by
  unfold rank
  have h_filter_eq :
    List.toFinset
      (List.filter (fun x => x < L[i])
        (L.eraseIdx i)) =
    Finset.image (fun x => L[x])
      (Finset.filter (fun x => L[x] < L[i])
        (Finset.univ.erase i)) := by
    ext; simp [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨k, hk⟩ :=
        List.mem_iff_get.mp h.1
      use ⟨if k.val < i.val then k.val
           else k.val + 1, by grind⟩
      generalize_proofs at *; grind
    · rintro ⟨j, ⟨hj₁, hj₂⟩, rfl⟩
      rw [List.mem_iff_get]
      simp_all +decide [Fin.ext_iff]
      use ⟨if j.val < i.val then j.val
           else j.val - 1, by grind⟩
      generalize_proofs at *; grind
  rw [← List.toFinset_card_of_nodup]
  · rw [h_filter_eq,
      Finset.card_image_of_injective _
        (fun x y hxy => by
          simpa [Fin.ext_iff] using
            List.nodup_iff_injective_get.mp
              hnd hxy)]
  · exact List.Nodup.filter _
      (hnd.eraseIdx _)

/-- The complement rank equals `L.length - 1 - rank`. -/
private lemma complement_rank_eq (L : List α) (hnd : L.Nodup) (i : Fin L.length) :
    ((L.eraseIdx i).filter (· ≥ L[i])).length =
      L.length - 1 - (rank L i).val := by
  have h_split :
    ((L.eraseIdx i).filter (· < L[i])).length +
      ((L.eraseIdx i).filter (· ≥ L[i])).length =
      L.length - 1 := by
    rw [length_filter_lt_ge (L.eraseIdx i) L[i]]
    simp +decide [List.length_eraseIdx]
  exact eq_tsub_of_add_eq
    (by linarith [rank_eq_filter_length L hnd i])

/-- The rank function is injective on nodup lists. -/
private lemma rank_injective (L : List α) (hnd : L.Nodup) :
    Function.Injective (rank L) := by
  intro i j hij
  by_cases h1 : L[i] < L[j]
  · -- L[i] < L[j]: rank i ⊂ rank j, contradiction
    have h_subset : Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i) ⊂
        Finset.filter (fun x => L[x] < L[j]) (Finset.univ.erase j) := by
      constructor
      · grind
      · simp_all +decide [Finset.subset_iff]
        exact ⟨i, by aesop⟩
    have := Finset.card_lt_card h_subset
    simp_all +decide [rank]
  · by_cases h2 : L[j] < L[i]
    · -- L[j] < L[i]: rank j ⊂ rank i, contradiction
      have h_subset : Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i) ⊇
          Finset.image id (Finset.filter (fun x => L[x] < L[j]) (Finset.univ.erase j)) ∪ {j} := by
        grind
      have := Finset.card_mono h_subset
      simp_all +decide
      simp [rank, Fin.ext_iff] at hij; omega
    · -- L[i] = L[j]: use nodup injectivity
      exact List.nodup_iff_injective_get.mp hnd <|
        le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

/-- The rank function as an equivalence on `Fin L.length` for nodup lists. -/
private noncomputable def rankEquiv (L : List α) (hnd : L.Nodup) : Fin L.length ≃ Fin L.length :=
  Equiv.ofBijective (rank L) (Finite.injective_iff_bijective.mp (rank_injective L hnd))

/-- Reindexing partition sizes by rank for nodup lists, general form:
any function of the two partition sizes can be re-summed over ranks.
Works in any `AddCommMonoid` (used with `ℚ` for Quicksort's exact
formula and with `ℝ≥0∞` for Quickselect's bound).

Uses `Finset.sum_equiv` with the rank equivalence for a clean
bijective reindexing. -/
lemma nodup_partition_sum₂ {β : Type*} [AddCommMonoid β]
    (L : List α) (hnd : L.Nodup) (f : ℕ → ℕ → β) :
    (∑ i : Fin L.length,
      f ((L.eraseIdx i).filter
          (· < L[i])).length
        ((L.eraseIdx i).filter
          (· ≥ L[i])).length) =
    ∑ k : Fin L.length,
      f k.val (L.length - 1 - k.val) := by
  -- Rewrite LHS summand in terms of rank, then reindex
  have h_eq : ∀ i : Fin L.length,
      f ((L.eraseIdx i).filter (· < L[i])).length
        ((L.eraseIdx i).filter (· ≥ L[i])).length =
      f (rank L i).val (L.length - 1 - (rank L i).val) := by
    intro i; rw [rank_eq_filter_length L hnd i, complement_rank_eq L hnd i]
  simp_rw [h_eq]
  exact Finset.sum_equiv (rankEquiv L hnd)
    (fun _ => by simp)
    (fun _ _ => rfl)

/-- Reindexing partition sizes by rank for nodup lists (additive form
used by Quicksort's exact-cost recurrence). -/
lemma nodup_partition_sum
    (L : List α) (hnd : L.Nodup) (f : ℕ → ℚ) :
    (∑ i : Fin L.length,
      (f ((L.eraseIdx i).filter
          (· < L[i])).length +
       f ((L.eraseIdx i).filter
          (· ≥ L[i])).length)) =
    ∑ k : Fin L.length,
      (f k.val +
        f (L.length - 1 - k.val)) :=
  nodup_partition_sum₂ L hnd fun a b => f a + f b

end LinearOrder

end ARA
