/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.ExpectedCost
import ARA.Algorithms.Partition
import Mathlib.Data.List.GetD

/-!
# Quickselect

This module implements a modular version of Quickselect.

## Architecture

Like `Quicksort`, a single definition parameterized by `RandMonad`
and `MonadCost` serves as executable program (`M = IO`), as
specification (`M = PMF`), and as timed algorithm (`M = TimeMT ℕ M'`).

## Main results

* `Correctness_Quickselect` — over any `LawfulRandMonad`, the output
  distribution is the Dirac mass at the true order statistic
  `orderStat L k`; the answer never depends on the random pivots.
  No hypotheses on `L` or `k` are required.
* `Expected_Complexity_Quickselect` — with one tick per pivot
  comparison, the expected cost on a list of `n` distinct elements is
  at most `4 n`: a **linear** bound, in contrast to QuickSort's
  `Θ(n log n)`. (For lists with duplicates the `≥`-side recursion can
  degrade; distinctness is the classical hypothesis.)

The cost analysis is carried out entirely in `ℝ≥0∞` via `𝔼_runtime[·]`,
so no summability or `toReal` bookkeeping is needed.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List

variable {α : Type} [LinearOrder α] [Inhabited α]

/-! ## Specification -/

/-- The `k`-th order statistic of `L` (0-indexed): the `k`-th element
of the sorted list, with `default` as out-of-range default. This is the
specification `Quickselect` must meet. -/
def orderStat (L : List α) (k : ℕ) : α := (L.mergeSort (· ≤ ·)).getD k default

/-! ## Algorithm -/

/-- Randomized Quickselect, polymorphic in the random monad `M` and
the cost monad `MonadCost ℕ M`. Partition around a uniformly random
pivot, then recurse into the (strictly smaller) side containing rank
`k`, or stop if the pivot itself has rank `k`. -/
def Quickselect
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → ℕ → M α
  | [], _ => return default
  | L@(_ :: _), k => do
      let idx ← randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let lt := rest.filter (· < pivot)
      MonadCost.tick rest.length
      if k < lt.length then
        Quickselect lt k
      else if k = lt.length then
        return pivot
      else
        Quickselect (rest.filter (· ≥ pivot)) (k - lt.length - 1)
  termination_by L _ => L.length
  decreasing_by all_goals grind

-- IO version (executable, untimed)
def Quickselect_IO : List ℕ → ℕ → IO ℕ := Quickselect

#eval Quickselect_IO [5, 3, 8, 1, 9, 2] 2

-- PMF version (noncomputable specification)
noncomputable def Quickselect_PMF : List ℕ → ℕ → PMF ℕ := Quickselect

-- IO timed version (executable)
def Quickselect_IO_Timed : List ℕ → ℕ → TimeMT ℕ IO ℕ := Quickselect

#eval (Quickselect_IO_Timed [5, 3, 8, 1, 9, 2] 2).run

/-!
## The pivot branch

As for QuickSort, we abstract the deterministic partition-and-recurse
step at a fixed pivot index; the algorithm is `randIdx >>= branch`.
-/

/-- Branch: partition around pivot `L[i]` and recurse into the side
containing rank `k` (or stop). Used for both correctness and
complexity proofs. -/
private noncomputable abbrev qsel_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List α) (k : ℕ) (i : Fin L.length) : M α := do
  let pivot := L[i]
  let rest := L.eraseIdx i
  let lt := rest.filter (· < pivot)
  MonadCost.tick rest.length
  if k < lt.length then
    Quickselect lt k
  else if k = lt.length then
    return pivot
  else
    Quickselect (rest.filter (· ≥ pivot)) (k - lt.length - 1)

/-- `Quickselect` on a nonempty list decomposes as
`randIdx L >>= qsel_branch M L k`. -/
private lemma quickselect_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : α) (tail : List α) (k : ℕ) :
    (Quickselect (head :: tail) k : M α) =
    randIdx (head :: tail) (by grind) >>=
      fun idx => qsel_branch M (head :: tail) k idx := by
  rw [Quickselect.eq_2]

/-- Timed decomposition: in `TimeMT ℕ M`, `Quickselect` decomposes as
`TimeMT.lift (randIdx ...) >>= qsel_branch`. -/
private lemma quickselect_timed_eq_bind
    {M} [Monad M] [RandMonad M]
    (head : α) (tail : List α) (k : ℕ) :
    (Quickselect (head :: tail) k : TimeMT ℕ M α) =
    TimeMT.lift (randIdx (head :: tail) : M _) >>=
      fun idx => qsel_branch (TimeMT ℕ M) (head :: tail) k idx := by
  rw [Quickselect.eq_2 (M := TimeMT ℕ M)]
  rfl

/-!
## Correctness

The sorted version of `L` splits around any pivot as
`sorted(< pivot) ++ [pivot] ++ sorted(≥ pivot)`, so the order statistic
of `L` reduces to the order statistic of one side. All three case
lemmas below are hypothesis-free consequences of this identity
(out-of-range ranks yield the default `0` on both sides).
-/

omit [Inhabited α] in
/-- The sorted list splits around any pivot. Reuses
`sorted_concat_pivot` and `perm_filter_partition` from
`ARA.Algorithms.Partition`. -/
private lemma mergeSort_partition (L : List α) (i : Fin L.length) :
    L.mergeSort (· ≤ ·) =
      ((L.eraseIdx i).filter (· < L[i])).mergeSort (· ≤ ·) ++ [L[i]] ++
        ((L.eraseIdx i).filter (· ≥ L[i])).mergeSort (· ≤ ·) := by
  apply eq_of_sortedLE_perm sortedLE_mergeSort
  · apply sorted_concat_pivot sortedLE_mergeSort sortedLE_mergeSort
    · intro x hx
      rw [mem_mergeSort] at hx
      simpa using of_mem_filter hx
    · intro x hx
      rw [mem_mergeSort] at hx
      simpa using of_mem_filter hx
  · exact (mergeSort_perm L _).trans
      ((perm_filter_partition L i).symm.trans
        ((((mergeSort_perm _ _).symm.append (Perm.refl [L[i]])).append
          (mergeSort_perm _ _).symm)))

/-- Rank `k` falls in the `< pivot` side. -/
private lemma orderStat_lt_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : k < ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat L k = orderStat ((L.eraseIdx i).filter (· < L[i])) k := by
  unfold orderStat
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append _ _ _ _ (by simpa using hk)]

/-- Rank `k` is exactly the pivot's rank. -/
private lemma orderStat_eq_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : k = ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat L k = L[i] := by
  unfold orderStat
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp [hk])]
  simp [hk]

/-- Rank `k` falls in the `≥ pivot` side. -/
private lemma orderStat_gt_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : ((L.eraseIdx i).filter (· < L[i])).length < k) :
    orderStat L k =
      orderStat ((L.eraseIdx i).filter (· ≥ L[i]))
        (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) := by
  unfold orderStat
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp only [List.length_mergeSort]; omega)]
  rw [List.singleton_append]
  have hidx : k - ((((L.eraseIdx i).filter (· < L[i])).mergeSort (· ≤ ·))).length =
      (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) + 1 := by
    simp only [List.length_mergeSort]; omega
  rw [hidx, List.getD_cons_succ]

/-- **Correctness.** For any `LawfulRandMonad`, `Quickselect L k`
(with no-op cost tracking) returns exactly the `k`-th order statistic:
its output distribution is the Dirac mass at `orderStat L k`,
independently of the random pivot choices. -/
theorem Correctness_Quickselect
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    LawfulRandMonad.toPMF
      (@Quickselect _ _ _ M _ _ instMonadCostDefault L k) =
      PMF.pure (orderStat L k) := by
  induction' n : L.length using Nat.strong_induction_on with n ih generalizing L k
  rcases L with (_ | ⟨head, tail⟩)
  · rw [Quickselect.eq_1]
    simp only [LawfulRandMonad.toPMF_pure]
    have h0 : orderStat ([] : List α) k = default := by simp [orderStat]
    rw [h0]
    rfl
  · -- Each pivot branch produces the same Dirac output.
    have h_step : ∀ i : Fin (head :: tail).length,
        LawfulRandMonad.toPMF
          (@qsel_branch _ _ _ M _ _ instMonadCostDefault (head :: tail) k i) =
          PMF.pure (orderStat (head :: tail) k) := by
      intro i
      unfold qsel_branch
      simp only [MonadCost.tick_default, pure_bind]
      split_ifs with h1 h2
      · rw [ih _ (by grind) _ k rfl, orderStat_lt_branch _ i h1]
      · rw [orderStat_eq_branch _ i h2]
        exact LawfulRandMonad.toPMF_pure _
      · rw [ih _ (by grind) _ _ rfl, orderStat_gt_branch _ i (by omega)]
    have hne : Nonempty (Fin (head :: tail).length) := ⟨⟨0, by grind⟩⟩
    calc LawfulRandMonad.toPMF
          (@Quickselect _ _ _ M _ _ instMonadCostDefault (head :: tail) k)
        = LawfulRandMonad.toPMF
            (randIdx (head :: tail) (by grind) >>=
              fun idx =>
                @qsel_branch _ _ _ M _ _ instMonadCostDefault (head :: tail) k idx) := by
          rw [quickselect_eq_bind]
      _ = (PMF.uniformOfFintype (Fin (head :: tail).length)).bind
            (fun idx =>
              LawfulRandMonad.toPMF
                (@qsel_branch _ _ _ M _ _ instMonadCostDefault (head :: tail) k idx)) := by
          rw [LawfulRandMonad.toPMF_bind, LawfulRandMonad.toPMF_randIdx]
          rfl
      _ = (PMF.uniformOfFintype (Fin (head :: tail).length)).bind
            (fun _ => PMF.pure (orderStat (head :: tail) k)) := by
          congr 1; funext i; exact h_step i
      _ = PMF.pure (orderStat (head :: tail) k) := PMF.bind_const _ _

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem quickselect_correct (L : List α) (k : ℕ) :
    (Quickselect L k : PMF α) = PMF.pure (orderStat L k) :=
  Correctness_Quickselect (M := PMF) L k

/-!
## Complexity

The expected cost obeys
`E[n] = (n-1) + (1/n) Σ_i E[side_i]`, and recursing always into a side
of size at most `max(r, n-1-r)` (for pivot rank `r`) gives the linear
bound `E[n] ≤ 4n`. Everything is stated in `ℝ≥0∞`.
-/

/-- The expected cost of `qsel_branch` in `TimeMT` is the tick cost
plus the expected cost of the branch actually taken. -/
private lemma expected_cost_qsel_branch
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (i : Fin L.length) :
    𝔼_runtime[qsel_branch (TimeMT ℕ M) L k i] =
    ((L.eraseIdx i).length : ENNReal) +
      (if k < ((L.eraseIdx i).filter (· < L[i])).length then
        𝔼_runtime[(Quickselect ((L.eraseIdx i).filter (· < L[i])) k :
          TimeMT ℕ M α)]
      else if k = ((L.eraseIdx i).filter (· < L[i])).length then 0
      else
        𝔼_runtime[(Quickselect ((L.eraseIdx i).filter (· ≥ L[i]))
          (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) :
          TimeMT ℕ M α)]) := by
  show expected_cost (inst.toPMF
    ((TimeMT.tick (L.eraseIdx i).length >>= fun _ =>
      if k < ((L.eraseIdx i).filter (· < L[i])).length then
        (Quickselect ((L.eraseIdx i).filter (· < L[i])) k : TimeMT ℕ M α)
      else if k = ((L.eraseIdx i).filter (· < L[i])).length then
        pure L[i]
      else
        Quickselect ((L.eraseIdx i).filter (· ≥ L[i]))
          (k - ((L.eraseIdx i).filter (· < L[i])).length - 1)).run)) = _
  cost_step
  congr 1
  split_ifs
  · rfl
  · exact expected_cost_toPMF_pure _
  · rfl

/-- The expected cost of `Quickselect` on a nonempty list is the
uniform average of the branch costs. -/
private lemma expected_cost_quickselect_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : α) (tail : List α) (k : ℕ) :
    let L := head :: tail
    𝔼_runtime[(Quickselect L k : TimeMT ℕ M α)] =
    (L.length : ENNReal)⁻¹ *
      ∑ i : Fin L.length,
        (((L.eraseIdx i).length : ENNReal) +
          (if k < ((L.eraseIdx i).filter (· < L[i])).length then
            𝔼_runtime[(Quickselect ((L.eraseIdx i).filter (· < L[i])) k :
              TimeMT ℕ M α)]
          else if k = ((L.eraseIdx i).filter (· < L[i])).length then 0
          else
            𝔼_runtime[(Quickselect ((L.eraseIdx i).filter (· ≥ L[i]))
              (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) :
              TimeMT ℕ M α)])) := by
  intro L
  rw [quickselect_timed_eq_bind head tail k]
  show expected_cost (inst.toPMF
    (TimeMT.lift (randIdx (head :: tail) : M _) >>=
      fun idx => qsel_branch (TimeMT ℕ M) (head :: tail) k idx).run) = _
  cost_step
  rw [inst.toPMF_randIdx]
  have hne : Nonempty (Fin L.length) := ⟨⟨0, by grind⟩⟩
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [Finset.mul_sum]
  congr 1; ext i; congr 1
  exact expected_cost_qsel_branch L k i

/-- Arithmetic core of the linear bound:
`4 · Σ_{r<n} max(r, n-1-r) ≤ 3 n²`. -/
private lemma sum_max_le : ∀ n : ℕ,
    4 * ∑ r ∈ Finset.range n, max r (n - 1 - r) ≤ 3 * n ^ 2
  | 0 => by simp
  | 1 => by simp
  | (m + 2) => by
      have hrec : ∑ r ∈ Finset.range (m + 2), max r (m + 1 - r) =
          (∑ r ∈ Finset.range m, max r (m - 1 - r)) + (3 * m + 2) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have h1 : ∀ r ∈ Finset.range m,
            max (r + 1) (m + 1 - (r + 1)) = max r (m - 1 - r) + 1 := by
          intro r hr
          have := Finset.mem_range.mp hr
          omega
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
        omega
      have ih := sum_max_le m
      have hsq : (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
      show 4 * ∑ r ∈ Finset.range (m + 2), max r (m + 1 - r) ≤ 3 * (m + 2) ^ 2
      omega

set_option maxHeartbeats 400000 in
/-- **Expected complexity of Quickselect.** With one tick per pivot
comparison, selecting from a list of `n` **distinct** elements costs
at most `4 n` comparisons in expectation — a linear bound, unlike
QuickSort's `Θ(n log n)`. -/
theorem Expected_Complexity_Quickselect
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    𝔼_runtime[(Quickselect L k : TimeMT ℕ M α)] ≤
      4 * (L.length : ENNReal) := by
  induction' n : L.length using Nat.strong_induction_on with n ih generalizing L k
  rcases L with (_ | ⟨head, tail⟩)
  · rw [Quickselect.eq_1]
    rw [expected_cost_toPMF_pure]
    exact bot_le
  · subst n
    rw [expected_cost_quickselect_step head tail k]
    -- Bound each branch by `tail.length + 4·max(|lt|, |ge|)` using the IH.
    have hbound : ∀ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          (if k < (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length then
            𝔼_runtime[(Quickselect
              (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) k :
              TimeMT ℕ M α)]
          else if k = (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length then 0
          else
            𝔼_runtime[(Quickselect
              (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i]))
              (k - (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length - 1) :
              TimeMT ℕ M α)])) ≤
        ((tail.length : ENNReal) +
          4 * ((max
            ((((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length)
            ((((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])).length) : ℕ) :
            ENNReal)) := by
      intro i
      have hrest : (((head :: tail).eraseIdx i).length : ENNReal) =
          (tail.length : ENNReal) := by
        have hi := i.isLt
        simp only [List.length_cons] at hi
        simp [List.length_eraseIdx, Nat.lt_succ_iff.mp hi]
      refine add_le_add (le_of_eq hrest) ?_
      have hnd' : (((head :: tail).eraseIdx i)).Nodup := hnd.eraseIdx _
      split_ifs with h1 h2
      · refine le_trans (ih _ (by grind) _ k (hnd'.filter _) rfl) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_left _ _))
      · exact bot_le
      · refine le_trans (ih _ (by grind) _ _ (hnd'.filter _) rfl) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_right _ _))
    -- Reindex the per-pivot bound by rank (nodup), then close numerically.
    have hsum : (∑ i : Fin (head :: tail).length,
        ((tail.length : ENNReal) +
          4 * ((max
            ((((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length)
            ((((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])).length) : ℕ) :
            ENNReal))) =
        ∑ r : Fin (head :: tail).length,
          ((tail.length : ENNReal) +
            4 * ((max r.val ((head :: tail).length - 1 - r.val) : ℕ) : ENNReal)) :=
      nodup_partition_sum₂ (head :: tail) hnd
        (fun a b => (tail.length : ENNReal) + 4 * ((max a b : ℕ) : ENNReal))
    -- ℕ-level bound for the reindexed sum.
    have hkey : (∑ r ∈ Finset.range (tail.length + 1),
        (tail.length + 4 * max r (tail.length - r))) ≤
        4 * (tail.length + 1) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h4 := sum_max_le (tail.length + 1)
      simp only [Nat.add_sub_cancel] at h4
      have hsq : (tail.length + 1) ^ 2 = tail.length ^ 2 + 2 * tail.length + 1 := by
        ring
      have hd : (tail.length + 1) * tail.length = tail.length ^ 2 + tail.length := by
        ring
      omega
    have probe : ((head :: tail).length : ENNReal)⁻¹ *
          ∑ i : Fin (head :: tail).length,
            (((((head :: tail).eraseIdx i)).length : ENNReal) +
              (if k < (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length then
                𝔼_runtime[(Quickselect
                  (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) k :
                  TimeMT ℕ M α)]
              else if k = (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length
                then 0
              else
                𝔼_runtime[(Quickselect
                  (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i]))
                  (k - (((head :: tail).eraseIdx i).filter
                    (· < (head :: tail)[i])).length - 1) :
                  TimeMT ℕ M α)]))
        ≤ 4 * ((head :: tail).length : ENNReal) := by
      have hsum_le :
              ∑ i : Fin (head :: tail).length,
                (((((head :: tail).eraseIdx i)).length : ENNReal) +
                  (if k < (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length then
                    𝔼_runtime[(Quickselect
                      (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) k :
                      TimeMT ℕ M α)]
                  else if k = (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length
                    then 0
                  else
                    𝔼_runtime[(Quickselect
                      (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i]))
                      (k - (((head :: tail).eraseIdx i).filter
                        (· < (head :: tail)[i])).length - 1) :
                      TimeMT ℕ M α)]))
            ≤ ((4 * (tail.length + 1) ^ 2 : ℕ) : ENNReal) := by
        refine le_trans (Finset.sum_le_sum fun i _ => hbound i) ?_
        rw [hsum, Fin.sum_univ_eq_sum_range
          (fun r => (tail.length : ENNReal) +
            4 * ((max r ((head :: tail).length - 1 - r) : ℕ) : ENNReal))]
        simp only [List.length_cons, Nat.add_sub_cancel]
        refine le_trans (le_of_eq ?_) (Nat.cast_le.mpr hkey)
        push_cast
        rfl
      have hfin : ((head :: tail).length : ENNReal)⁻¹ *
          ((4 * (tail.length + 1) ^ 2 : ℕ) : ENNReal) ≤
          4 * ((head :: tail).length : ENNReal) := by
        have hne0 : ((tail.length : ENNReal) + 1) ≠ 0 := by positivity
        have hnetop : ((tail.length : ENNReal) + 1) ≠ ⊤ := by finiteness
        simp only [List.length_cons]
        push_cast
        rw [show ((tail.length : ENNReal) + 1)⁻¹ *
              (4 * ((tail.length : ENNReal) + 1) ^ 2) =
            4 * (((tail.length : ENNReal) + 1) *
              (((tail.length : ENNReal) + 1)⁻¹ * ((tail.length : ENNReal) + 1)))
          from by ring]
        rw [ENNReal.inv_mul_cancel hne0 hnetop, mul_one]
      exact le_trans (mul_le_mul' le_rfl hsum_le) hfin
    exact probe

/-!
## Named corollaries at `M = PMF`
-/

/-- Expected number of comparisons performed by `Quickselect L k`:
the expected runtime of the instrumented algorithm interpreted in
`PMF`, one tick per pivot comparison. -/
noncomputable def expectedComparisons (L : List α) (k : ℕ) : ENNReal :=
  𝔼_runtime[(Quickselect L k : TimeMT ℕ PMF α)]

/-- **Expected cost is linear.** Selecting from a list of `n` distinct
elements takes at most `4 n` comparisons in expectation. -/
theorem quickselect_expected_cost_linear
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    expectedComparisons L k ≤ 4 * (L.length : ENNReal) :=
  Expected_Complexity_Quickselect L k hnd

end ARA
