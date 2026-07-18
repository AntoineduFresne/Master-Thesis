/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.ExpectedCost
import ARA.Infrastructure.Correctness
import ARA.Helpers.Partition
import Mathlib.Data.List.GetD
import Mathlib.NumberTheory.Harmonic.Defs

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
* `Quickselect_Cost_Upper_Bound` — for arbitrary lists (possibly
  with duplicates) and any rank, the expected cost is at most `C(n,2)`,
  tight on all-equal inputs.
* `Expected_Complexity_Quickselect` — with one tick per pivot
  comparison, the expected cost on a list of `n` distinct elements
  is at most `4 n`: a linear bound, in contrast to QuickSort's
  `Θ(n log n)`.
* `Expected_Complexity_Quickselect_exact` — Knuth's (1971) exact
  expected cost of selecting rank `k` (0-indexed) from `n` distinct
  elements: `2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))`
  comparisons.
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

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed; `RandMonad IO` comes from
-- `ARA.Infrastructure.LawfulRandMonad`)
def Quickselect_IO : List ℕ → ℕ → IO ℕ := Quickselect

#eval Quickselect_IO [5, 3, 8, 1, 9, 2] 2

-- PMF version (noncomputable specification)
noncomputable def Quickselect_PMF : List ℕ → ℕ → PMF ℕ := Quickselect

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable; `RandMonad (TimeMT ℕ M)` comes from
-- `ARA.Infrastructure.ExpectedCost`)
def Quickselect_IO_Timed : List ℕ → ℕ → TimeMT ℕ IO ℕ := Quickselect

#eval (Quickselect_IO_Timed [5, 3, 8, 1, 9, 2] 2).run

-- PMF timed version (noncomputable specification)
noncomputable def Quickselect_PMF_Timed :
    List ℕ → ℕ → TimeMT ℕ PMF ℕ := Quickselect

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-!
### Abbreviations

As for `Quicksort`, we abstract the deterministic partition-and-recurse
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


-- ### Structural decomposition

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
### Order-statistic case lemmas

By `mergeSort_partition` (from `ARA.Helpers.Partition`), the sorted
version of `L` splits around any pivot as
`sorted(< pivot) ++ [pivot] ++ sorted(≥ pivot)`, so the order statistic
of `L` reduces to the order statistic of one side. All three case
lemmas are hypothesis-free (out-of-range ranks yield `default` on both
sides).
-/

/-- Rank `k` falls in the `< pivot` side: the order statistic is found
left of the pivot. -/
@[spec_transport]
private lemma orderStat_lt_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : k < ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat L k = orderStat ((L.eraseIdx i).filter (· < L[i])) k := by
  unfold orderStat
  -- Index `k` lands inside the first block of the split sorted list.
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append _ _ _ _ (by simpa using hk)]

/-- Rank `k` is exactly the pivot's rank: the order statistic is the
pivot itself. -/
@[spec_transport]
private lemma orderStat_eq_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : k = ((L.eraseIdx i).filter (· < L[i])).length) :
    orderStat L k = L[i] := by
  unfold orderStat
  -- Index `k` lands exactly on the singleton `[pivot]` block.
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp [hk])]
  simp [hk]

/-- Rank `k` falls in the `≥ pivot` side: shift the rank past the left
block and the pivot. Also covers out-of-range ranks (both sides yield
`default`). -/
@[spec_transport]
private lemma orderStat_gt_branch (L : List α) (i : Fin L.length) {k : ℕ}
    (hk : ((L.eraseIdx i).filter (· < L[i])).length < k) :
    orderStat L k =
      orderStat ((L.eraseIdx i).filter (· ≥ L[i]))
        (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) := by
  unfold orderStat
  -- Index `k` lands in the last block; subtract the first block's length…
  rw [mergeSort_partition L i, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp only [List.length_mergeSort]; omega)]
  rw [List.singleton_append]
  -- …and one more for the pivot.
  have hidx : k - ((((L.eraseIdx i).filter (· < L[i])).mergeSort (· ≤ ·))).length =
      (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) + 1 := by
    simp only [List.length_mergeSort]; omega
  rw [hidx, List.getD_cons_succ]

/-!
### Generic correctness theorem

For the correctness proof, we work with the no-op `MonadCost`
instance (`instMonadCostDefault`), whose `tick` is definitionally
`pure ()` (`MonadCost.tick_default`) — so cost tracking is invisible
to the output distribution.
-/

/-- For any `LawfulRandMonad`, `Quickselect L k`
returns exactly the `k`-th order statistic:
its output distribution is the Dirac mass at `orderStat L k`,
independently of the random pivot choices.
-/
theorem Correctness_Quickselect
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    LawfulRandMonad.toPMF
      (@Quickselect _ _ _ M _ _ instMonadCostDefault L k) =
      PMF.pure (orderStat L k) := by
  induction L, k using Quickselect.induct with
  | case1 k =>
    -- Base case: the empty list returns `default`, matching the
    -- out-of-range value of `orderStat`.
    rw [Quickselect.eq_1]
    simp only [LawfulRandMonad.toPMF_pure]
    rw [show orderStat ([] : List α) k = default from by simp [orderStat]]
    rfl
  | case2 head tail k ih1 ih2 =>
    -- Collapse the uniform pivot choice (`toPMF_randIdx_bind_dirac`):
    -- every branch produces the same Dirac mass at the order statistic.
    rw [quickselect_eq_bind]
    refine toPMF_randIdx_bind_dirac fun i => ?_
    unfold qsel_branch
    dirac_step
    split_ifs with h1 h2
    · -- `k` in the `<`-side: recurse (IH) and transport the order
      -- statistic with `orderStat_lt_branch`.
      rw [ih1 i, orderStat_lt_branch _ i h1]
    · -- `k` is the pivot's rank: the branch returns the pivot.
      rw [orderStat_eq_branch _ i h2]
      exact LawfulRandMonad.toPMF_pure _
    · -- `k` in the `≥`-side: recurse with the shifted rank.
      rw [ih2 i, orderStat_gt_branch _ i (by omega)]

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem quickselect_correct (L : List α) (k : ℕ) :
    (Quickselect L k : PMF α) = PMF.pure (orderStat L k) :=
  Correctness_Quickselect (M := PMF) L k

-- ----------------------------------------
-- Free Proof: Untimed Quickselect_PMF
-- ----------------------------------------

lemma Correctness_Quickselect_PMF (L : List ℕ) (k : ℕ) :
    Quickselect_PMF L k = pure (orderStat L k) :=
  quickselect_correct L k

-- ----------------------------------------
-- Free Proof: Timed Quickselect_PMF_Timed
-- ----------------------------------------

/-! ### TimeMT erasure for the unified Quickselect -/

/-- Erasing time from the timed Quickselect gives the untimed
Quickselect: the `MonadCost.tick` in `TimeMT` erases to `pure ()`,
matching the no-op `MonadCost` instance.
-/
lemma Quickselect_erasure
    {M} [Monad M] [LawfulMonad M] [RandMonad M]
    (L : List α) (k : ℕ) :
    TimeM.ret <$> (Quickselect L k : TimeMT ℕ M α).run =
      (Quickselect L k : M α) := by
  induction L, k using Quickselect.induct
  · -- Base case
    rw [Quickselect.eq_1 (M := TimeMT ℕ M), Quickselect.eq_1 (M := M)]
    simp
  · -- Inductive case
    next head tail k ih1 ih2 =>
    rw [Quickselect.eq_2 (M := TimeMT ℕ M), Quickselect.eq_2 (M := M)]
    simp only [TimeMT_erase_bind, TimeMT_randIdx_run, TimeMT_erase_lift,
      MonadCost.tick_timeMT, TimeMT_erase_tick, MonadCost.tick_default,
      pure_bind]
    -- The pivot choice is shared; compare the branches pointwise.
    refine bind_congr fun idx => ?_
    split_ifs with h1 h2
    · exact ih1 idx
    · simp
    · exact ih2 idx

/-- Timed PMF correctness for free. -/
lemma Correctness_Quickselect_Timed_PMF (L : List ℕ) (k : ℕ) :
    TimeM.ret <$> (Quickselect_PMF_Timed L k).run =
      pure (orderStat L k) := by
  unfold Quickselect_PMF_Timed
  rw [Quickselect_erasure]
  exact quickselect_correct L k

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
## Complexity

The expected cost obeys
`E[n] = (n-1) + (1/n) Σ_i E[side_i]`. Three results follow, all by
functional induction on `Quickselect`:

* bounding the recursion by the whole `rest` gives `E ≤ C(n,2)` for
  arbitrary lists (tight on all-equal inputs), which also yields
  finiteness of the expected cost;
* recursing always into a side of size at most `max(r, n-1-r)` (for
  pivot rank `r`) gives the linear bound `E ≤ 4n` for distinct lists;
* for distinct lists the recurrence solves exactly: rank reindexing
  turns the sum over pivots into Knuth's (1971) bivariate harmonic
  closed form (`Expected_Complexity_Quickselect_exact`).

The upper bounds are stated in `ℝ≥0∞`, where no summability
bookkeeping is needed; the exact formula descends to `ℝ` via `toReal`,
with finiteness supplied by the `C(n,2)` bound.
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
        𝔼_runtime[Quickselect ((L.eraseIdx i).filter (· < L[i])) k | M]
      else if k = ((L.eraseIdx i).filter (· < L[i])).length then 0
      else
        𝔼_runtime[Quickselect ((L.eraseIdx i).filter (· ≥ L[i]))
          (k - ((L.eraseIdx i).filter (· < L[i])).length - 1) | M]) := by
  show expected_cost (inst.toPMF
    ((TimeMT.tick (L.eraseIdx i).length >>= fun _ =>
      if k < ((L.eraseIdx i).filter (· < L[i])).length then
        (Quickselect ((L.eraseIdx i).filter (· < L[i])) k : TimeMT ℕ M α)
      else if k = ((L.eraseIdx i).filter (· < L[i])).length then
        pure L[i]
      else
        Quickselect ((L.eraseIdx i).filter (· ≥ L[i]))
          (k - ((L.eraseIdx i).filter (· < L[i])).length - 1)).run)) = _
  -- Peel the tick with the bridge lemmas, then the `pure` branch is free.
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
    𝔼_runtime[Quickselect (head :: tail) k | M] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          (if k < (pivotLT (head :: tail) i).length then
            𝔼_runtime[Quickselect (pivotLT (head :: tail) i) k | M]
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            𝔼_runtime[Quickselect (pivotGE (head :: tail) i)
              (k - (pivotLT (head :: tail) i).length - 1) | M])) := by
  rw [quickselect_timed_eq_bind head tail k, expected_cost_uniform_step]
  congr 1
  exact Finset.sum_congr rfl fun i _ => expected_cost_qsel_branch (head :: tail) k i

/-- The empty list costs nothing (for any rank). -/
lemma expected_cost_quickselect_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] (k : ℕ) :
    𝔼_runtime[Quickselect ([] : List α) k | M] = 0 := by
  rw [Quickselect.eq_1, expected_cost_toPMF_pure]

/-!
### The `C(n,2)` bound for arbitrary lists

The linear bound below needs distinct elements: on an all-equal list
the `≥`-side keeps every duplicate, so selecting rank `n-1` degenerates
to `T(n) = (n-1) + T(n-1) = C(n,2)`. That worst case is itself an upper
bound for every list and rank, by the same argument as for `Quicksort`.
Its `ℝ≥0∞` form also provides finiteness of the expected cost for free.
-/

/-- For an arbitrary list (possibly
with duplicates) and any rank `k`, the expected cost of `Quickselect`
is bounded by `L.length.choose 2`. Tight on all-equal inputs. -/
theorem Quickselect_Cost_Upper_Bound_ennreal
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼_runtime[Quickselect L k | M] ≤
      ((L.length.choose 2 : ℕ) : ENNReal) := by
  induction L, k using Quickselect.induct with
  | case1 k =>
    rw [expected_cost_quickselect_nil]
    exact bot_le
  | case2 head tail k ih1 ih2 =>
    rw [expected_cost_quickselect_step head tail k]
    -- Whichever branch is taken recurses on at most `tail.length`
    -- elements, so `C(·,2)`-monotonicity bounds it by `C(tail.length, 2)`.
    have hbound : ∀ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          (if k < (pivotLT (head :: tail) i).length then
            𝔼_runtime[Quickselect (pivotLT (head :: tail) i) k | M]
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            𝔼_runtime[Quickselect (pivotGE (head :: tail) i)
              (k - (pivotLT (head :: tail) i).length - 1) | M])) ≤
        ((tail.length : ENNReal) + ((tail.length.choose 2 : ℕ) : ENNReal)) := by
      intro i
      refine add_le_add (le_of_eq (by rw [length_eraseIdx_cons])) ?_
      split_ifs with h1 h2
      · exact le_trans (ih1 i) (Nat.cast_le.mpr (Nat.choose_le_choose 2 (by grind)))
      · exact bot_le
      · exact le_trans (ih2 i) (Nat.cast_le.mpr (Nat.choose_le_choose 2 (by grind)))
    -- Pascal: `C(n,2) = tail.length + C(tail.length, 2)`.
    have hpascal : (head :: tail).length.choose 2 =
        tail.length + tail.length.choose 2 := by
      simp only [List.length_cons]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    -- Average the `n` equal bounds.
    refine uniform_avg_le (by simp)
      (le_trans (Finset.sum_le_sum fun i _ => hbound i) ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hpascal]
    push_cast
    exact le_rfl

/-- For an arbitrary list (possibly with duplicates) and any rank, the
expected cost of `Quickselect` is at most `C(n,2)` comparisons.
Real-valued corollary of `Quickselect_Cost_Upper_Bound_ennreal`. -/
theorem Quickselect_Cost_Upper_Bound
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼ℝ_runtime[Quickselect L k | M] ≤ L.length.choose 2 := by
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _)
    (Quickselect_Cost_Upper_Bound_ennreal (M := M) L k)
  simpa using this

/-- Finiteness of the expected cost — a free corollary of the `C(n,2)`
bound, no separate induction needed. Feeds the `toReal` steps of the
exact-formula theorem below. -/
lemma expected_cost_quickselect_ne_top
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    𝔼_runtime[Quickselect L k | M] ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (Quickselect_Cost_Upper_Bound_ennreal L k)

/-!
### The linear bound for distinct lists
-/

/-- With one tick per pivot comparison, selecting from a list
of `n` **distinct** elements costs at most `4 n` comparisons
in expectation — a linear bound, unlike QuickSort's `Θ(n log n)`. -/
theorem Expected_Complexity_Quickselect
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    𝔼_runtime[Quickselect L k | M] ≤
      4 * (L.length : ENNReal) := by
  revert hnd
  induction L, k using Quickselect.induct with
  | case1 k =>
    intro _
    rw [expected_cost_quickselect_nil]
    exact bot_le
  | case2 head tail k ih1 ih2 =>
    intro hnd
    rw [expected_cost_quickselect_step head tail k]
    -- Bound each branch by `tail.length + 4·max(|lt|, |ge|)` using the IH:
    -- whichever side is recursed into has at most `max` elements.
    have hbound : ∀ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          (if k < (pivotLT (head :: tail) i).length then
            𝔼_runtime[Quickselect (pivotLT (head :: tail) i) k | M]
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            𝔼_runtime[Quickselect (pivotGE (head :: tail) i)
              (k - (pivotLT (head :: tail) i).length - 1) | M])) ≤
        ((tail.length : ENNReal) +
          4 * ((max
            ((pivotLT (head :: tail) i).length)
            ((pivotGE (head :: tail) i).length) : ℕ) :
            ENNReal)) := by
      intro i
      refine add_le_add (le_of_eq (by rw [length_eraseIdx_cons])) ?_
      have hnd' : (((head :: tail).eraseIdx i)).Nodup := hnd.eraseIdx _
      split_ifs with h1 h2
      · -- `<`-side: the IH gives `4·|lt|`, and `|lt| ≤ max`.
        refine le_trans (ih1 i (hnd'.filter _)) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_left _ _))
      · -- pivot hit: free.
        exact bot_le
      · -- `≥`-side: the IH gives `4·|ge|`, and `|ge| ≤ max`.
        refine le_trans (ih2 i (hnd'.filter _)) ?_
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr (le_max_right _ _))
    -- Reindex the per-pivot bound by rank (`nodup_partition_sum₂`).
    have hsum : (∑ i : Fin (head :: tail).length,
        ((tail.length : ENNReal) +
          4 * ((max
            ((pivotLT (head :: tail) i).length)
            ((pivotGE (head :: tail) i).length) : ℕ) :
            ENNReal))) =
        ∑ r : Fin (head :: tail).length,
          ((tail.length : ENNReal) +
            4 * ((max r.val ((head :: tail).length - 1 - r.val) : ℕ) : ENNReal)) :=
      nodup_partition_sum₂ (head :: tail) hnd
        (fun a b => (tail.length : ENNReal) + 4 * ((max a b : ℕ) : ENNReal))
    -- ℕ-level bound for the reindexed sum, in `n * (4n)` shape
    -- (`sum_max_le` is the arithmetic core, from `ARA.Helpers.Partition`).
    have hkey : (∑ r ∈ Finset.range (tail.length + 1),
        (tail.length + 4 * max r (tail.length - r))) ≤
        (tail.length + 1) * (4 * (tail.length + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h4 := sum_max_le (tail.length + 1)
      simp only [Nat.add_sub_cancel] at h4
      have hf : (tail.length + 1) ^ 2 = tail.length ^ 2 + 2 * tail.length + 1 := by
        ring
      have he : (tail.length + 1) * (4 * (tail.length + 1)) =
          4 * tail.length ^ 2 + 8 * tail.length + 4 := by ring
      have hd : (tail.length + 1) * tail.length = tail.length ^ 2 + tail.length := by
        ring
      omega
    -- Average the `n` bounds: `n⁻¹ * (n * 4n) ≤ 4n`.
    refine uniform_avg_le (by simp)
      (le_trans (Finset.sum_le_sum fun i _ => hbound i) ?_)
    rw [hsum, Fin.sum_univ_eq_sum_range
      (fun r => (tail.length : ENNReal) +
        4 * ((max r ((head :: tail).length - 1 - r) : ℕ) : ENNReal))]
    simp only [List.length_cons, Nat.add_sub_cancel]
    refine le_trans (le_of_eq ?_) (le_trans (Nat.cast_le.mpr hkey) (le_of_eq ?_))
    · push_cast
      rfl
    · push_cast
      ring

/-!
### The exact expected cost for arbitrary rank (Knuth 1971)

For general `k` the recursion enters the `<`-side (size `r`, rank `k`)
when the pivot rank `r` exceeds `k`, stops at `r = k`, and enters the
`≥`-side (size `n−1−r`, rank `k−1−r`) when `r < k`, so

`n·C(n,k) = n(n−1) + Σ_{r=k+1}^{n−1} C(r,k) + Σ_{s=0}^{k−1} C(n−k+s, s)`

(the second sum reindexed by `s := k−1−r`). Its solution (Knuth 1971,
*Mathematical analysis of algorithms*) is the bivariate harmonic
closed form `expected_qsel_cost` below. Each partial sum telescopes
against an explicit closed form by a one-variable induction
(`qsel_sumA`, `qsel_sumB`), phrased via the ℕ-subtraction-free
reparametrization `qselCost j k = expected_qsel_cost (j + k) k`.
-/

/-- Knuth's exact expected number of comparisons for selecting rank `k`
(0-indexed) from `n` distinct elements:
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))`.
Specializes to `2n − 2·H(n)` at `k = 0` (`expected_qsel_cost_zero`). -/
def expected_qsel_cost (n k : ℕ) : ℚ :=
  2 * (n + 3 + (n + 1) * harmonic n
      - (k + 3) * harmonic (k + 1)
      - (n + 2 - k) * harmonic (n - k))

/-- At `k = 0`, Knuth's formula collapses to the classic
minimum-selection cost `2n − 2·H(n)`. -/
lemma expected_qsel_cost_zero (n : ℕ) :
    expected_qsel_cost n 0 = 2 * n - 2 * harmonic n := by
  unfold expected_qsel_cost
  rw [Nat.sub_zero, harmonic_succ 0, harmonic_zero]
  push_cast
  ring

/-- `j`-parametrized form of `expected_qsel_cost`, avoiding
ℕ-subtraction: `qselCost j k` is the expected cost for length `j + k`
and rank `k`. All telescoping runs through this form. -/
private def qselCost (j k : ℕ) : ℚ :=
  2 * (j + k + 3 + (j + k + 1) * harmonic (j + k)
      - (k + 3) * harmonic (k + 1)
      - (j + 2) * harmonic j)

private lemma expected_qsel_cost_add (j s : ℕ) :
    expected_qsel_cost (j + s) s = qselCost j s := by
  unfold expected_qsel_cost qselCost
  rw [Nat.add_sub_cancel]
  push_cast
  ring

/-- Closed form for the `<`-side partial sum `Σ_{t<d} C(k+1+t, k)`:
the ranks strictly above `k` contribute a telescoping harmonic sum. -/
private lemma qsel_sumA (k d : ℕ) :
    ∑ t ∈ Finset.range d, qselCost (t + 1) k =
      d * (d + 2 * k + 7)
      + (k + d + 1) * (k + d + 2) * harmonic (k + d)
      - (k + d) * (k + d + 3) / 2
      - ((k + 1) * (k + 2) + 2 * d * (k + 3)) * harmonic (k + 1)
      + (k + 2) + k * (k + 3) / 2
      - (d + 1) * (d + 4) * harmonic d
      + d * (d + 7) / 2 := by
  induction d with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero, harmonic_zero]
      rw [harmonic_succ k]
      have hk : (k : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      unfold qselCost
      rw [show d + 1 + k = k + d + 1 from by omega,
        show k + (d + 1) = k + d + 1 from by omega,
        harmonic_succ (k + d), harmonic_succ d]
      have h1 : (k : ℚ) + d + 1 ≠ 0 := by positivity
      have h2 : (d : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- Closed form for the `≥`-side partial sum `Σ_{s<k} C(j+s, s)`: the
ranks strictly below `k`, reindexed, contribute a diagonal harmonic
sum with fixed side-length offset `j`. -/
private lemma qsel_sumB (j k : ℕ) :
    ∑ s ∈ Finset.range k, qselCost j s =
      k * (2 * j + k + 5)
      + (j + k) * (j + k + 1) * harmonic (j + k)
      - (j + k) * (j + k + 3) / 2
      - j * (j + 1) * harmonic j
      + j * (j + 3) / 2
      - (k + 1) * (k + 4) * harmonic (k + 1)
      + (k + 4) + k * (k + 7) / 2
      - 2 * k * (j + 2) * harmonic j := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.add_zero]
      rw [harmonic_succ 0, harmonic_zero]
      push_cast
      ring
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      unfold qselCost
      rw [show j + (k + 1) = j + k + 1 from by omega,
        harmonic_succ (j + k), harmonic_succ (k + 1)]
      have h1 : (j : ℚ) + k + 1 ≠ 0 := by positivity
      have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- Recurrence satisfaction: summing the branch costs over all `n`
pivot ranks gives `n·C(n,k) − n(n−1)`, i.e. `expected_qsel_cost`
solves Quickselect's three-way recurrence. The sum splits at rank `k`
into the two telescoped partial sums. -/
private lemma qsel_cost_sum_eq (n k : ℕ) (hk : k < n) :
    ∑ r ∈ Finset.range n,
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (n - 1 - r) (k - r - 1)) =
    n * expected_qsel_cost n k - n * (n - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (by omega : k + 1 ≤ k + 1 + d),
    ← Finset.range_eq_Ico]
  -- Ranks below `k` (reflected) and the vanishing `r = k` term.
  have hB : (∑ r ∈ Finset.range (k + 1),
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (k + 1 + d - 1 - r) (k - r - 1))) =
      ∑ s ∈ Finset.range k, qselCost (d + 1) s := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl k), if_pos rfl, add_zero,
      ← Finset.sum_range_reflect (fun s => qselCost (d + 1) s) k]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r < k := Finset.mem_range.mp hr
    rw [if_neg (by omega), if_neg (by omega),
      show k - r - 1 = k - 1 - r from by omega,
      show k + 1 + d - 1 - r = d + 1 + (k - 1 - r) from by omega,
      expected_qsel_cost_add]
  -- Ranks above `k`.
  have hA : (∑ r ∈ Finset.Ico (k + 1) (k + 1 + d),
      (if k < r then expected_qsel_cost r k
       else if k = r then 0
       else expected_qsel_cost (k + 1 + d - 1 - r) (k - r - 1))) =
      ∑ t ∈ Finset.range d, qselCost (t + 1) k := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [show k + 1 + d - (k + 1) = d from by omega]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos (by omega : k < k + 1 + t),
      show k + 1 + t = t + 1 + k from by omega,
      expected_qsel_cost_add]
  -- Combine the closed forms; one final harmonic-step rewrite closes it.
  rw [hB, hA, qsel_sumA k d, qsel_sumB (d + 1) k,
    show k + 1 + d = d + 1 + k from by omega,
    expected_qsel_cost_add]
  unfold qselCost
  rw [show d + 1 + k = k + d + 1 from by omega,
    harmonic_succ (k + d), harmonic_succ d]
  have h1 : (k : ℚ) + d + 1 ≠ 0 := by positivity
  have h2 : (d : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Exact expected complexity of Quickselect** (Knuth 1971's analysis).
Selecting rank `k` (0-indexed, `k < n`) from a list
of `n` distinct elements costs exactly
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))` comparisons in
expectation. -/
theorem Expected_Complexity_Quickselect_exact
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) (k : ℕ) (hnd : L.Nodup) (hk : k < L.length) :
    𝔼ℝ_runtime[Quickselect L k | M] =
      (expected_qsel_cost L.length k : ℚ) := by
  revert hnd hk
  induction L, k using Quickselect.induct with
  | case1 k =>
    -- Vacuous: no rank is below length `0`.
    intro _ hk
    simp only [List.length_nil] at hk
    omega
  | case2 head tail k ih1 ih2 =>
    intro hnd hk
    rw [expected_cost_quickselect_step head tail k]
    -- Every branch is finite (from the `C(n,2)` bound), so `toReal`
    -- distributes through the average.
    have hite : ∀ i : Fin (head :: tail).length,
        (if k < (pivotLT (head :: tail) i).length then
          𝔼_runtime[Quickselect (pivotLT (head :: tail) i) k | M]
        else if k = (pivotLT (head :: tail) i).length then 0
        else
          𝔼_runtime[Quickselect (pivotGE (head :: tail) i)
            (k - (pivotLT (head :: tail) i).length - 1) | M]) ≠ ⊤ := by
      intro i
      split_ifs
      · exact expected_cost_quickselect_ne_top _ _
      · exact ENNReal.zero_ne_top
      · exact expected_cost_quickselect_ne_top _ _
    rw [toReal_uniform_avg (fun i =>
      ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hite i⟩)]
    have hknat : k < tail.length + 1 := by simpa using hk
    -- Rewrite each summand with the IH (in `ℝ`); the `≥`-branch rank
    -- stays in range because the two filters partition `rest`.
    have hterm : ∀ i : Fin (head :: tail).length,
        (((((head :: tail).eraseIdx i).length : ENNReal) +
          (if k < (pivotLT (head :: tail) i).length then
            𝔼_runtime[Quickselect (pivotLT (head :: tail) i) k | M]
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            𝔼_runtime[Quickselect (pivotGE (head :: tail) i)
              (k - (pivotLT (head :: tail) i).length - 1) | M])).toReal) =
        (tail.length : ℝ) +
          ((if k < (pivotLT (head :: tail) i).length then
            expected_qsel_cost
              ((pivotLT (head :: tail) i).length) k
          else if k = (pivotLT (head :: tail) i).length then 0
          else
            expected_qsel_cost
              ((pivotGE (head :: tail) i).length)
              (k - (pivotLT (head :: tail) i).length - 1) :
            ℚ) : ℝ) := by
      intro i
      have hlen : (pivotLT (head :: tail) i).length +
          (pivotGE (head :: tail) i).length =
          tail.length := by
        rw [length_filter_lt_ge ((head :: tail).eraseIdx i) (head :: tail)[i]]
        exact length_eraseIdx_cons head tail i
      rw [ENNReal.toReal_add (ENNReal.natCast_ne_top _) (hite i),
        ENNReal.toReal_natCast, length_eraseIdx_cons head tail i]
      congr 1
      split_ifs with h1 h2
      · exact ih1 i ((hnd.eraseIdx _).filter _) h1
      · simp
      · exact ih2 i ((hnd.eraseIdx _).filter _)
          (by simp only [pivotLT, pivotGE] at *; omega)
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    -- Reindex by rank (`|lt_i| = rank i`, `|ge_i| = n−1−rank i`).
    rw [nodup_partition_sum₂ (head :: tail) hnd
      (fun a b => (tail.length : ℝ) +
        ((if k < a then expected_qsel_cost a k
          else if k = a then 0
          else expected_qsel_cost b (k - a - 1) : ℚ) : ℝ))]
    rw [Fin.sum_univ_eq_sum_range
      (fun r => (tail.length : ℝ) +
        ((if k < r then expected_qsel_cost r k
          else if k = r then 0
          else expected_qsel_cost ((head :: tail).length - 1 - r) (k - r - 1) : ℚ) : ℝ))]
    -- Separate the constant part and apply the recurrence identity.
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show (∑ r ∈ Finset.range (head :: tail).length,
          ((if k < r then expected_qsel_cost r k
            else if k = r then 0
            else expected_qsel_cost ((head :: tail).length - 1 - r) (k - r - 1) : ℚ) : ℝ)) =
        ((∑ r ∈ Finset.range (head :: tail).length,
          (if k < r then expected_qsel_cost r k
            else if k = r then 0
            else expected_qsel_cost ((head :: tail).length - 1 - r) (k - r - 1)) : ℚ) : ℝ)
        from by push_cast; rfl,
      qsel_cost_sum_eq (head :: tail).length k hk]
    -- Close with field arithmetic in `ℝ`.
    have hn1 : ((tail.length : ℝ) + 1) ≠ 0 := by positivity
    simp only [List.length_cons]
    push_cast
    field_simp
    ring

/-!
## Named corollaries at `M = PMF`
-/

/-- Expected number of comparisons performed by `Quickselect L k`:
the expected runtime of the instrumented algorithm interpreted in
`PMF`, one tick per pivot comparison. -/
noncomputable def quickselectComparisons (L : List α) (k : ℕ) : ENNReal :=
  𝔼_runtime[Quickselect L k | PMF]

/-- **Expected cost is linear.** Selecting from a list of `n` distinct
elements takes at most `4 n` comparisons in expectation. -/
theorem quickselect_expected_cost_linear
    (L : List α) (k : ℕ) (hnd : L.Nodup) :
    quickselectComparisons L k ≤ 4 * (L.length : ENNReal) :=
  Expected_Complexity_Quickselect L k hnd

/-- **Exact expected cost** (Knuth 1971): selecting rank `k` from `n`
distinct elements takes exactly
`2(n + 3 + (n+1)·H(n) − (k+3)·H(k+1) − (n+2−k)·H(n−k))` comparisons
in expectation. -/
theorem quickselect_expected_cost_exact
    (L : List α) (k : ℕ) (hnd : L.Nodup) (hk : k < L.length) :
    (quickselectComparisons L k).toReal = (expected_qsel_cost L.length k : ℚ) :=
  Expected_Complexity_Quickselect_exact (M := PMF) L k hnd hk

end ARA
