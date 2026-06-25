/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.ExpectedCost
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# QuickSort

This module implements a modular version of QuickSort.

## Architecture

A single `QuickSort` definition is parameterized by both `RandMonad`
(for pivot selection) and `MonadCost ℕ` (for cost tracking). By
instantiating with different `MonadCost` instances, the same code
serves as:

* **Untimed specification** (`M = PMF`, no-op `tick`)
* **Timed specification** (`M = TimeMT ℕ PMF`, accumulating `tick`)
* **Executable** (`M = IO`, no-op `tick`)
* **Executable timed** (`M = TimeMT ℕ IO`, accumulating `tick`)

## Main results

* `Correctness_Quicksort` — Establishes generic correctness over any
  `LawfulRandMonad`: guarantees the algorithm deterministically
  returns a sorted permutation of the input list.
* `Expected_Complexity_Quicksort` — Quantifies the exact expected
  cost over any `LawfulRandMonad`: sorting a list of `n` distinct
  elements requires exactly `2(n+1)H(n) - 4n` comparisons.

## Notation

The expected runtime of a timed computation is written using the
`𝔼_runtime[·]` (or `𝔼ℝ_runtime[·]` for a real value) notation defined in
`ARA.ExpectedCost`. For example:

  `𝔼ℝ_runtime[(QuickSort L : TimeMT ℕ M _)]`

reads as "the expected runtime of QuickSort on L, as a real number".
The type ascription is needed because `QuickSort` is monad-polymorphic;
the `instRandMonadTimeMT` / `instMonadCostTimeMT` instances are then
picked up automatically.
-/

namespace ARA

open ARA
open Cslib.Algorithms.Lean
open List

/-!
## Algorithm definition

A single implementation parameterized by `MonadCost ℕ M`.
The `MonadCost.tick` call is a no-op when `M` doesn't track cost,
and accumulates cost when `M = TimeMT ℕ M'`.
-/

/-- The main QuickSort function, polymorphic in the random monad `M`
and the cost monad `MonadCost ℕ M`. -/
def QuickSort
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List ℕ → M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      MonadCost.tick rest.length
      let S1 ← QuickSort L1
      let S2 ← QuickSort L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
  decreasing_by all_goals grind

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO: real computable (pseudo-)randomness
instance : RandMonad IO where
  randFin n := do
    let i ← IO.rand 0 (n - 1)
    return ⟨i % n, Nat.mod_lt i (Nat.pos_of_ne_zero (NeZero.ne n))⟩

-- IO version (executable, untimed)
def QuickSort_IO : List ℕ → IO (List ℕ) := QuickSort

#eval QuickSort_IO [8,4,1,2]

-- PMF version (noncomputable specification)
noncomputable def QuickSort_PMF :
    List ℕ → PMF (List ℕ) := QuickSort

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

/-- RandMonad lifts through `TimeMT` via `monadLift`. -/
instance instRandMonadTimeMT {M} [Monad M] [RandMonad M] :
    RandMonad (TimeMT ℕ M) where
  randFin n := TimeMT.lift (RandMonad.randFin n)

-- IO timed version (executable)
def QuickSort_IO_Timed : List ℕ → TimeMT ℕ IO (List ℕ) := QuickSort

#eval (QuickSort_IO_Timed [5, 4, 2, 1, 3, 6, 2, 1, 24, 6]).run

-- PMF timed version (noncomputable specification)
noncomputable def QuickSort_PMF_Timed :
    List ℕ → TimeMT ℕ PMF (List ℕ) := QuickSort

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-! ### Helper lemmas -/

/-- Two sorted ℕ-permutations are equal. -/
lemma eq_of_sortedLE_perm
    {l1 l2 : List ℕ}
    (h1 : l1.SortedLE) (h2 : l2.SortedLE)
    (hp : l1.Perm l2) : l1 = l2 :=
  hp.eq_of_pairwise
    (fun _ _ _ _ hab hba =>
      Nat.le_antisymm hab hba)
    (sortedLE_iff_pairwise.mp h1)
    (sortedLE_iff_pairwise.mp h2)

/-- Concatenation `S1 ++ [p] ++ S2` is sorted when
`∀ x ∈ S1, x < p` and `∀ x ∈ S2, p ≤ x` and both
sublists are sorted. -/
lemma sorted_concat_pivot
    {S1 S2 : List ℕ} {p : ℕ}
    (h1 : S1.SortedLE) (h2 : S2.SortedLE)
    (hb1 : ∀ x ∈ S1, x < p)
    (hb2 : ∀ x ∈ S2, p ≤ x) :
    (S1 ++ [p] ++ S2).SortedLE := by
  rw [sortedLE_iff_pairwise]
  apply pairwise_append.mpr
  refine ⟨?_, sortedLE_iff_pairwise.mp h2,
    fun x hx y hy => by grind⟩
  rw [← sortedLE_iff_pairwise,
    sortedLE_iff_pairwise]
  grind

/-- `eraseIdx` gives back a permutation. -/
lemma perm_getElem_cons_eraseIdx
    (L : List ℕ) (i : Fin L.length) :
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

/-- Filter-partition around a pivot permutes the
original list. -/
lemma perm_filter_partition
    (L : List ℕ) (i : Fin L.length) :
    ((L.eraseIdx i).filter
        (fun x => decide (x < L[i])) ++
      [L[i]] ++
      (L.eraseIdx i).filter
        (fun x => decide (x ≥ L[i]))).Perm L := by
  have hc :
    (L.eraseIdx i).filter
      (fun x => !(decide (x < L[i]))) =
    (L.eraseIdx i).filter
      (fun x => decide (x ≥ L[i])) := by grind
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
    simp only [append_assoc]; grind
  exact hmid.trans
    ((Perm.cons _ hf).trans
      (perm_getElem_cons_eraseIdx L i).symm)

/-!
### Abbreviations

Deterministic branch abstraction for the
partition-and-recurse step at a given pivot index.
-/

/-- Branch: partition around pivot `L[i]` and
recurse with `QuickSort`. Used for both correctness
and complexity proofs. -/
private noncomputable abbrev qs_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List ℕ) (i : Fin L.length) :
    M (List ℕ) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  MonadCost.tick rest.length
  let S1 ← QuickSort (rest.filter (· < pivot))
  let S2 ← QuickSort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

/-!
### Structural decomposition

`QuickSort` on a nonempty list is exactly
`randIdx >>= qs_branch`.
-/

/-- `QuickSort L` on a nonempty list decomposes as
`randIdx L >>= qs_branch M L`. -/
private lemma quicksort_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : ℕ) (tail : List ℕ) :
    (QuickSort (head :: tail) : M (List ℕ)) =
    randIdx (head :: tail) (by grind) >>=
      fun idx => qs_branch M (head :: tail) idx := by
  rw [QuickSort.eq_2 head tail]

/-- Timed decomposition: in `TimeMT ℕ M`, `QuickSort` decomposes
as `TimeMT.lift (randIdx ...) >>= qs_branch`. This exposes the
`TimeMT.lift` for bridge lemma application. -/
private lemma quicksort_timed_eq_bind
    {M} [Monad M] [RandMonad M]
    (head : ℕ) (tail : List ℕ) :
    (QuickSort (head :: tail) : TimeMT ℕ M (List ℕ)) =
    TimeMT.lift (randIdx (head :: tail) : M _) >>=
      fun idx => qs_branch (TimeMT ℕ M) (head :: tail) idx := by
  rw [QuickSort.eq_2 (M := TimeMT ℕ M) head tail]
  rfl

/-!
### Generic correctness theorem

For the correctness proof, we work with the no-op `MonadCost`
instance. The tick becomes `pure ()` and is invisible.
-/

/-- For any `LawfulRandMonad`, `QuickSort L` (with no-op cost
tracking) produces a single deterministic output that is sorted
and a permutation of `L`. -/
lemma Correctness_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [LawfulRandMonad M] :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      LawfulRandMonad.toPMF
        (@QuickSort M _ _ instMonadCostDefault L) =
        pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  apply QuickSort.induct
  -- Base case
  · exact ⟨[],
      by simp [QuickSort,
        LawfulRandMonad.toPMF_pure],
      by simp [List.sortedLE_iff_pairwise],
      by simp⟩
  -- Inductive case
  · intro head tail ihL1 ihL2
    let L := head :: tail
    -- For each pivot, build a correct output from IH
    have h_step :
        ∀ i : Fin L.length, ∃ Out,
          LawfulRandMonad.toPMF
            (@qs_branch M _ _ instMonadCostDefault L i) =
            pure Out ∧
          Out.SortedLE ∧ Out.Perm L := by
      intro i
      obtain ⟨O1, h1, s1, p1⟩ := ihL1 i
      obtain ⟨O2, h2, s2, p2⟩ := ihL2 i
      use O1 ++ [L[i]] ++ O2
      split_ands
      · unfold qs_branch; unfold_do
        simp only [LawfulRandMonad.toPMF_bind,
          LawfulRandMonad.toPMF_pure,
          MonadCost.tick_default]
        rw [h1, h2]
        simp_all [length_cons,
          Fin.getElem_fin, ge_iff_le, L]
        rfl
      · apply sorted_concat_pivot s1 s2
          <;> grind
      · exact (Perm.append
          (Perm.append p1 (.refl _)) p2).trans
          (perm_filter_partition L i)
    -- All pivots yield the same output (uniqueness
    -- of sorted permutation), so the PMF is a point mass.
    obtain ⟨Output, h0, hS, hP⟩ :=
      h_step ⟨0, by grind⟩
    refine ⟨Output, ?_, hS, hP⟩
    have : Nonempty (Fin L.length) :=
      ⟨⟨0, by grind⟩⟩
    calc LawfulRandMonad.toPMF
          (@QuickSort M _ _ instMonadCostDefault L)
        = LawfulRandMonad.toPMF
            (randIdx L (by grind) >>=
              fun idx =>
                @qs_branch M _ _ instMonadCostDefault L idx) := by
          unfold qs_branch
          rw [@QuickSort.eq_2 M _ _ instMonadCostDefault head tail]
      _ = (PMF.uniformOfFintype
            (Fin L.length)).bind
            (fun idx =>
              LawfulRandMonad.toPMF
                (@qs_branch M _ _ instMonadCostDefault L idx)) := by
          rw [LawfulRandMonad.toPMF_bind,
            LawfulRandMonad.toPMF_randIdx]
          simp_all only [length_cons,
            Fin.getElem_fin, ge_iff_le,
            Fin.zero_eta, L]
          rfl
      _ = (PMF.uniformOfFintype
            (Fin L.length)).bind
            fun _ => pure Output := by
          congr 1; funext i
          obtain ⟨Oi, hi, si, pi⟩ := h_step i
          rwa [eq_of_sortedLE_perm si hS
            (pi.trans hP.symm)] at hi
      _ = pure Output := PMF.bind_const _ _

-- ----------------------------------------
-- Free Proof: Untimed QuickSort_PMF
-- ----------------------------------------

lemma Correctness_Quicksort_PMF :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      QuickSort_PMF L = pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  intro L
  obtain ⟨Out, hEq, hS, hP⟩ :=
    @Correctness_Quicksort PMF _ _ _ L
  exact ⟨Out, hEq, hS, hP⟩

-- ----------------------------------------
-- Free Proof: Timed QuickSort_PMF_Timed
-- ----------------------------------------

/-! ### TimeMT erasure for the unified QuickSort -/

@[simp] lemma TimeMT_randIdx_run
    {M} [Monad M] [RandMonad M]
    (L : List ℕ) (h : 0 < L.length) :
    (randIdx L h :
      TimeMT ℕ M (Fin L.length)).run =
    (TimeMT.lift
      (randIdx L h :
        M (Fin L.length))).run := rfl

/-- Erasing time from the timed QuickSort gives the untimed QuickSort.
This follows from the unified definition: the `MonadCost.tick` in
`TimeMT` erases to `pure ()`, matching the no-op `MonadCost` instance.

Uses **functional induction** on `QuickSort`. -/
lemma QuickSort_erasure
    {M} [Monad M] [LawfulMonad M] [RandMonad M]
    (L : List ℕ) :
    TimeM.ret <$>
      (QuickSort L : TimeMT ℕ M (List ℕ)).run =
      (QuickSort L : M (List ℕ)) := by
  induction L using QuickSort.induct
  · -- Base case
    rw [QuickSort.eq_1 (M := TimeMT ℕ M), QuickSort.eq_1 (M := M)]
    simp
  · -- Inductive case
    next head tail ih1 ih2 =>
    rw [QuickSort.eq_2 (M := TimeMT ℕ M) head tail,
        QuickSort.eq_2 (M := M) head tail]
    simp only [TimeMT_erase_bind, TimeMT_randIdx_run, TimeMT_erase_lift,
      MonadCost.tick_timeMT, TimeMT_erase_tick, MonadCost.tick_default, pure_bind]
    simp only [ih1, ih2, TimeMT_erase_pure]

/-- Timed PMF correctness for free. -/
lemma Correctness_QuickSort_Timed_PMF :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      TimeM.ret <$> (QuickSort_PMF_Timed L).run =
        pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  intro L
  obtain ⟨Out, hEq, hSort, hPerm⟩ :=
    Correctness_Quicksort_PMF L
  use Out
  unfold QuickSort_PMF_Timed
  rw [QuickSort_erasure]
  exact ⟨hEq, hSort, hPerm⟩

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
### Closed-form cost function

We reuse Mathlib's harmonic number
`harmonic n = ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹`
(`Mathlib.NumberTheory.Harmonic.Defs`) together with its `@[simp]` lemmas
`harmonic_zero` and `harmonic_succ`, rather than redefining it here.
-/

/-- The exact expected number of comparisons for
QuickSort on a list of `n` distinct elements:
`2(n+1)H(n) − 4n`. -/
def expected_qs_cost (n : ℕ) : ℚ :=
  2 * (n + 1) * harmonic n - 4 * n

@[simp] lemma expected_qs_cost_zero :
    expected_qs_cost 0 = 0 := by
  simp [expected_qs_cost, harmonic]

@[simp] lemma expected_qs_cost_one :
    expected_qs_cost 1 = 0 := by
  simp [expected_qs_cost, harmonic]; norm_num

/-- Helper: extracts the summation into a closed form. -/
lemma expected_qs_sum_helper (n : ℕ) :
    (2 : ℚ) * ∑ i ∈ Finset.range n,
      expected_qs_cost i =
    (n : ℚ) *
      (expected_qs_cost n - (n : ℚ) + 1) := by
  induction n with
  | zero => simp [expected_qs_cost, harmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold expected_qs_cost
    rw [harmonic_succ]; push_cast
    have h_nz : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp; ring

/-- The QuickSort recurrence:
`C(n+1) = n + (2/(n+1)) ∑_{i<n+1} C(i)`. -/
lemma expected_qs_recurrence (n : ℕ) :
    (n : ℚ) +
      (2 / (n + 1)) *
        (∑ i ∈ Finset.range (n + 1),
          expected_qs_cost i) =
    expected_qs_cost (n + 1) := by
  have h_sum := expected_qs_sum_helper (n + 1)
  push_cast at h_sum ⊢
  have h_nz : (n : ℚ) + 1 ≠ 0 := by positivity
  have h_step :
    2 / ((n : ℚ) + 1) *
      (∑ i ∈ Finset.range (n + 1),
        expected_qs_cost i) =
    (((n : ℚ) + 1) *
      (expected_qs_cost (n + 1) -
        ((n : ℚ) + 1) + 1)) /
      ((n : ℚ) + 1) := by
    calc 2 / ((n : ℚ) + 1) *
          (∑ i ∈ Finset.range (n + 1),
            expected_qs_cost i)
      _ = (2 * ∑ i ∈ Finset.range (n + 1),
            expected_qs_cost i) /
          ((n : ℚ) + 1) := by ring
      _ = (((n : ℚ) + 1) *
            (expected_qs_cost (n + 1) -
              ((n : ℚ) + 1) + 1)) /
          ((n : ℚ) + 1) := by rw [h_sum]
  rw [h_step]; field_simp; ring

/-- Non-negativity of `expected_qs_cost`. -/
lemma expected_qs_cost_nonneg (n : ℕ) :
    0 ≤ expected_qs_cost n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | n + 1 =>
      rw [← expected_qs_recurrence]
      apply add_nonneg (by positivity)
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro i hi
      exact ih i (Finset.mem_range.mp hi)

/-!
### Branch cost lemma (for timed variant)

The expected cost of the deterministic branch
`qs_branch M L i` (when `M = TimeMT ℕ M'`) is the tick cost
plus the expected costs of the two recursive calls.

Uses the `𝔼_runtime[·]` notation for readability.
-/

/-- The expected cost of `qs_branch` in `TimeMT` is
`rest.length + E[QS L1] + E[QS L2]`. -/
private lemma expected_cost_qs_branch
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List ℕ) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (· < pivot)
    let L2 := rest.filter (· ≥ pivot)
    𝔼_runtime[qs_branch (TimeMT ℕ M) L i] =
    (rest.length : ENNReal) +
      𝔼_runtime[(QuickSort L1 : TimeMT ℕ M _)] +
      𝔼_runtime[(QuickSort L2 : TimeMT ℕ M _)] := by
  intro pivot rest L1 L2
  -- Peel `tick` and the trailing `pure` automatically.
  show expected_cost (inst.toPMF
    (TimeMT.tick rest.length >>=
      fun _ => (QuickSort L1 : TimeMT ℕ M _) >>=
        fun S1 => (QuickSort L2 : TimeMT ℕ M _) >>=
          fun S2 => pure
            (S1 ++ [pivot] ++ S2)).run) = _
  cost_step
  -- Decompose the outer recursive bind, then collapse the inner
  -- continuation `(QS L2 >>= pure)` to `E[QS L2]`.
  rw [expected_cost_toPMF_bind]
  have h_inner : ∀ tm : TimeM ℕ (List ℕ),
      expected_cost
        (inst.toPMF
          ((QuickSort L2 : TimeMT ℕ M _) >>= fun S2 =>
            (pure (tm.ret ++ [pivot] ++ S2) :
              TimeMT ℕ M (List ℕ))).run) =
      expected_cost
        (inst.toPMF (QuickSort L2 : TimeMT ℕ M _).run) := by
    intro tm
    rw [expected_cost_toPMF_bind]
    cost_step
  simp only [h_inner, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  ring

/-!
### Monadic unfolding: base case
-/

lemma expected_cost_quicksort_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_runtime[(QuickSort [] : TimeMT ℕ M (List ℕ))] = 0 := by
  rw [QuickSort.eq_1]; cost_step

/-!
### Monadic unfolding: inductive step
-/

/-- After applying `toPMF` to `.run` of `QuickSort`
(in `TimeMT`) on a nonempty list, the expected cost is the
uniform average:
`E[cost] = (1/n) * Σ_i (|rest_i| + E[L1_i] + E[L2_i])`
-/
lemma expected_cost_quicksort_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : ℕ) (tail : List ℕ) :
    let L := head :: tail
    𝔼_runtime[(QuickSort L : TimeMT ℕ M _)] =
    (L.length : ENNReal)⁻¹ *
      ∑ i : Fin L.length,
        let pivot := L[i]
        let rest := L.eraseIdx i
        let L1 := rest.filter (· < pivot)
        let L2 := rest.filter (· ≥ pivot)
        ((rest.length : ENNReal) +
          𝔼_runtime[(QuickSort L1 : TimeMT ℕ M _)] +
          𝔼_runtime[(QuickSort L2 : TimeMT ℕ M _)]) := by
  intro L
  -- Step 1: decompose as lift(randIdx) >>= qs_branch
  conv_lhs =>
    rw [show L = head :: tail from rfl]
  rw [quicksort_timed_eq_bind head tail]
  -- Step 2: apply lift-bind to separate randomness
  show expected_cost (inst.toPMF (TimeMT.lift (randIdx (head :: tail) : M _) >>=
    fun idx => qs_branch (TimeMT ℕ M) (head :: tail) idx).run) = _
  cost_step
  rw [inst.toPMF_randIdx]
  -- Step 3: convert tsum to finsum, factor out 1/n
  have hne : Nonempty (Fin L.length) :=
    ⟨⟨0, by grind⟩⟩
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply,
    Fintype.card_fin]
  rw [Finset.mul_sum]
  -- Step 4: apply branch cost lemma to each summand
  congr 1; ext i; congr 1
  exact expected_cost_qs_branch L i

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
private noncomputable def rank (L : List ℕ) (i : Fin L.length) : Fin L.length :=
  ⟨((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card,
   by
    calc ((Finset.univ.erase i).filter (fun j => L[j] < L[i])).card
        ≤ (Finset.univ.erase i).card := Finset.card_filter_le _ _
      _ = L.length - 1 := by simp [Finset.card_erase_of_mem]
      _ < L.length := Nat.sub_lt (Fin.pos i) Nat.one_pos⟩

/-- The rank function equals the filter-length on the erased list. -/
private lemma rank_eq_filter_length (L : List ℕ) (hnd : L.Nodup) (i : Fin L.length) :
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
private lemma complement_rank_eq (L : List ℕ) (hnd : L.Nodup) (i : Fin L.length) :
    ((L.eraseIdx i).filter (· ≥ L[i])).length =
      L.length - 1 - (rank L i).val := by
  have h_split :
    ((L.eraseIdx i).filter (· ≥ L[i])).length +
      ((L.eraseIdx i).filter (· < L[i])).length =
      L.length - 1 := by
    have : ∀ l : List ℕ,
        (l.filter (· ≥ L[i])).length +
          (l.filter (· < L[i])).length =
          l.length := by
      intro l; induction l
        <;> simp +decide [*]; grind
    convert this (L.eraseIdx i) using 1
    simp +decide [List.length_eraseIdx]
  exact eq_tsub_of_add_eq
    (by linarith [rank_eq_filter_length L hnd i])

/-- The rank function is injective on nodup lists. -/
private lemma rank_injective (L : List ℕ) (hnd : L.Nodup) :
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
private noncomputable def rankEquiv (L : List ℕ) (hnd : L.Nodup) : Fin L.length ≃ Fin L.length :=
  Equiv.ofBijective (rank L) (Finite.injective_iff_bijective.mp (rank_injective L hnd))

/-- Reindexing partition sizes by rank for nodup lists.

Uses `Finset.sum_equiv` with the rank equivalence for a clean
bijective reindexing. -/
lemma nodup_partition_sum
    (L : List ℕ) (hnd : L.Nodup) (f : ℕ → ℚ) :
    (∑ i : Fin L.length,
      (f ((L.eraseIdx i).filter
          (· < L[i])).length +
       f ((L.eraseIdx i).filter
          (· ≥ L[i])).length)) =
    ∑ k : Fin L.length,
      (f k.val +
        f (L.length - 1 - k.val)) := by
  -- Rewrite LHS summand in terms of rank, then reindex
  have h_eq : ∀ i : Fin L.length,
      f ((L.eraseIdx i).filter (· < L[i])).length +
       f ((L.eraseIdx i).filter (· ≥ L[i])).length =
      f (rank L i).val + f (L.length - 1 - (rank L i).val) := by
    intro i; rw [rank_eq_filter_length L hnd i, complement_rank_eq L hnd i]
  simp_rw [h_eq]
  exact Finset.sum_equiv (rankEquiv L hnd)
    (fun _ => by simp)
    (fun _ _ => rfl)

/-!
### Finiteness of expected cost
-/

lemma expected_cost_quicksort_ne_top
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (L : List ℕ) :
    𝔼_runtime[(QuickSort L : TimeMT ℕ M _)] ≠ ⊤ := by
  induction' n : L.length
    using Nat.strong_induction_on
    with n ih generalizing L
  rcases L with (_ | ⟨head, tail⟩)
  -- Base case: empty list
  · simp [expected_cost_quicksort_nil]
  -- Inductive case: use step decomposition
  · rw [expected_cost_quicksort_step]
    simp_all +decide
    rw [ENNReal.mul_eq_top]; norm_num
    grind +revert

/-!
### The main theorem

**Note**: The formula `2(n+1)H(n) − 4n` requires
`L.Nodup` (distinct elements). For lists with duplicates,
the expected cost differs.
-/

/-- The expected cost of `QuickSort` (in timed mode) on a list of
`n` distinct elements is exactly `2(n+1)H(n) − 4n`
comparisons. -/
theorem Expected_Complexity_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    𝔼ℝ_runtime[(QuickSort L : TimeMT ℕ M _)] =
    (expected_qs_cost L.length : ℚ) := by
  induction' n : L.length
    using Nat.strong_induction_on
    with n ih generalizing L
  cases' L with head tail
    <;> simp_all +decide
      [expected_cost_quicksort_step]
  · subst n
    norm_num [expected_cost_quicksort_nil]
  · rw [ENNReal.toReal_sum]
    · rw [Finset.sum_congr rfl fun i hi => ?_]
      rotate_left
      use fun i =>
        (tail.length : ℝ) +
          expected_qs_cost
            ((List.filter
              (fun x =>
                decide (x < (head :: tail)[i]))
              (List.eraseIdx
                (head :: tail) i)).length) +
          expected_qs_cost
            ((List.filter
              (fun x =>
                decide
                  ((head :: tail)[i] ≤ x))
              (List.eraseIdx
                (head :: tail) i)).length)
      · rw [ENNReal.toReal_add,
          ENNReal.toReal_add]
          <;> norm_num
            [expected_cost_quicksort_ne_top]
        grind
      · have := nodup_partition_sum
          (head :: tail)
          (by aesop)
          (fun k => expected_qs_cost k)
        simp_all +decide
          [Finset.sum_add_distrib]
        have := expected_qs_recurrence
          (List.length tail)
        simp_all +decide
          [Finset.sum_range, Nat.sub_sub]
        rw [← this]; norm_cast
        simp_all +decide [add_assoc]
        ring_nf
        rw [← n]
        norm_num [Nat.succ_eq_add_one,
          add_comm, add_left_comm, add_assoc]
        ring_nf; field_simp
        rw [mul_two,
          ← Finset.sum_bij
            (fun x _ => Fin.rev x)]
        · norm_num [add_comm,
            add_left_comm, add_assoc]
          ring
        · exact fun _ _ => Finset.mem_univ _
        · aesop
        · exact fun x _ =>
            ⟨Fin.rev x, Finset.mem_univ _,
              Fin.rev_rev x⟩
        · grind
    · simp +decide [ENNReal.add_eq_top]
      grind +suggestions

/-!
## Complexity for general (possibly non-distinct) lists

The closed-form `2(n+1)H(n) − 4n` requires `L.Nodup` because duplicates
shift the partition distribution. For a list with repeated keys, the
worst case is all-equal inputs `L = [a, a, …, a]`:

  pivot = a, `L1 = []`, `L2 = rest` (length `n-1`, again all `a`)

so the recurrence degenerates to `T(n) = (n-1) + T(n-1)` and yields
`T(n) = n(n-1)/2 = C(n,2)` deterministically. This is the worst case
across all inputs and pivot sequences, so the expected cost on any list
is bounded by `C(n,2)`. -/

/-- Partition lemma: filtering a list by `(· < p)` and `(· ≥ p)`
gives complementary sub-lists. -/
private lemma length_filter_lt_ge (l : List ℕ) (p : ℕ) :
    (l.filter (· < p)).length + (l.filter (· ≥ p)).length = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    by_cases h : hd < p
    · rw [List.filter_cons_of_pos (by simpa using h),
        List.filter_cons_of_neg (by simp; omega)]
      show (tl.filter (· < p)).length + 1 +
        (tl.filter (· ≥ p)).length = tl.length + 1
      linarith [ih]
    · rw [List.filter_cons_of_neg (by simpa using h),
        List.filter_cons_of_pos (by simp; omega)]
      show (tl.filter (· < p)).length +
        ((tl.filter (· ≥ p)).length + 1) = tl.length + 1
      linarith [ih]

/-- Discrete convexity of `Nat.choose · 2`: along the line `a + b = k`,
the sum `a.choose 2 + b.choose 2` is maximized at the corners and equals
`k.choose 2 = (a + b).choose 2`.

Equivalent to the polynomial identity
`a(a − 1) + b(b − 1) + 2ab = (a + b)(a + b − 1)`. -/
private lemma choose_two_add_le (a b : ℕ) :
    a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    -- Pascal: `(n + 1).choose 2 = n.choose 1 + n.choose 2 = n + n.choose 2`.
    have hb : (b + 1).choose 2 = b.choose 2 + b := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; linarith
    have hab : (a + (b + 1)).choose 2 = (a + b).choose 2 + (a + b) := by
      rw [show a + (b + 1) = (a + b) + 1 from rfl,
        Nat.choose_succ_succ, Nat.choose_one_right]; linarith
    rw [hb, hab]; omega

/-- For an arbitrary list (possibly with duplicates), the expected cost
of `QuickSort` is bounded by `L.length.choose 2`. This bound is tight on
the all-equal list `[a, a, …, a]`.

The proof is by strong induction on `L.length`. The inductive step uses
`expected_cost_quicksort_step` to expand into a uniform average over
pivot choices, the IH to bound each recursive call, and `choose_two_add_le`
to combine the two subproblem bounds. -/
theorem Quicksort_Cost_Upper_Bound
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List ℕ) :
    𝔼ℝ_runtime[(QuickSort L : TimeMT ℕ M _)] ≤ L.length.choose 2 := by
  -- Step 1: reduce to an inequality in `ENNReal`.
  suffices h : 𝔼_runtime[(QuickSort L : TimeMT ℕ M _)] ≤
      ((L.length.choose 2 : ℕ) : ENNReal) by
    have hne : ((L.length.choose 2 : ℕ) : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have := ENNReal.toReal_mono hne h
    simpa using this
  -- Step 2: strong induction on `L.length`.
  suffices h_strong : ∀ n (L : List ℕ), L.length = n →
      𝔼_runtime[(QuickSort L : TimeMT ℕ M _)] ≤ ((n.choose 2 : ℕ) : ENNReal) by
    exact h_strong L.length L rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hL
    rcases L with (_ | ⟨head, tail⟩)
    · -- Base case: `L = []`, so `n = 0` and the bound is `0`.
      simp only [List.length_nil] at hL
      subst hL
      simp [expected_cost_quicksort_nil]
    · -- Inductive case: `L = head :: tail`, so `n = tail.length + 1`.
      simp only [List.length_cons] at hL
      have hn : n = tail.length + 1 := hL.symm
      rw [expected_cost_quicksort_step]
      -- Bound each summand by `(n.choose 2 : ENNReal)`.
      have h_summand : ∀ i : Fin (head :: tail).length,
          (((head :: tail).eraseIdx i).length : ENNReal) +
            𝔼_runtime[(QuickSort
              (((head :: tail).eraseIdx i).filter
                (· < (head :: tail)[i])) : TimeMT ℕ M _)] +
            𝔼_runtime[(QuickSort
              (((head :: tail).eraseIdx i).filter
                (· ≥ (head :: tail)[i])) : TimeMT ℕ M _)] ≤
          ((n.choose 2 : ℕ) : ENNReal) := by
        intro i
        set rest := (head :: tail).eraseIdx i with h_rest_def
        set pivot := (head :: tail)[i] with h_pivot_def
        set L1 := rest.filter (· < pivot) with h_L1_def
        set L2 := rest.filter (· ≥ pivot) with h_L2_def
        -- `rest` has length `tail.length`.
        have h_rest_len : rest.length = tail.length := by
          show ((head :: tail).eraseIdx i).length = tail.length
          rw [List.length_eraseIdx]
          have : i.val < tail.length + 1 := i.isLt
          split <;> aesop
        -- Partition: `|L1| + |L2| = |rest|`.
        have h_filter_split : L1.length + L2.length = rest.length := by
          show (rest.filter (· < pivot)).length +
            (rest.filter (· ≥ pivot)).length = rest.length
          exact length_filter_lt_ge rest pivot
        -- Lengths of `L1` and `L2` are strictly less than `n`,
        -- so the IH applies.
        have h_L1_le : L1.length ≤ rest.length := List.length_filter_le _ _
        have h_L2_le : L2.length ≤ rest.length := List.length_filter_le _ _
        have h_L1_lt : L1.length < n := by omega
        have h_L2_lt : L2.length < n := by omega
        have h_ihL1 := ih L1.length h_L1_lt L1 rfl
        have h_ihL2 := ih L2.length h_L2_lt L2 rfl
        -- Convexity: `|L1|.choose 2 + |L2|.choose 2 ≤ tail.length.choose 2`.
        have h_convex : L1.length.choose 2 + L2.length.choose 2 ≤
            tail.length.choose 2 := by
          have hc := choose_two_add_le L1.length L2.length
          rw [h_filter_split, h_rest_len] at hc
          exact hc
        -- Pascal: `n.choose 2 = tail.length + tail.length.choose 2`.
        have h_pascal : n.choose 2 = tail.length + tail.length.choose 2 := by
          rw [hn]
          show tail.length.choose 1 + tail.length.choose 2 =
            tail.length + tail.length.choose 2
          rw [Nat.choose_one_right]
        -- Combine: rest.length + IH₁ + IH₂ ≤ tail.length + tail.length.choose 2.
        calc (rest.length : ENNReal) +
              𝔼_runtime[(QuickSort L1 : TimeMT ℕ M _)] +
              𝔼_runtime[(QuickSort L2 : TimeMT ℕ M _)]
            ≤ (rest.length : ENNReal) +
                ((L1.length.choose 2 : ℕ) : ENNReal) +
                ((L2.length.choose 2 : ℕ) : ENNReal) := by gcongr
          _ = (rest.length : ENNReal) +
                (((L1.length.choose 2 + L2.length.choose 2 : ℕ) : ENNReal)) := by
                push_cast; ring
          _ ≤ (rest.length : ENNReal) +
                ((tail.length.choose 2 : ℕ) : ENNReal) := by
                exact add_le_add le_rfl (by exact_mod_cast h_convex)
          _ = (tail.length : ENNReal) +
                ((tail.length.choose 2 : ℕ) : ENNReal) := by rw [h_rest_len]
          _ = (((tail.length + tail.length.choose 2 : ℕ) : ENNReal)) := by
                push_cast; ring
          _ = ((n.choose 2 : ℕ) : ENNReal) := by rw [← h_pascal]
      -- Sum the per-summand bound.
      have h_sum_le :
          ∑ i : Fin (head :: tail).length,
            ((((head :: tail).eraseIdx i).length : ENNReal) +
              𝔼_runtime[(QuickSort
                (((head :: tail).eraseIdx i).filter
                  (· < (head :: tail)[i])) : TimeMT ℕ M _)] +
              𝔼_runtime[(QuickSort
                (((head :: tail).eraseIdx i).filter
                  (· ≥ (head :: tail)[i])) : TimeMT ℕ M _)]) ≤
          ((head :: tail).length : ENNReal) * ((n.choose 2 : ℕ) : ENNReal) := by
        calc _ ≤ ∑ _ : Fin (head :: tail).length, ((n.choose 2 : ℕ) : ENNReal) :=
                Finset.sum_le_sum (fun i _ => h_summand i)
          _ = ((head :: tail).length : ENNReal) * ((n.choose 2 : ℕ) : ENNReal) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul]
      -- Multiply both sides by `(L.length)⁻¹` and cancel.
      have hne_zero : ((head :: tail).length : ENNReal) ≠ 0 := by
        simp
      have hne_top : ((head :: tail).length : ENNReal) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      calc ((head :: tail).length : ENNReal)⁻¹ *
              ∑ i : Fin (head :: tail).length,
                ((((head :: tail).eraseIdx i).length : ENNReal) +
                  𝔼_runtime[(QuickSort
                    (((head :: tail).eraseIdx i).filter
                      (· < (head :: tail)[i])) : TimeMT ℕ M _)] +
                  𝔼_runtime[(QuickSort
                    (((head :: tail).eraseIdx i).filter
                      (· ≥ (head :: tail)[i])) : TimeMT ℕ M _)])
            ≤ ((head :: tail).length : ENNReal)⁻¹ *
                (((head :: tail).length : ENNReal) *
                  ((n.choose 2 : ℕ) : ENNReal)) := by gcongr
          _ = (((head :: tail).length : ENNReal)⁻¹ *
                ((head :: tail).length : ENNReal)) *
                ((n.choose 2 : ℕ) : ENNReal) := by rw [mul_assoc]
          _ = 1 * ((n.choose 2 : ℕ) : ENNReal) := by
                rw [ENNReal.inv_mul_cancel hne_zero hne_top]
          _ = ((n.choose 2 : ℕ) : ENNReal) := one_mul _

end ARA
