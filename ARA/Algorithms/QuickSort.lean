/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.ExpectedCost
import ARA.Algorithms.Partition
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Quicksort

This module implements a modular version of Quicksort.

## Architecture

A single `Quicksort` definition is parameterized by both `RandMonad`
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

  `𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)]`

reads as "the expected runtime of Quicksort on L, as a real number".
The type ascription is needed because `Quicksort` is monad-polymorphic;
the `instRandMonadTimeMT` / `instMonadCostTimeMT` instances are then
picked up automatically.
-/

namespace ARA

open ARA
open Cslib.Algorithms.Lean
open List

variable {α : Type} [LinearOrder α]

/-!
## Algorithm definition

A single implementation parameterized by `MonadCost ℕ M`.
The `MonadCost.tick` call is a no-op when `M` doesn't track cost,
and accumulates cost when `M = TimeMT ℕ M'`.
-/

/-- The main Quicksort function, polymorphic in the random monad `M`
and the cost monad `MonadCost ℕ M`. -/
def Quicksort
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → M (List α)
  | [] => return []
  | L@(_::_) => do
      let idx ← randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      MonadCost.tick rest.length
      let S1 ← Quicksort L1
      let S2 ← Quicksort L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
  decreasing_by all_goals grind

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed; `RandMonad IO` comes from
-- `ARA.LawfulRandMonad`)
def Quicksort_IO : List ℕ → IO (List ℕ) := Quicksort

#eval Quicksort_IO [8,4,1,2]

-- PMF version (noncomputable specification)
noncomputable def Quicksort_PMF :
    List ℕ → PMF (List ℕ) := Quicksort

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable; `RandMonad (TimeMT ℕ M)` comes from
-- `ARA.ExpectedCost`)
def Quicksort_IO_Timed : List ℕ → TimeMT ℕ IO (List ℕ) := Quicksort

#eval (Quicksort_IO_Timed [5, 4, 2, 1, 3, 6, 2, 1, 24, 6]).run

-- PMF timed version (noncomputable specification)
noncomputable def Quicksort_PMF_Timed :
    List ℕ → TimeMT ℕ PMF (List ℕ) := Quicksort

-- ----------------------------------------
-- Generic Correctness proof
-- ----------------------------------------

/-! ### Helper lemmas

The generic partition helpers (`eq_of_sortedLE_perm`,
`sorted_concat_pivot`, `perm_filter_partition`, `nodup_partition_sum₂`)
live in `ARA.Algorithms.Partition` and are shared with `Quickselect`. -/

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
    (L : List α) (i : Fin L.length) :
    M (List α) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  MonadCost.tick rest.length
  let S1 ← Quicksort (rest.filter (· < pivot))
  let S2 ← Quicksort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

/-!
### Structural decomposition

`Quicksort` on a nonempty list is exactly
`randIdx >>= qs_branch`.
-/

/-- `Quicksort L` on a nonempty list decomposes as
`randIdx L >>= qs_branch M L`. -/
private lemma quicksort_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : α) (tail : List α) :
    (Quicksort (head :: tail) : M (List α)) =
    randIdx (head :: tail) (by grind) >>=
      fun idx => qs_branch M (head :: tail) idx := by
  rw [Quicksort.eq_2 head tail]

/-- Timed decomposition: in `TimeMT ℕ M`, `Quicksort` decomposes
as `TimeMT.lift (randIdx ...) >>= qs_branch`. This exposes the
`TimeMT.lift` for bridge lemma application. -/
private lemma quicksort_timed_eq_bind
    {M} [Monad M] [RandMonad M]
    (head : α) (tail : List α) :
    (Quicksort (head :: tail) : TimeMT ℕ M (List α)) =
    TimeMT.lift (randIdx (head :: tail) : M _) >>=
      fun idx => qs_branch (TimeMT ℕ M) (head :: tail) idx := by
  rw [Quicksort.eq_2 (M := TimeMT ℕ M) head tail]
  rfl

/-!
### Generic correctness theorem

For the correctness proof, we work with the no-op `MonadCost`
instance. The tick becomes `pure ()` and is invisible.
-/

/-- For any `LawfulRandMonad`, `Quicksort L` (with no-op cost
tracking) produces a single deterministic output that is sorted
and a permutation of `L`. -/
lemma Correctness_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [LawfulRandMonad M] :
    ∀ L : List α, ∃ Output : List α,
      LawfulRandMonad.toPMF
        (@Quicksort _ _ M _ _ instMonadCostDefault L) =
        pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  apply Quicksort.induct
  -- Base case
  · exact ⟨[],
      by simp [Quicksort,
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
            (@qs_branch _ _ M _ _ instMonadCostDefault L i) =
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
          (@Quicksort _ _ M _ _ instMonadCostDefault L)
        = LawfulRandMonad.toPMF
            (randIdx L (by grind) >>=
              fun idx =>
                @qs_branch _ _ M _ _ instMonadCostDefault L idx) := by
          unfold qs_branch
          rw [@Quicksort.eq_2 _ _ M _ _ instMonadCostDefault head tail]
      _ = (PMF.uniformOfFintype
            (Fin L.length)).bind
            (fun idx =>
              LawfulRandMonad.toPMF
                (@qs_branch _ _ M _ _ instMonadCostDefault L idx)) := by
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
-- Free Proof: Untimed Quicksort_PMF
-- ----------------------------------------

lemma Correctness_Quicksort_PMF :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      Quicksort_PMF L = pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  intro L
  obtain ⟨Out, hEq, hS, hP⟩ :=
    Correctness_Quicksort (M := PMF) L
  exact ⟨Out, hEq, hS, hP⟩

-- ----------------------------------------
-- Free Proof: Timed Quicksort_PMF_Timed
-- ----------------------------------------

/-! ### TimeMT erasure for the unified Quicksort -/

omit [LinearOrder α] in
@[simp]
lemma TimeMT_randIdx_run
    {M} [Monad M] [RandMonad M]
    (L : List α) (h : 0 < L.length) :
    (randIdx L h :
      TimeMT ℕ M (Fin L.length)).run =
    (TimeMT.lift
      (randIdx L h :
        M (Fin L.length))).run := rfl

/-- Erasing time from the timed Quicksort gives the untimed Quicksort.
This follows from the unified definition: the `MonadCost.tick` in
`TimeMT` erases to `pure ()`, matching the no-op `MonadCost` instance.

Uses **functional induction** on `Quicksort`. -/
lemma Quicksort_erasure
    {M} [Monad M] [LawfulMonad M] [RandMonad M]
    (L : List α) :
    TimeM.ret <$>
      (Quicksort L : TimeMT ℕ M (List α)).run =
      (Quicksort L : M (List α)) := by
  induction L using Quicksort.induct
  · -- Base case
    rw [Quicksort.eq_1 (M := TimeMT ℕ M), Quicksort.eq_1 (M := M)]
    simp
  · -- Inductive case
    next head tail ih1 ih2 =>
    rw [Quicksort.eq_2 (M := TimeMT ℕ M) head tail,
        Quicksort.eq_2 (M := M) head tail]
    simp only [TimeMT_erase_bind, TimeMT_randIdx_run, TimeMT_erase_lift,
      MonadCost.tick_timeMT, TimeMT_erase_tick, MonadCost.tick_default, pure_bind]
    simp only [ih1, ih2, TimeMT_erase_pure]

/-- Timed PMF correctness for free. -/
lemma Correctness_Quicksort_Timed_PMF :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      TimeM.ret <$> (Quicksort_PMF_Timed L).run =
        pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  intro L
  obtain ⟨Out, hEq, hSort, hPerm⟩ :=
    Correctness_Quicksort_PMF L
  use Out
  unfold Quicksort_PMF_Timed
  rw [Quicksort_erasure]
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
    (L : List α) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (· < pivot)
    let L2 := rest.filter (· ≥ pivot)
    𝔼_runtime[qs_branch (TimeMT ℕ M) L i] =
    (rest.length : ENNReal) +
      𝔼_runtime[(Quicksort L1 : TimeMT ℕ M _)] +
      𝔼_runtime[(Quicksort L2 : TimeMT ℕ M _)] := by
  intro pivot rest L1 L2
  -- Peel `tick` and the trailing `pure` automatically.
  show expected_cost (inst.toPMF
    (TimeMT.tick rest.length >>=
      fun _ => (Quicksort L1 : TimeMT ℕ M _) >>=
        fun S1 => (Quicksort L2 : TimeMT ℕ M _) >>=
          fun S2 => pure
            (S1 ++ [pivot] ++ S2)).run) = _
  cost_step
  -- Decompose the outer recursive bind, then collapse the inner
  -- continuation `(QS L2 >>= pure)` to `E[QS L2]`.
  rw [expected_cost_toPMF_bind]
  have h_inner : ∀ tm : TimeM ℕ (List α),
      expected_cost
        (inst.toPMF
          ((Quicksort L2 : TimeMT ℕ M _) >>= fun S2 =>
            (pure (tm.ret ++ [pivot] ++ S2) :
              TimeMT ℕ M (List α))).run) =
      expected_cost
        (inst.toPMF (Quicksort L2 : TimeMT ℕ M _).run) := by
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
    𝔼_runtime[(Quicksort [] : TimeMT ℕ M (List α))] = 0 := by
  rw [Quicksort.eq_1]; cost_step

/-!
### Monadic unfolding: inductive step
-/

/-- After applying `toPMF` to `.run` of `Quicksort`
(in `TimeMT`) on a nonempty list, the expected cost is the
uniform average:
`E[cost] = (1/n) * Σ_i (|rest_i| + E[L1_i] + E[L2_i])`
-/
lemma expected_cost_quicksort_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : α) (tail : List α) :
    let L := head :: tail
    𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] =
    (L.length : ENNReal)⁻¹ *
      ∑ i : Fin L.length,
        let pivot := L[i]
        let rest := L.eraseIdx i
        let L1 := rest.filter (· < pivot)
        let L2 := rest.filter (· ≥ pivot)
        ((rest.length : ENNReal) +
          𝔼_runtime[(Quicksort L1 : TimeMT ℕ M _)] +
          𝔼_runtime[(Quicksort L2 : TimeMT ℕ M _)]) := by
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
### Finiteness of expected cost

(The rank-reindexing lemma `nodup_partition_sum` used below is
provided by `ARA.Algorithms.Partition`.)
-/

lemma expected_cost_quicksort_ne_top
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (L : List α) :
    𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] ≠ ⊤ := by
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

/-- The expected cost of `Quicksort` (in timed mode) on a list of
`n` distinct elements is exactly `2(n+1)H(n) − 4n`
comparisons. -/
theorem Expected_Complexity_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (hnd : L.Nodup) :
    𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)] =
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

set_option maxHeartbeats 400000 in
/-- For an arbitrary list (possibly with duplicates), the expected cost
of `Quicksort` is bounded by `L.length.choose 2`. This bound is tight on
the all-equal list `[a, a, …, a]`.

The proof is by strong induction on `L.length`. The inductive step uses
`expected_cost_quicksort_step` to expand into a uniform average over
pivot choices, the IH to bound each recursive call, and `choose_two_add_le`
to combine the two subproblem bounds. -/
theorem Quicksort_Cost_Upper_Bound
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)] ≤ L.length.choose 2 := by
  -- Step 1: reduce to an inequality in `ENNReal`.
  suffices h : 𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] ≤
      ((L.length.choose 2 : ℕ) : ENNReal) by
    have hne : ((L.length.choose 2 : ℕ) : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have := ENNReal.toReal_mono hne h
    simpa using this
  -- Step 2: strong induction on `L.length`.
  suffices h_strong : ∀ n (L : List α), L.length = n →
      𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] ≤ ((n.choose 2 : ℕ) : ENNReal) by
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
            𝔼_runtime[(Quicksort
              (((head :: tail).eraseIdx i).filter
                (· < (head :: tail)[i])) : TimeMT ℕ M _)] +
            𝔼_runtime[(Quicksort
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
              𝔼_runtime[(Quicksort L1 : TimeMT ℕ M _)] +
              𝔼_runtime[(Quicksort L2 : TimeMT ℕ M _)]
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
              𝔼_runtime[(Quicksort
                (((head :: tail).eraseIdx i).filter
                  (· < (head :: tail)[i])) : TimeMT ℕ M _)] +
              𝔼_runtime[(Quicksort
                (((head :: tail).eraseIdx i).filter
                  (· ≥ (head :: tail)[i])) : TimeMT ℕ M _)]) ≤
          ((head :: tail).length : ENNReal) * ((n.choose 2 : ℕ) : ENNReal) := by
        refine le_trans (Finset.sum_le_sum fun i _ => h_summand i) (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      -- Multiply both sides by `(L.length)⁻¹` and cancel.
      have hne_zero : ((head :: tail).length : ENNReal) ≠ 0 := by
        simp
      have hne_top : ((head :: tail).length : ENNReal) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      refine le_trans (mul_le_mul' le_rfl h_sum_le) ?_
      rw [← mul_assoc, ENNReal.inv_mul_cancel hne_zero hne_top, one_mul]

end ARA
