import TimeM
import ARA.Tactics
import ARA.ExpectedCost_TimeMT

/-!
# QuickSort

This module implements a modular version of QuickSort.

We use typeclasses to abstract over the source of randomness:

* `RandMonad` — typeclass for random pivot selection
* `IO` instance — real computable (pseudo-)randomness
* `PMF` instance — noncomputable uniform distribution

The `TimeMT` monad transformer provides a timed variant,
and we show that `RandMonad` lifts automatically through
`TimeMT` via `monadLift`.

## Main results

* `Correctness_Quicksort` — generic correctness for any
  `LawfulRandMonad`: the output is a sorted permutation
* `Expected_Complexity_Quicksort` — the expected number of
  comparisons on a list of `n` distinct elements is exactly
  `2(n+1)H(n) − 4n`
-/

namespace ARA

open ARA
open Cslib.Algorithms.Lean
open List

/-!
## Algorithm definition
-/

/-- The main abstracted QuickSort function, polymorphic
in the random monad `M`. -/
def QuickSort
    {M} [Monad M] [RandMonad M] :
    List ℕ → M (List ℕ)
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

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO: real computable (pseudo-)randomness
instance : RandMonad IO where
  randIdx L hne := do
    let i ← IO.rand 0 (L.length - 1)
    return ⟨i % L.length, Nat.mod_lt i hne⟩

-- IO version (executable)
def QuickSort_IO : List ℕ → IO (List ℕ) := QuickSort

#eval QuickSort_IO
  [0, 1, 22, 43, 46, 45, 43, 45, 45, 67, 89, 789, 8, 656]

-- PMF version (noncomputable specification)
noncomputable def QuickSort_PMF :
    List ℕ → PMF (List ℕ) := QuickSort

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

/-- RandMonad lifts through `TimeMT` via `monadLift`.
This is where we "stack" monads: an abstract monad gets
wrapped in a `TimeMT` to obtain a timed version. -/
instance {M} [Monad M] [RandMonad M] :
    RandMonad (TimeMT ℕ M) where
  randIdx L h := TimeMT.lift (RandMonad.randIdx L h)

/-- Timed QuickSort: charges `rest.length` comparisons
per partition step. -/
def QuickSortTimed
    {M} [Monad M] [RandMonad M] :
    List ℕ → TimeMT ℕ M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      -- each element of `rest` is compared once
      TimeMT.tick rest.length
      let S1 ← QuickSortTimed L1
      let S2 ← QuickSortTimed L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
decreasing_by all_goals grind

-- IO version (executable)
def QuickSortT_IO :
    List ℕ → TimeMT ℕ IO (List ℕ) := QuickSortTimed

#eval (QuickSortT_IO [5, 4, 2, 1, 3, 6, 2, 1, 24, 6]).run

noncomputable def QuickSortT_PMF :
    List ℕ → TimeMT ℕ PMF (List ℕ) := QuickSortTimed

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

Deterministic branch abstractions for the
partition-and-recurse step at a given pivot index.
`qs_branch` is untimed; `qs_branch_timed` is the
timed variant that charges `rest.length` comparisons.
-/

/-- Untimed branch: partition around pivot `L[i]` and
recurse with `QuickSort`. -/
private noncomputable abbrev qs_branch
    (M : Type → Type) [Monad M] [RandMonad M]
    (L : List ℕ) (i : Fin L.length) :
    M (List ℕ) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  let S1 ← QuickSort (rest.filter (· < pivot))
  let S2 ← QuickSort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

/-- Timed branch: the purely deterministic logic executed
after the pivot index `i` is chosen in `QuickSortTimed`.
Charges `rest.length` comparisons via `TimeMT.tick`, then
recurses on both partitions. This separates the
probabilistic pivot selection from the deterministic
partition-and-recurse step. -/
private noncomputable abbrev qs_branch_timed
    (M : Type → Type) [Monad M] [RandMonad M]
    (L : List ℕ) (i : Fin L.length) :
    TimeMT ℕ M (List ℕ) := do
  let pivot := L[i]
  let rest := L.eraseIdx i
  let L1 := rest.filter (· < pivot)
  let L2 := rest.filter (· ≥ pivot)
  TimeMT.tick rest.length
  let S1 ← QuickSortTimed L1
  let S2 ← QuickSortTimed L2
  return (S1 ++ [pivot] ++ S2)

/-!
### Structural decomposition

`QuickSortTimed` on a nonempty list is exactly
`randIdx >>= qs_branch_timed`.
-/

/-- `QuickSortTimed L` decomposes as
`randIdx L >>= qs_branch_timed M L`. -/
private lemma quicksort_timed_eq_bind
    {M} [Monad M] [RandMonad M]
    (head : ℕ) (tail : List ℕ) :
    (QuickSortTimed (head :: tail) :
      TimeMT ℕ M (List ℕ)) =
    TimeMT.lift
      (RandMonad.randIdx (head :: tail) (by simp) :
        M _) >>=
      fun idx => qs_branch_timed M
        (head :: tail) idx := by
  rw [QuickSortTimed.eq_2 head tail]
  rfl

/-!
### Generic correctness theorem
-/

/-- For any `LawfulRandMonad`, `QuickSort L` produces a
single deterministic output that is sorted and a
permutation of `L`. -/
lemma Correctness_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [LawfulRandMonad M] :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      LawfulRandMonad.toPMF
        (QuickSort L : M (List ℕ)) =
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
            (qs_branch M L i) =
            pure Out ∧
          Out.SortedLE ∧ Out.Perm L := by
      intro i
      obtain ⟨O1, h1, s1, p1⟩ := ihL1 i
      obtain ⟨O2, h2, s2, p2⟩ := ihL2 i
      use O1 ++ [L[i]] ++ O2
      split_ands
      · unfold qs_branch; unfold_do
        simp only [LawfulRandMonad.toPMF_bind,
          LawfulRandMonad.toPMF_pure]
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
    -- of sorted permutation), so the PMF is a point
    -- mass.
    obtain ⟨Output, h0, hS, hP⟩ :=
      h_step ⟨0, by grind⟩
    refine ⟨Output, ?_, hS, hP⟩
    have : Nonempty (Fin L.length) :=
      ⟨⟨0, by grind⟩⟩
    calc LawfulRandMonad.toPMF
          (QuickSort L : M (List ℕ))
        = LawfulRandMonad.toPMF
            (RandMonad.randIdx L (by grind) >>=
              fun idx =>
                qs_branch M L idx) := by
          unfold qs_branch
          rw [QuickSort.eq_2 head tail]
      _ = (PMF.uniformOfFintype
            (Fin L.length)).bind
            (fun idx =>
              LawfulRandMonad.toPMF
                (qs_branch M L idx)) := by
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
-- Free Proof: Timed QuickSortT_PMF
-- ----------------------------------------

/-! ### Helper lemmas for TimeMT erasure -/

@[simp] lemma TimeMT_randIdx_run
    {M} [Monad M] [RandMonad M]
    (L : List ℕ) (h : 0 < L.length) :
    (RandMonad.randIdx L h :
      TimeMT ℕ M (Fin L.length)).run =
    (TimeMT.lift
      (RandMonad.randIdx L h :
        M (Fin L.length))).run := rfl

/-- Tracking time doesn't change the sorting logic. -/
lemma QuickSortTimed_erasure
    {M} [Monad M] [LawfulMonad M] [RandMonad M]
    (L : List ℕ) :
    TimeM.ret <$>
      (QuickSortTimed L :
        TimeMT ℕ M (List ℕ)).run =
      QuickSort L := by
  induction L using QuickSort.induct
  · -- Base case
    rw [QuickSort.eq_1, QuickSortTimed.eq_1]; simp
  · -- Inductive case
    next head tail ih1 ih2 =>
      rw [QuickSort.eq_2 head tail,
        QuickSortTimed.eq_2 head tail]
      simp only [TimeMT_erase_bind,
        TimeMT_randIdx_run, TimeMT_erase_lift,
        TimeMT_erase_tick, TimeMT_erase_pure]
      simp only [ih1, ih2]
      simp only [pure_bind]

/-- Timed PMF correctness for free. -/
lemma Correctness_QuicksortTimed_PMF :
    ∀ L : List ℕ, ∃ Output : List ℕ,
      TimeM.ret <$> (QuickSortT_PMF L).run =
        pure Output ∧
      Output.SortedLE ∧ Output.Perm L := by
  intro L
  obtain ⟨Out, hEq, hSort, hPerm⟩ :=
    Correctness_Quicksort_PMF L
  use Out
  unfold QuickSortT_PMF
  rw [QuickSortTimed_erasure]
  exact ⟨hEq, hSort, hPerm⟩

-- ----------------------------------------
-- Generic Complexity Proof
-- ----------------------------------------

/-!
### Closed-form cost function
-/

/-- The `n`-th harmonic number
`H(n) = Σ_{k=1}^{n} 1/k`. -/
def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + (1 / (n + 1))

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
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold expected_qs_cost
    have H_step : harmonic (n + 1) =
        harmonic n + 1 / ((n : ℚ) + 1) := by
      change harmonic n + 1 / (n + 1 : ℚ) = _
      rfl
    rw [H_step]; push_cast
    have h_nz : (n : ℚ) + 1 ≠ 0 := by positivity
    generalize harmonic n = H
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
### Branch cost lemma

The expected cost of the deterministic branch
`qs_branch_timed M L i` is the tick cost plus the
expected costs of the two recursive calls.
-/

/-- The expected cost of `qs_branch_timed M L i` is
`rest.length + E[QS L1] + E[QS L2]`, where `L1` and `L2`
are the two partitions around pivot `L[i]`. -/
private lemma expected_cost_tm_qs_branch_timed
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List ℕ) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (· < pivot)
    let L2 := rest.filter (· ≥ pivot)
    expected_cost_tm
      (inst.toPMF
        (qs_branch_timed M L i).run) =
    (rest.length : ENNReal) +
      expected_cost_tm
        (inst.toPMF
          (QuickSortTimed L1 :
            TimeMT ℕ M (List ℕ)).run) +
      expected_cost_tm
        (inst.toPMF
          (QuickSortTimed L2 :
            TimeMT ℕ M (List ℕ)).run) := by
  intro pivot rest L1 L2
  -- Step 1: peel off the tick
  show expected_cost_tm (inst.toPMF
    (TimeMT.tick rest.length >>=
      fun _ => QuickSortTimed L1 >>=
        fun S1 => QuickSortTimed L2 >>=
          fun S2 => pure
            (S1 ++ [pivot] ++ S2)).run) = _
  rw [expected_cost_tm_toPMF_tick_bind]
  -- Step 2: peel off QS(L1)
  rw [expected_cost_tm_toPMF_bind]
  -- Step 3: the inner continuation cost is just E[QS L2]
  have h_inner : ∀ tm : TimeM ℕ (List ℕ),
      expected_cost_tm
        (inst.toPMF
          (QuickSortTimed L2 >>= fun S2 =>
            (pure (tm.ret ++ [pivot] ++ S2) :
              TimeMT ℕ M (List ℕ))).run) =
      expected_cost_tm
        (inst.toPMF
          (QuickSortTimed L2).run) := by
    intro tm
    rw [expected_cost_tm_toPMF_bind]
    simp only [expected_cost_tm_toPMF_pure,
      mul_zero, tsum_zero, add_zero]
  simp only [h_inner]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe,
    one_mul]
  ring

/-!
### Monadic unfolding: base case
-/

lemma expected_cost_tm_quicksort_nil
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] :
    expected_cost_tm
      (inst.toPMF
        (QuickSortTimed ([] : List ℕ) :
          TimeMT ℕ M (List ℕ)).run) = 0 := by
  rw [QuickSortTimed.eq_1]
  simp only [TimeMT.run_pure, inst.toPMF_pure]
  change expected_cost_tm
    (PMF.pure ⟨[], 0⟩) = 0
  simp [expected_cost_tm_pure_val]

/-!
### Monadic unfolding: inductive step

For `L = head :: tail`, `QuickSortTimed` picks a uniform
pivot, partitions, ticks `rest.length`, and recurses.
After applying `toPMF`, the expected cost decomposes as a
uniform average over pivot choices.

The proof proceeds in two clean steps:
1. Show `QuickSortTimed L = randIdx >>= qs_branch_timed`
2. Apply the uniform average from `randIdx`, then
   integrate the branch cost lemma.
-/

/-- After applying `toPMF` to `.run` of `QuickSortTimed`
on a nonempty list, the expected cost is the uniform
average:
`E[cost] = (1/n) * Σ_i (|rest_i| + E[L1_i] + E[L2_i])`
-/
lemma expected_cost_tm_quicksort_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : ℕ) (tail : List ℕ) :
    let L := head :: tail
    expected_cost_tm
      (inst.toPMF
        (QuickSortTimed L :
          TimeMT ℕ M (List ℕ)).run) =
    (L.length : ENNReal)⁻¹ *
      ∑ i : Fin L.length,
        let pivot := L[i]
        let rest := L.eraseIdx i
        let L1 := rest.filter (· < pivot)
        let L2 := rest.filter (· ≥ pivot)
        ((rest.length : ENNReal) +
          expected_cost_tm
            (inst.toPMF
              (QuickSortTimed L1 :
                TimeMT ℕ M (List ℕ)).run) +
          expected_cost_tm
            (inst.toPMF
              (QuickSortTimed L2 :
                TimeMT ℕ M (List ℕ)).run)) := by
  intro L
  -- Step 1: decompose as randIdx >>= qs_branch_timed
  conv_lhs =>
    rw [show L = head :: tail from rfl]
  rw [quicksort_timed_eq_bind head tail]
  -- Step 2: apply lift-bind to separate randomness
  rw [expected_cost_tm_toPMF_lift_bind]
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
  exact expected_cost_tm_qs_branch_timed L i

/-!
### Partition size lemma for distinct lists

For a list with distinct elements, summing
`f(|L1_i|) + f(|L2_i|)` over all pivot indices `i`
gives `Σ_k (f(k) + f(n−1−k))`, because choosing the
element of rank `k` as pivot gives exactly `k` elements
less than it and `n−1−k` elements `≥` it.
-/

open Finset in
/-- Reindexing partition sizes by rank for nodup
lists. -/
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
  -- Step 1: rank(i) = |{j ≠ i | L[j] < L[i]}|
  have h_rank : ∀ i : Fin L.length,
      ((L.eraseIdx i).filter
        (· < L[i])).length =
        (Finset.filter (fun x => L[x] < L[i])
          (Finset.univ.erase i)).card := by
    intro i
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
  -- Step 2: complement rank
  have h_complement_rank :
      ∀ i : Fin L.length,
      ((L.eraseIdx i).filter
        (· ≥ L[i])).length =
        L.length - 1 -
          (Finset.filter
            (fun x => L[x] < L[i])
            (Finset.univ.erase i)).card := by
    intro i
    have h_split :
      ((L.eraseIdx i).filter
        (· ≥ L[i])).length +
        ((L.eraseIdx i).filter
          (· < L[i])).length =
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
      (by linarith [h_rank i])
  -- Step 3: rank is a bijection, so reindex
  have h_bijection :
    Finset.image
      (fun i : Fin L.length =>
        (Finset.filter
          (fun x => L[x] < L[i])
          (Finset.univ.erase i)).card)
      (Finset.univ : Finset (Fin L.length)) =
    Finset.range L.length := by
    refine Finset.eq_of_subset_of_card_le
      (Finset.image_subset_iff.mpr ?_) ?_
      <;> simp_all +decide
    · grind
    · rw [Finset.card_image_of_injective]
        <;> norm_num [Function.Injective]
      intro i j h; contrapose! h
      simp_all +decide [Finset.filter_erase]
      cases lt_or_gt_of_ne
        (show L[i] ≠ L[j] from fun h' =>
          h <| Fin.ext <| by
            have :=
              List.nodup_iff_injective_get.mp
                hnd h'
            aesop) <;> simp_all +decide
      · refine ne_of_lt
          (Finset.card_lt_card ?_)
        simp_all +decide
          [Finset.ssubset_def,
           Finset.subset_iff]
        exact ⟨fun x hx =>
          lt_trans hx ‹_›,
          i, ‹_›, le_rfl⟩
      · refine ne_of_gt
          (Finset.card_lt_card ?_)
        simp_all +decide
          [Finset.ssubset_def,
           Finset.subset_iff]
        exact ⟨fun x hx =>
          lt_trans hx ‹_›,
          j, ‹_›, le_rfl⟩
  have h_reindex :
    ∑ i : Fin L.length,
      (f ((Finset.filter
            (fun x => L[x] < L[i])
            (Finset.univ.erase i)).card) +
       f (L.length - 1 -
            (Finset.filter
              (fun x => L[x] < L[i])
              (Finset.univ.erase i)).card)) =
    ∑ k ∈ Finset.range L.length,
      (f k + f (L.length - 1 - k)) := by
    rw [← h_bijection, Finset.sum_image]
    intro i hi j hj hij
    have := Finset.card_image_iff.mp
      (by aesop :
        Finset.card
          (Finset.image
            (fun i : Fin L.length =>
              # (Finset.filter
                (fun x : Fin L.length =>
                  L[x] < L[i])
                (Finset.erase
                  Finset.univ i)))
            Finset.univ) =
          Finset.card Finset.univ)
    aesop
  simp_all +decide [Finset.sum_range]

/-!
### Finiteness of expected cost

Uses the branch abstraction to cleanly decompose the
inductive case: the expected cost of
`randIdx >>= qs_branch_timed` is finite because each
branch cost is a finite sum of finite recursive costs.
-/

lemma expected_cost_tm_quicksort_ne_top
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (L : List ℕ) :
    expected_cost_tm
      (inst.toPMF
        (QuickSortTimed L :
          TimeMT ℕ M (List ℕ)).run) ≠ ⊤ := by
  induction' n : L.length
    using Nat.strong_induction_on
    with n ih generalizing L
  rcases L with (_ | ⟨head, tail⟩)
  -- Base case: empty list
  · simp [expected_cost_tm_quicksort_nil]
  -- Inductive case: use step decomposition
  · rw [expected_cost_tm_quicksort_step]
    simp_all +decide
    rw [ENNReal.mul_eq_top]; norm_num
    grind +revert

/-!
### The main theorem

**Note**: The formula `2(n+1)H(n) − 4n` requires
`L.Nodup` (distinct elements). For lists with duplicates,
the expected cost differs (e.g. `[1,1,1]` costs 3 but
`C(3) = 8/3`).
-/

/-- The expected cost of `QuickSortTimed` on a list of
`n` distinct elements is exactly `2(n+1)H(n) − 4n`
comparisons. -/
theorem Expected_Complexity_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    (expected_cost_tm
      (inst.toPMF
        (QuickSortTimed L :
          TimeMT ℕ M (List ℕ)).run)).toReal =
    (expected_qs_cost L.length : ℚ) := by
  induction' n : L.length
    using Nat.strong_induction_on
    with n ih generalizing L
  cases' L with head tail
    <;> simp_all +decide
      [expected_cost_tm_quicksort_step]
  · subst n
    norm_num [expected_cost_tm_quicksort_nil]
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
            [expected_cost_tm_quicksort_ne_top]
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

end ARA
