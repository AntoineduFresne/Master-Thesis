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
* `Quicksort_Cost_Upper_Bound` — For arbitrary lists (possibly with
  duplicates), bounds the expected cost by `C(n,2)`, tight on
  all-equal inputs. Its `ℝ≥0∞` core also supplies the finiteness
  fact needed by the exact-formula proof.
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

/-!
### Abbreviations

Deterministic branch abstraction for the
partition-and-recurse step at a given pivot index.
-/

/-- Branch: partition around pivot `L[i]` and
recurse with `Quicksort`. Used for both correctness
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
## Complexity

The expected cost obeys
`E[n] = (n-1) + (1/n) Σ_i (E[L1_i] + E[L2_i])`. Two results follow,
both by functional induction on `Quicksort`:

* bounding both recursive calls via discrete convexity of `C(·,2)`
  gives `E ≤ C(n,2)` for arbitrary lists (tight on all-equal inputs),
  which also yields finiteness of the expected cost;
* for distinct lists, rank reindexing turns the sum over pivots into
  the harmonic recurrence, which solves exactly to `2(n+1)H(n) − 4n`
  (`Expected_Complexity_Quicksort`).

The upper bound is stated in `ℝ≥0∞`, where no summability bookkeeping
is needed; the exact formula descends to `ℝ` via `toReal`, with
finiteness supplied by the `C(n,2)` bound.
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

/-- The empty list costs nothing. -/
lemma expected_cost_quicksort_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_runtime[(Quicksort [] : TimeMT ℕ M (List α))] = 0 := by
  rw [Quicksort.eq_1]; cost_step

/-- The expected cost of `Quicksort` on a nonempty list is the uniform
average of the branch costs:
`E[cost] = (1/n) * Σ_i (|rest_i| + E[L1_i] + E[L2_i])`. -/
lemma expected_cost_quicksort_step
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (head : α) (tail : List α) :
    𝔼_runtime[(Quicksort (head :: tail) : TimeMT ℕ M _)] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) :
            TimeMT ℕ M _)] +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])) :
            TimeMT ℕ M _)]) := by
  rw [quicksort_timed_eq_bind head tail]
  -- Separate the uniform pivot choice from the branch costs.
  show expected_cost (inst.toPMF (TimeMT.lift (randIdx (head :: tail) : M _) >>=
    fun idx => qs_branch (TimeMT ℕ M) (head :: tail) idx).run) = _
  cost_step
  rw [inst.toPMF_randIdx]
  have hne : Nonempty (Fin (head :: tail).length) := ⟨⟨0, by grind⟩⟩
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [Finset.mul_sum]
  congr 1; ext i; congr 1
  exact expected_cost_qs_branch (head :: tail) i

/-!
### The `C(n,2)` bound for arbitrary lists

The closed-form `2(n+1)H(n) − 4n` requires `L.Nodup` because duplicates
shift the partition distribution. For a list with repeated keys, the
worst case is all-equal inputs `L = [a, a, …, a]`:

  pivot = a, `L1 = []`, `L2 = rest` (length `n-1`, again all `a`)

so the recurrence degenerates to `T(n) = (n-1) + T(n-1)` and yields
`T(n) = n(n-1)/2 = C(n,2)` deterministically. This is the worst case
across all inputs and pivot sequences, so the expected cost on any list
is bounded by `C(n,2)`. Its `ℝ≥0∞` form also provides finiteness of
the expected cost for free. -/

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
/-- **`ℝ≥0∞` core of the upper bound.** For an arbitrary list (possibly
with duplicates), the expected cost of `Quicksort` is bounded by
`L.length.choose 2`. Tight on the all-equal list `[a, a, …, a]`. -/
theorem Quicksort_Cost_Upper_Bound_ennreal
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] ≤
      ((L.length.choose 2 : ℕ) : ENNReal) := by
  induction L using Quicksort.induct with
  | case1 =>
    rw [expected_cost_quicksort_nil]
    exact bot_le
  | case2 head tail ih1 ih2 =>
    rw [expected_cost_quicksort_step head tail]
    -- The recursive calls act on complementary parts of `rest`, so
    -- convexity of `C(·,2)` bounds their joint cost by `C(tail.length, 2)`.
    have hbound : ∀ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) :
            TimeMT ℕ M _)] +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])) :
            TimeMT ℕ M _)]) ≤
        ((tail.length : ENNReal) + ((tail.length.choose 2 : ℕ) : ENNReal)) := by
      intro i
      have hrest : (((head :: tail).eraseIdx i).length) = tail.length := by
        have hi := i.isLt
        simp only [List.length_cons] at hi
        simp [List.length_eraseIdx, Nat.lt_succ_iff.mp hi]
      have hsplit : (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length +
          (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])).length =
          tail.length := by
        rw [length_filter_lt_ge]
        exact hrest
      have hchoose : ((((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length).choose 2 +
          ((((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])).length).choose 2 ≤
          tail.length.choose 2 := by
        rw [← hsplit]
        exact choose_two_add_le _ _
      rw [add_assoc,
        show ((((head :: tail).eraseIdx i).length : ENNReal)) = (tail.length : ENNReal)
          from by rw [hrest]]
      refine add_le_add le_rfl (le_trans (add_le_add (ih1 i) (ih2 i)) ?_)
      rw [← Nat.cast_add]
      exact Nat.cast_le.mpr hchoose
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

/-- For an arbitrary list (possibly with duplicates), the expected cost of
`Quicksort` is at most `C(n,2)` comparisons. Real-valued corollary of
`Quicksort_Cost_Upper_Bound_ennreal`. -/
theorem Quicksort_Cost_Upper_Bound
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)] ≤ L.length.choose 2 := by
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _)
    (Quicksort_Cost_Upper_Bound_ennreal (M := M) L)
  simpa using this

/-- Finiteness of the expected cost — a free corollary of the `C(n,2)`
bound, no separate induction needed. Feeds the `toReal` steps of the
exact-formula theorem below. -/
lemma expected_cost_quicksort_ne_top
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M] (L : List α) :
    𝔼_runtime[(Quicksort L : TimeMT ℕ M _)] ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (Quicksort_Cost_Upper_Bound_ennreal L)

/-!
### The exact expected cost for distinct lists

We reuse Mathlib's harmonic number
`harmonic n = ∑ i ∈ Finset.range n, (↑(i + 1))⁻¹`
(`Mathlib.NumberTheory.Harmonic.Defs`). The formula `2(n+1)H(n) − 4n`
requires `L.Nodup`: duplicates shift the partition distribution
(see the `C(n,2)` section above for the degenerate worst case).
-/

/-- The exact expected number of comparisons for
Quicksort on a list of `n` distinct elements:
`2(n+1)H(n) − 4n`. -/
def expected_qs_cost (n : ℕ) : ℚ :=
  2 * (n + 1) * harmonic n - 4 * n

@[simp] lemma expected_qs_cost_zero :
    expected_qs_cost 0 = 0 := by
  simp [expected_qs_cost, harmonic]

@[simp] lemma expected_qs_cost_one :
    expected_qs_cost 1 = 0 := by
  simp [expected_qs_cost, harmonic]; norm_num

/-- Summation identity for the recurrence:
`2 Σ_{i<n} C(i) = n·(C(n) − n + 1)`. -/
lemma expected_qs_sum_helper (n : ℕ) :
    (2 : ℚ) * ∑ i ∈ Finset.range n, expected_qs_cost i =
    (n : ℚ) * (expected_qs_cost n - (n : ℚ) + 1) := by
  induction n with
  | zero => simp [expected_qs_cost, harmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    unfold expected_qs_cost
    rw [harmonic_succ]; push_cast
    have h_nz : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp; ring

set_option maxHeartbeats 400000 in
/-- **Exact expected complexity of Quicksort.** Sorting a list of `n`
distinct elements costs exactly `2(n+1)H(n) − 4n` comparisons in
expectation. -/
theorem Expected_Complexity_Quicksort
    {M} [Monad M] [LawfulMonad M]
    [inst : LawfulRandMonad M]
    (L : List α) (hnd : L.Nodup) :
    𝔼ℝ_runtime[(Quicksort L : TimeMT ℕ M _)] =
    (expected_qs_cost L.length : ℚ) := by
  revert hnd
  induction L using Quicksort.induct with
  | case1 =>
    intro _
    rw [expected_cost_quicksort_nil]
    simp
  | case2 head tail ih1 ih2 =>
    intro hnd
    rw [expected_cost_quicksort_step head tail]
    -- Each summand is finite (from the `C(n,2)` bound), so `toReal`
    -- distributes through the average.
    have hne : ∀ i : Fin (head :: tail).length,
        ((((head :: tail).eraseIdx i).length : ENNReal) +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) :
            TimeMT ℕ M _)] +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])) :
            TimeMT ℕ M _)]) ≠ ⊤ := fun i =>
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,
          expected_cost_quicksort_ne_top _⟩,
        expected_cost_quicksort_ne_top _⟩
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun i _ => hne i)]
    have hrest_nat : ∀ i : Fin (head :: tail).length,
        (((head :: tail).eraseIdx i).length) = tail.length := by
      intro i
      have hi := i.isLt
      simp only [List.length_cons] at hi
      simp [List.length_eraseIdx, Nat.lt_succ_iff.mp hi]
    -- Rewrite each summand with the IH (in `ℝ`).
    have hterm : ∀ i : Fin (head :: tail).length,
        (((((head :: tail).eraseIdx i).length : ENNReal) +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])) :
            TimeMT ℕ M _)] +
          𝔼_runtime[(Quicksort
            (((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])) :
            TimeMT ℕ M _)]).toReal) =
        (tail.length : ℝ) +
          ((expected_qs_cost
            ((((head :: tail).eraseIdx i).filter (· < (head :: tail)[i])).length) : ℚ) : ℝ) +
          ((expected_qs_cost
            ((((head :: tail).eraseIdx i).filter (· ≥ (head :: tail)[i])).length) : ℚ) : ℝ) := by
      intro i
      rw [ENNReal.toReal_add
          (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,
            expected_cost_quicksort_ne_top _⟩)
          (expected_cost_quicksort_ne_top _),
        ENNReal.toReal_add (ENNReal.natCast_ne_top _)
          (expected_cost_quicksort_ne_top _),
        ENNReal.toReal_natCast, hrest_nat i,
        ih1 i ((hnd.eraseIdx _).filter _), ih2 i ((hnd.eraseIdx _).filter _)]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    -- Reindex by rank (`|L1_i| = rank i` for nodup lists).
    rw [nodup_partition_sum₂ (head :: tail) hnd
      (fun a b => (tail.length : ℝ) + ((expected_qs_cost a : ℚ) : ℝ) +
        ((expected_qs_cost b : ℚ) : ℝ))]
    rw [Fin.sum_univ_eq_sum_range
      (fun r => (tail.length : ℝ) + ((expected_qs_cost r : ℚ) : ℝ) +
        ((expected_qs_cost ((head :: tail).length - 1 - r) : ℚ) : ℝ))]
    simp only [List.length_cons]
    -- Split the sum; the reflected second cost sum equals the first.
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul,
      Finset.sum_range_reflect
        (fun r => ((expected_qs_cost r : ℚ) : ℝ)) (tail.length + 1),
      show (∑ r ∈ Finset.range (tail.length + 1),
          ((expected_qs_cost r : ℚ) : ℝ)) =
        ((∑ r ∈ Finset.range (tail.length + 1),
          expected_qs_cost r : ℚ) : ℝ) from by push_cast; rfl]
    -- Apply the summation identity and close with field arithmetic.
    have hsum : (∑ r ∈ Finset.range (tail.length + 1), expected_qs_cost r) =
        ((tail.length + 1) *
          (expected_qs_cost (tail.length + 1) - (tail.length + 1) + 1)) / 2 := by
      have h := expected_qs_sum_helper (tail.length + 1)
      push_cast at h
      linarith
    rw [hsum]
    have hn1 : ((tail.length : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end ARA
