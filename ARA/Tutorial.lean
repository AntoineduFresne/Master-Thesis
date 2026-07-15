/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.ExpectedCost
import ARA.Correctness
import ARA.Algorithms.Partition

/-!
# Tutorial — verify your first randomized algorithm

This file is a template: copy it, replace the toy algorithm with
yours, and follow the numbered steps. Everything that is not marked
"the mathematics" is boilerplate that the framework automates.

## The recipe

1. **Algorithm** — write it *once*, polymorphic over
   `{M} [Monad M] [RandMonad M] [MonadCost ℕ M]`. Draw randomness with
   `randIdx`/`randFin`, charge cost with `MonadCost.tick`, and let
   `termination_by`/`decreasing_by grind` handle recursion.
2. **Instances for free** — the same definition runs in `IO`
   (execute it!), specifies a distribution in `PMF`, and carries a
   clock in `TimeMT ℕ _`. Sanity-check with `#eval`.
3. **Branch + decomposition** — an `abbrev` for the per-pivot branch
   and two one-line `_eq_bind` lemmas exposing the pivot choice.
4. **Spec + transport lemmas** — define the specification and prove
   how it commutes with one branch (tag `@[spec_transport]`).
   *This is the only real mathematics.*
5. **Correctness** — `induction … using yourAlgo.induct`, expose the
   pivot, collapse with `toPMF_randIdx_bind_dirac`, finish with
   `dirac_finish`.

Note: For Monte-Carlo algorithms (output genuinely random, e.g. Karger),
replace step 5's collapse by the distributional primitives
`support_toPMF_randIdx_bind` / `le_toPMF_randIdx_bind` and state
correctness as a support fact plus a success-probability bound.

6. **Expected cost** — branch cost by `cost_step`, step lemma by
   `expected_cost_uniform_step`, then solve the recurrence along
   `yourAlgo.induct`.

## Example

`RandMax`: scan a list in *random* order, one comparison per round,
returning the maximum. Output is deterministic (Las Vegas), cost is
exactly `n` ticks — small enough that every proof fits on a screen.
-/

namespace ARA

open Cslib.Algorithms.Lean

variable {α : Type} [LinearOrder α] [Inhabited α]

/-!
## Step 1 — the algorithm, written once

Randomness (`randIdx`), cost (`tick`), and recursion live in any monad
`M` with the two capability classes. Nothing about probabilities or
clocks appears here.
-/

/-- Find the maximum by repeatedly removing a uniformly random element
and comparing it against the maximum of the rest (one tick per
comparison). -/
def RandMax {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → M α
  | [] => return default
  | L@(_ :: _) => do
      let idx ← randIdx L
      MonadCost.tick 1
      let m ← RandMax (L.eraseIdx idx)
      return max L[idx] m
  termination_by L => L.length
  decreasing_by all_goals grind

/-!
## Step 2 — instances for free

One definition, four readings. Run the executable ones with `#eval`.
-/

def RandMax_IO : List ℕ → IO ℕ := RandMax

#eval RandMax_IO [3, 1, 4, 1, 5, 9, 2, 6]        -- 9

noncomputable def RandMax_PMF : List ℕ → PMF ℕ := RandMax

def RandMax_IO_Timed : List ℕ → TimeMT ℕ IO ℕ := RandMax

#eval (RandMax_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6]).run  -- ret 9, time 8

/-!
## Step 3 — branch + decomposition (pure boilerplate)

Abstract the deterministic work done at a fixed pivot index; the
algorithm is then literally `randIdx >>= branch`, which is the shape
all framework lemmas consume. Both proofs are one rewrite with the
equation lemma Lean generated from the definition.
-/

/-- The work at a fixed pivot index `i`. -/
private abbrev randMax_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List α) (i : Fin L.length) : M α := do
  MonadCost.tick 1
  let m ← RandMax (L.eraseIdx i)
  return max L[i] m

private lemma randMax_eq_bind
    {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (head : α) (tail : List α) :
    (RandMax (head :: tail) : M α) =
    randIdx (head :: tail) >>=
      fun i => randMax_branch M (head :: tail) i := by
  rw [RandMax.eq_2]

private lemma randMax_timed_eq_bind
    {M} [Monad M] [RandMonad M]
    (head : α) (tail : List α) :
    (RandMax (head :: tail) : TimeMT ℕ M α) =
    TimeMT.lift (randIdx (head :: tail) : M _) >>=
      fun i => randMax_branch (TimeMT ℕ M) (head :: tail) i := by
  rw [RandMax.eq_2 (M := TimeMT ℕ M)]
  rfl

/-!
## Step 4 — the specification and its transport lemma

This is the mathematics. The spec is what the algorithm should
compute; the transport lemma says how the spec interacts with one
branch of the recursion. Everything else in the file is machinery.
-/

/-- Specification: the maximum of a list (with `default` for `[]`). -/
def listMax (L : List α) : α := L.foldr max default

private instance : LeftCommutative (max : α → α → α) :=
  max_left_commutative

/-- Transport: removing the chosen element and re-inserting it via
`max` recovers the maximum — because `max`-folds are invariant under
permutation, and `L` permutes to `L[i] :: L.eraseIdx i`.

Stated with a ℕ index (the `simp`-normal form of `L[i]`), so that
`dirac_finish` can apply it. -/
@[spec_transport]
private lemma listMax_branch (L : List α) (i : ℕ) (h : i < L.length) :
    max L[i] (listMax (L.eraseIdx i)) = listMax L := by
  unfold listMax
  rw [(perm_getElem_cons_eraseIdx L ⟨i, h⟩).foldr_eq default, List.foldr_cons]
  rfl

/-!
## Step 5 — Dirac correctness

The output never depends on the coin flips, so the distribution is a
point mass at the spec. The proof is the recipe verbatim: functional
induction, expose the pivot, collapse, `dirac_finish`.
-/

/-- **Correctness.** For any lawful random monad, `RandMax` returns
exactly `listMax L` — the pivot choices are invisible. -/
theorem Correctness_RandMax
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    LawfulRandMonad.toPMF
      (@RandMax _ _ _ M _ _ instMonadCostDefault L) =
      PMF.pure (listMax L) := by
  induction L using RandMax.induct with
  | case1 =>
    rw [RandMax.eq_1]
    simp only [LawfulRandMonad.toPMF_pure]
    rfl
  | case2 head tail ih =>
    rw [randMax_eq_bind]
    refine toPMF_randIdx_bind_dirac fun i => ?_
    unfold randMax_branch
    dirac_finish

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem randMax_correct (L : List α) :
    (RandMax L : PMF α) = PMF.pure (listMax L) :=
  Correctness_RandMax (M := PMF) L

/-!
## Step 6 — expected cost

Three lemmas, each following a fixed pattern:

* the **branch cost** is read off by `cost_step` (the trailing
  `return …` is free by `expected_cost_toPMF_bind_pure`);
* the **step lemma** is `expected_cost_uniform_step` plus the branch
  cost — this is the recurrence `E(n) = (1/n) Σᵢ (1 + E(n−1))`;
* the **closed form** solves the recurrence along `RandMax.induct`.
-/

private lemma expected_cost_randMax_branch
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) (i : Fin L.length) :
    𝔼_runtime[randMax_branch (TimeMT ℕ M) L i] =
    1 + 𝔼_runtime[RandMax (L.eraseIdx i) | M] := by
  show expected_cost (inst.toPMF
    ((TimeMT.tick 1 >>= fun _ =>
      (RandMax (L.eraseIdx i) : TimeMT ℕ M α) >>= fun m =>
        pure (max L[i] m)).run)) = _
  cost_step
  rw [Nat.cast_one]

private lemma expected_cost_randMax_step
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (head : α) (tail : List α) :
    𝔼_runtime[RandMax (head :: tail) | M] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length,
        (1 + 𝔼_runtime[RandMax ((head :: tail).eraseIdx i) | M]) := by
  rw [randMax_timed_eq_bind head tail, expected_cost_uniform_step]
  congr 1
  exact Finset.sum_congr rfl fun i _ => expected_cost_randMax_branch (head :: tail) i

private lemma expected_cost_randMax_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_runtime[RandMax ([] : List α) | M] = 0 := by
  rw [RandMax.eq_1, expected_cost_toPMF_pure]

/-- **Exact expected cost.** `RandMax` performs exactly `n` comparisons
in expectation (in fact, always): one per round, `n` rounds. -/
theorem Expected_Complexity_RandMax
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼_runtime[RandMax L | M] = (L.length : ENNReal) := by
  induction L using RandMax.induct with
  | case1 =>
    rw [expected_cost_randMax_nil]
    simp
  | case2 head tail ih =>
    rw [expected_cost_randMax_step head tail]
    -- Every branch recurses on `tail.length` elements…
    have hterm : ∀ i : Fin (head :: tail).length,
        1 + 𝔼_runtime[RandMax ((head :: tail).eraseIdx i) | M] =
        ((head :: tail).length : ENNReal) := by
      intro i
      rw [ih i, length_eraseIdx_cons]
      simp only [List.length_cons]
      push_cast
      ring
    -- …so the average of `n` copies of `n` is `n`.
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

/-!
## Where to go from here

* Case splits in a branch? `dirac_finish` handles guards it can read
  off the hypotheses; orient your `@[spec_transport]` lemmas
  left-to-right ("branch value = spec") and close stubborn cases
  manually after `dirac_step` + `split_ifs` — see
  `Correctness_Quickselect`.
* Non-uniform recursion (branch size depends on the pivot)? Reindex
  the step-lemma sum by pivot rank with `nodup_partition_sum₂` — see
  the exact cost proofs of `Quicksort` and `Quickselect`.
* Upper bounds instead of exact formulas? Stay in `ℝ≥0∞` and close
  with `uniform_avg_le`; get finiteness for free from the bound and
  descend to `ℝ` with `toReal_uniform_avg` — see
  `Quickselect_Cost_Upper_Bound_ennreal`.
* Monte-Carlo correctness? `support_toPMF_randIdx_bind` and
  `le_toPMF_randIdx_bind` in `ARA.Correctness` — see `Karger`.
-/

end ARA
