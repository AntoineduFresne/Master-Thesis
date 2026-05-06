import ARA.Tactics
import TimeM

/-!
# QuickSort

This module implement a modular versions of QuickSort.

We are using typeclasses to abstract over the type of randomness.

`RandMonad` is the typeclass for the randomness, and we give two instances:
- `IO` for real computable (pseudo-)randomness
- `PMF` for noncomputable randomness with uniform distribution over valid indices

We are also using the `TimeMT` monad transformer to get a timed version of QuickSort,
and we show that `RandMonad` lifts automatically through `TimeMT` via `monadLift`.

Finally, we prove the correctness of the PMF version of QuickSort (which implies
the correctness of all versions since they share the same code?).
-/

namespace ARA

/-
Typeclasses to abstract over the type of randomness
(choosing a pivot index).
-/
class RandMonad (M : Type → Type) [Monad M] where
  -- Given a nonempty list, pick a random valid index
  randIdx {α} : (L : List α) → 0 < L.length → M (Fin L.length)

-- The main abstracted QuickSort function
def QuickSort {M} [Monad M] [RandMonad M] : List ℕ → M (List ℕ)
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

-- --------------------------------------
-- Different instance of "randomness"
-- --------------------------------------

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

-- ---------------------------------------
-- Monad transformer version (timed)
-- ---------------------------------------

open Cslib.Algorithms.Lean
#check TimeMT

/--
RandMonad lifts automatically through TimeMT via monadLift
This is where we "stack" monads: an abstract monad get wrapped up
in a TimeMT to get a timed version of the same monad.
-/
instance {M} [Monad M] [RandMonad M] : RandMonad (TimeMT ℕ M) where
  randIdx L h := TimeMT.lift (RandMonad.randIdx L h)

def QuickSortTimed {M} [Monad M] [RandMonad M] : List ℕ → TimeMT ℕ M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      -- each element of `rest` is compared once against pivot
      TimeMT.tick rest.length
      let S1 ← QuickSortTimed L1
      let S2 ← QuickSortTimed L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
decreasing_by all_goals grind

-- IO version (executable)
def QuickSortT_IO: List ℕ → TimeMT ℕ IO (List ℕ) := QuickSortTimed

#eval (QuickSortT_IO [5,4,2,1,3,6,2,1,24,6]).run

noncomputable def QuickSortT_PMF: List ℕ → TimeMT ℕ PMF (List ℕ) := QuickSortTimed

-- ---------------------------------------
-- Correctness proof of the PMF version
-- ---------------------------------------

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

private noncomputable abbrev qs_branch (M : Type → Type) [Monad M] [RandMonad M]
  (L : List ℕ) (i : Fin L.length) : M (List ℕ) := do
  let rest := L.eraseIdx i
  let pivot := L[i]
  let S1 ← QuickSort (rest.filter (· < pivot))
  let S2 ← QuickSort (rest.filter (· ≥ pivot))
  return (S1 ++ [pivot] ++ S2)

-- ---------------------------------------
-- Mathematical Specification (Axioms)
-- ---------------------------------------

class LawfulRandMonad (M : Type → Type) [Monad M] [LawfulMonad M] extends RandMonad M where
  -- A way to evaluate the abstract monad as a mathematical probability
  toPMF : ∀ {α}, M α → PMF α

  -- Axiom 1: pure maps to PMF.pure
  toPMF_pure : ∀ {α} (a : α), toPMF (pure a) = pure a

  -- Axiom 2: bind maps to PMF.bind
  toPMF_bind : ∀ {α β} (x : M α) (f : α → M β),
    toPMF (x >>= f) = (toPMF x) >>= (fun a => toPMF (f a))

  -- Axiom 3: randIdx is perfectly uniform
  toPMF_randIdx : ∀ (L : List ℕ) (hne : 0 < L.length),
    toPMF (randIdx L hne) =
      (have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩;
       PMF.uniformOfFintype (Fin L.length))

-- ---------------------------------------
-- The Generic Correctness Lemma
-- ---------------------------------------

lemma Correctness_Quicksort {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    ∀ L : List ℕ, ∃ Output : List ℕ,
    LawfulRandMonad.toPMF (QuickSort L : M (List ℕ)) = pure Output ∧
    Output.SortedLE ∧ Output.Perm L := by
  apply QuickSort.induct
  -- Base case
  · exact ⟨[], by simp [QuickSort.eq_1, LawfulRandMonad.toPMF_pure],
    by simp [List.sortedLE_iff_pairwise], by simp⟩
  -- Inductive case
  · intro head tail ihL1 ihL2
    let L := head :: tail
     -- For each pivot, build a correct output from the IH
    have h_step : ∀ i : Fin L.length, ∃ Out,
        LawfulRandMonad.toPMF (qs_branch M L i) = pure Out ∧ Out.SortedLE ∧ Out.Perm L := by
      intro i
      obtain ⟨O1, h1, s1, p1⟩ := ihL1 i
      obtain ⟨O2, h2, s2, p2⟩ := ihL2 i
      use O1 ++ [L[i]] ++ O2
      split_ands
      · unfold qs_branch; unfold_do
        simp only [LawfulRandMonad.toPMF_bind, LawfulRandMonad.toPMF_pure]
        rw [h1, h2]; simp_all [length_cons, Fin.getElem_fin, ge_iff_le, L]
        rfl
      · apply sorted_concat_pivot s1 s2 <;> grind
      · exact (List.Perm.append (List.Perm.append p1 (.refl _)) p2).trans (perm_filter_partition L i)
    -- All pivots yield the same output (uniqueness of sorted permutation)
    -- which is sorted and a permutation of the input. So we use such an output.
    obtain ⟨Output, h0, hS, hP⟩ := h_step ⟨0, by grind⟩
    refine ⟨Output, ?_, hS, hP⟩
    -- The PMF is uniform over the pivot choice,
    -- and all pivots yield the same output,
    -- so the PMF is actually a point mass on this output.
    have : Nonempty (Fin L.length) := ⟨⟨0, by grind⟩⟩
    calc LawfulRandMonad.toPMF (QuickSort L : M (List ℕ))
        = LawfulRandMonad.toPMF (RandMonad.randIdx L (by grind) >>= fun idx => qs_branch M L idx) := by
          unfold qs_branch
          rw [QuickSort.eq_2 head tail]
      _ = (PMF.uniformOfFintype (Fin L.length)).bind (fun idx => LawfulRandMonad.toPMF (qs_branch M L idx)) := by
          rw [LawfulRandMonad.toPMF_bind, LawfulRandMonad.toPMF_randIdx]
          simp_all only [length_cons, Fin.getElem_fin, ge_iff_le, Fin.zero_eta, L]
          rfl
      _ = (PMF.uniformOfFintype (Fin L.length)).bind fun _ => pure Output := by
          congr 1; funext i
          obtain ⟨Oi, hi, si, pi⟩ := h_step i
          rwa [eq_of_sortedLE_perm si hS (pi.trans hP.symm)] at hi
      _ = pure Output := PMF.bind_const _ _

-- ---------------------------------------
-- Free Proof: Untimed QuickSort_PMF
-- ---------------------------------------

-- First, we prove PMF itself is a LawfulRandMonad trivially
noncomputable instance : LawfulRandMonad PMF where
  toPMF := id
  toPMF_pure _ := rfl
  toPMF_bind _ _ := rfl
  toPMF_randIdx _ _ := rfl

-- Now we get the untimed PMF correctness completely for free
lemma Correctness_Quicksort_PMF : ∀ L : List ℕ, ∃ Output : List ℕ,
  QuickSort_PMF L = pure Output ∧ Output.SortedLE ∧ Output.Perm L := Correctness_Quicksort (M := PMF)


-- ---------------------------------------
-- Free Proof: Timed QuickSortT_PMF
-- ---------------------------------------

/-! ### Helper lemmas for TimeMT erasure -/

-- If we chain two steps together, extracting the final answer is the
-- same as ignoring the time in step 1, then ignoring the time in step 2.
@[simp] lemma TimeMT_erase_bind {M} [Monad M] [LawfulMonad M] {α β}
    (m : TimeMT ℕ M α) (f : α → TimeMT ℕ M β) :
    TimeM.ret <$> (m >>= f).run = (TimeM.ret <$> m.run) >>= fun a => TimeM.ret <$> (f a).run := by
  simp only [TimeMT.run_bind, map_bind]
  simp_all only [map_pure, bind_pure_comp, bind_map_left]

-- If we create a plain value with no time cost, extracting the
-- answer just gives us that exact plain value back.
@[simp] lemma TimeMT_erase_pure {M} [Monad M] [LawfulMonad M] {α} (a : α) :
    TimeM.ret <$> (pure a : TimeMT ℕ M α).run = pure a := by
  simp only [TimeMT.run_pure, map_pure]

-- If we simply advance the clock (a 'tick') without returning any data,
-- extracting the answer gives us an empty result.
@[simp] lemma TimeMT_erase_tick {M} [Monad M] [LawfulMonad M] (t : ℕ) :
    TimeM.ret <$> (TimeMT.tick t : TimeMT ℕ M Unit).run = pure () := by
  simp only [TimeMT.run_tick, map_pure]

-- If we take a standard function and wrap it to track time, stripping
-- that time wrapper away gives us the standard function back.
@[simp] lemma TimeMT_erase_lift {M} [Monad M] [LawfulMonad M] {α} (m : M α) :
    TimeM.ret <$> (TimeMT.lift m : TimeMT ℕ M α).run = m := by
  rw [TimeMT.run_lift, ← Functor.map_map]
  simp_all only [Functor.map_map, id_map']

-- Picking a random number in our timed program is functionally identical
-- to picking a random number normally and then wrapping it in a time tracker.
@[simp] lemma TimeMT_randIdx_run {M} [Monad M] [RandMonad M] (L : List ℕ) (h : 0 < L.length) :
    (RandMonad.randIdx L h : TimeMT ℕ M (Fin L.length)).run =
    (TimeMT.lift (RandMonad.randIdx L h : M (Fin L.length))).run := rfl

-- ---------------------------------------
-- Erasure & Main Proof
-- ---------------------------------------

-- We prove that tracking time doesn't change the actual sorting logic by
-- checking every step of the QuickSort process.
lemma QuickSortTimed_erasure {M} [Monad M] [LawfulMonad M] [RandMonad M] (L : List ℕ) :
    TimeM.ret <$> (QuickSortTimed L : TimeMT ℕ M (List ℕ)).run = QuickSort L := by
  induction L using QuickSort.induct
  · -- Base case
    rw [QuickSort.eq_1, QuickSortTimed.eq_1]
    simp
  · -- Inductive case
    next head tail ih1 ih2 =>
      rw [QuickSort.eq_2 head tail, QuickSortTimed.eq_2 head tail]
      -- Push the TimeM.ret erasure down through all the binds and primitives
      simp only [TimeMT_erase_bind, TimeMT_randIdx_run, TimeMT_erase_lift,
                 TimeMT_erase_tick, TimeMT_erase_pure]
      -- Apply the inductive hypotheses directly inside the simplified binds
      simp only [ih1, ih2]
      -- Clean up the `pure () >>= fun _ => ...` introduced by `tick`
      simp only [pure_bind]

-- Now we get the timed PMF correctness completely for free
lemma Correctness_QuicksortTimed_PMF : ∀ L : List ℕ, ∃ Output : List ℕ,
    TimeM.ret <$> (QuickSortT_PMF L).run = pure Output ∧ Output.SortedLE ∧ Output.Perm L := by
  intro L
  -- 1. Extract the pure math proof we already finished for PMF
  obtain ⟨Out, hEq, hSort, hPerm⟩ := Correctness_Quicksort_PMF L
  use Out
  -- 2. Rewrite the timed goal into the untimed goal using our bridge
  unfold QuickSortT_PMF
  rw [QuickSortTimed_erasure]
  -- 3. Apply the free facts
  exact ⟨hEq, hSort, hPerm⟩

end ARA
