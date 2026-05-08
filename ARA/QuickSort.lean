import TimeM
import ARA.Tactics
import ARA.ExpectedCost

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
-- Generic Correctness proof
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

/-!
### Mathematical Specification (Axioms)
-/
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

lemma LawfulRandMonad.toPMF_map {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {α β} (f : α → β) (x : M α) :
    LawfulRandMonad.toPMF (f <$> x) = f <$> LawfulRandMonad.toPMF x := by
  rw [map_eq_bind_pure_comp, LawfulRandMonad.toPMF_bind]
  simp [LawfulRandMonad.toPMF_pure, map_eq_bind_pure_comp]

-- The Generic Correctness Lemma for monad satisfying these axioms
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

-- ---------------------------------------
-- Generic Complexity Proof
-- ---------------------------------------

-- The n-th Harmonic number
def harmonic : ℕ → ℚ
  | 0 => 0
  | n + 1 => harmonic n + (1 / (n + 1))

-- The exact expected number of comparisons for QuickSort -/
def expected_qs_cost (n : ℕ) : ℚ :=
  2 * (n + 1) * harmonic n - 4 * n

/-
### Bridge between TimeM and TimedResult
-/

/-- Convert TimeM to TimedResult. -/
def toTimedResult {α : Type} (tm : TimeM ℕ α) : TimedResult α :=
  ⟨tm.ret, tm.time⟩

/-- Convert TimedResult to TimeM. -/
def toTimeM {α : Type} (tr : TimedResult α) : TimeM ℕ α :=
  ⟨tr.val, tr.cost⟩

@[simp] lemma toTimedResult_toTimeM {α : Type} (tr : TimedResult α) :
    toTimedResult (toTimeM tr) = tr := rfl

@[simp] lemma toTimeM_toTimedResult {α : Type} (tm : TimeM ℕ α) :
    toTimeM (toTimedResult tm) = tm := by ext <;> rfl

/-- Expected cost of a timed computation via the TimedResult bridge. -/
noncomputable def expected_cost_tm {α : Type} (p : PMF (TimeM ℕ α)) : ENNReal :=
  expected_cost (p.map toTimedResult)

/-!
### Bridge lemmas: lift expected_cost properties to expected_cost_tm
-/

@[simp] lemma expected_cost_tm_pure_val {α : Type} (a : α) (t : ℕ) :
    expected_cost_tm (PMF.pure ⟨a, t⟩ : PMF (TimeM ℕ α)) = (t : ENNReal) := by
  simp only [expected_cost_tm, PMF.pure_map, toTimedResult]
  exact expected_cost_pure_val a t

/-- Linearity of expected cost through a PMF bind (outer distribution has no time). -/
lemma expected_cost_tm_bind {A : Type} {β : Type} (d : PMF A) (f : A → PMF (TimeM ℕ β)) :
    expected_cost_tm (d >>= f) = ∑' a, d a * expected_cost_tm (f a) := by
  simp only [expected_cost_tm]
  have h : PMF.map toTimedResult (d >>= f) =
      d.bind (fun a => PMF.map toTimedResult (f a)) := PMF.map_bind d f toTimedResult
  rw [h]
  exact expected_cost_bind d (fun a => PMF.map toTimedResult (f a))

/-- Expected cost under uniform pivot selection. -/
lemma expected_cost_tm_uniform_bind {n : ℕ} [NeZero n] {β : Type}
    (f : Fin n → PMF (TimeM ℕ β)) :
    expected_cost_tm (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, expected_cost_tm (f i) := by
  simp only [expected_cost_tm]
  have h : PMF.map toTimedResult (PMF.uniformOfFintype (Fin n) >>= fun i => f i) =
    PMF.uniformOfFintype (Fin n) >>= fun i => PMF.map toTimedResult (f i) :=
    PMF.map_bind _ _ _
  rw [h]
  exact expected_cost_uniform_bind _

@[simp] lemma expected_qs_cost_zero : expected_qs_cost 0 = 0 := by
  simp [expected_qs_cost, harmonic]

@[simp] lemma expected_qs_cost_one : expected_qs_cost 1 = 0 := by
  simp [expected_qs_cost, harmonic]; norm_num

/-- The QuickSort recurrence: `C(n+1) = n + (2/(n+1)) ∑_{i<n+1} C(i)`. -/
lemma expected_qs_recurrence (n : ℕ) :
    (n : ℚ) + (2 / (n + 1)) * (∑ i ∈ Finset.range (n + 1), expected_qs_cost i)
    = expected_qs_cost (n + 1) := by
  unfold expected_qs_cost
  induction n <;> simp_all +decide [Finset.sum_range_succ, harmonic]
  · norm_num
  · sorry

/-- Non-negativity of expected_qs_cost (by strong induction). -/
lemma expected_qs_cost_nonneg (n : ℕ) : 0 ≤ expected_qs_cost n := by
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
### The Main Theorem

**Note**: The formula `2(n+1)H(n) − 4n` requires `L.Nodup` (distinct elements).
For lists with duplicates, the expected cost differs (e.g. `[1,1,1]` costs 3
but `C(3) = 8/3`).
-/

/-!
### Monadic unfolding: base case

For the empty list, `QuickSortTimed` returns `pure ⟨[], 0⟩` with zero cost.
-/

lemma expected_cost_tm_quicksort_nil
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    expected_cost_tm
      (inst.toPMF (QuickSortTimed ([] : List ℕ) : TimeMT ℕ M (List ℕ)).run) = 0 := by
  rw [QuickSortTimed.eq_1]
  simp only [TimeMT.run_pure, inst.toPMF_pure]
  -- Now goal is: expected_cost_tm (pure ⟨[], 0⟩) = 0
  -- `pure` here is PMF.pure since toPMF_pure converted
  change expected_cost_tm (PMF.pure ⟨[], 0⟩) = 0
  simp [expected_cost_tm_pure_val]

/-!
### Monadic unfolding: inductive case

For `L = head :: tail`, `QuickSortTimed` picks a uniform pivot, partitions,
ticks `rest.length`, and recurses. After applying `toPMF`, the expected cost
decomposes as a uniform average over pivot choices.

The proof requires unfolding the `TimeMT.run_bind` chain and distributing
`toPMF` through each M-bind. This is the most technically involved step.
-/

/-- After applying toPMF to the .run of QuickSortTimed on a nonempty list,
the expected cost is the uniform average:
`E[cost] = (1/n) * Σ_i ((n-1) + E[cost L1_i] + E[cost L2_i])`

This is a monadic unfolding lemma that connects the operational code
to the combinatorial cost analysis. -/
lemma expected_cost_tm_quicksort_step
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (head : ℕ) (tail : List ℕ) :
    let L := head :: tail
    expected_cost_tm (inst.toPMF (QuickSortTimed L : TimeMT ℕ M (List ℕ)).run) =
    (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length,
      let pivot := L[i]
      let rest := L.eraseIdx i
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      ((rest.length : ENNReal) +
        expected_cost_tm (inst.toPMF (QuickSortTimed L1 : TimeMT ℕ M (List ℕ)).run) +
        expected_cost_tm (inst.toPMF (QuickSortTimed L2 : TimeMT ℕ M (List ℕ)).run)) := by
  sorry

/-!
### Partition size lemma for distinct lists

For a list with distinct elements, the set of partition sizes
`{|L1_i| : i ∈ Fin n}` equals `{0, ..., n-1}` (as a multiset).
This is because choosing the element of rank k as pivot gives
exactly k elements less than it and (n-1-k) elements ≥ it.
-/

open Finset

/-
For a list of distinct elements, summing `f(|L1_i|) + f(|L2_i|)` over
all pivot indices i gives `Σ_k (f(k) + f(n-1-k))`.
-/
lemma nodup_partition_sum (L : List ℕ) (hnd : L.Nodup) (f : ℕ → ℚ) :
    (∑ i : Fin L.length,
      (f ((L.eraseIdx i).filter (· < L[i])).length +
       f ((L.eraseIdx i).filter (· ≥ L[i])).length)) =
    ∑ k : Fin L.length,
      (f k.val + f (L.length - 1 - k.val)) := by
  -- By definition of $rank$, we know that for each $i$, $(List.filter (fun x => x < L[i]) (L.eraseIdx i)).length = rank(i)$.
  have h_rank : ∀ i : Fin L.length, ((L.eraseIdx i).filter (· < L[i])).length = (Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)).card := by
    intro i
    have h_filter_eq : List.toFinset (List.filter (fun x => x < L[i]) (L.eraseIdx i)) = Finset.image (fun x => L[x]) (Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)) := by
      ext; simp [Finset.mem_image];
      constructor;
      · intro h;
        obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp h.1;
        use ⟨ if k.val < i.val then k.val else k.val + 1, by
          grind ⟩
        generalize_proofs at *;
        grind;
      · rintro ⟨ j, ⟨ hj₁, hj₂ ⟩, rfl ⟩;
        rw [ List.mem_iff_get ];
        simp_all +decide [ Fin.ext_iff];
        use ⟨ if j.val < i.val then j.val else j.val - 1, by
          grind ⟩
        generalize_proofs at *;
        grind;
    rw [ ← List.toFinset_card_of_nodup ];
    · rw [ h_filter_eq, Finset.card_image_of_injective _ fun x y hxy => by simpa [ Fin.ext_iff ] using List.nodup_iff_injective_get.mp hnd hxy ];
    · exact List.Nodup.filter _ ( hnd.eraseIdx _ );
  -- By definition of $rank$, we know that for each $i$, $(List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)).length = L.length - 1 - rank(i)$.
  have h_complement_rank : ∀ i : Fin L.length, ((L.eraseIdx i).filter (· ≥ L[i])).length = L.length - 1 - (Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)).card := by
    intro i
    have h_complement_rank_eq : ((L.eraseIdx i).filter (· ≥ L[i])).length + ((L.eraseIdx i).filter (· < L[i])).length = L.length - 1 := by
      have h_complement_rank_eq : ∀ l : List ℕ, ((l.filter (· ≥ L[i])).length + (l.filter (· < L[i])).length = l.length) := by
        intro l; induction l <;> simp +decide [ * ] ;
        grind;
      convert h_complement_rank_eq ( L.eraseIdx i ) using 1;
      simp +decide [ List.length_eraseIdx ];
    exact eq_tsub_of_add_eq ( by linarith [ h_rank i ] );
  -- Since $rank$ is a bijection on $Fin L.length$, we can reindex the sum.
  have h_bijection : Finset.image (fun i : Fin L.length => (Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)).card) (Finset.univ : Finset (Fin L.length)) = Finset.range L.length := by
    refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _ <;> simp_all +decide;
    · grind;
    · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      intro i j h; contrapose! h; simp_all +decide [ Finset.filter_erase ] ;
      cases lt_or_gt_of_ne ( show L[i] ≠ L[j] from fun h' => h <| Fin.ext <| by have := List.nodup_iff_injective_get.mp hnd h'; aesop ) <;> simp_all +decide ;
      · refine' ne_of_lt ( Finset.card_lt_card _ );
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ fun x hx => lt_trans hx ‹_›, i, ‹_›, le_rfl ⟩;
      · refine' ne_of_gt ( Finset.card_lt_card _ );
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact ⟨ fun x hx => lt_trans hx ‹_›, j, ‹_›, le_rfl ⟩;
  have h_reindex : ∑ i : Fin L.length, (f ((Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)).card) + f (L.length - 1 - (Finset.filter (fun x => L[x] < L[i]) (Finset.univ.erase i)).card)) = ∑ k ∈ Finset.range L.length, (f k + f (L.length - 1 - k)) := by
    rw [ ← h_bijection, Finset.sum_image ];
    intro i hi j hj hij; have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image ( fun i : Fin L.length => # ( Finset.filter ( fun x : Fin L.length => L[x] < L[i] ) ( Finset.erase Finset.univ i ) ) ) Finset.univ ) = Finset.card Finset.univ ) ; aesop;
  simp_all +decide [ Finset.sum_range ]

/-- The expected cost of QuickSortTimed on a list of `n` distinct elements
is exactly `2(n+1)H(n) − 4n` comparisons. -/
theorem Expected_Complexity_Quicksort
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List ℕ) (hnd : L.Nodup) :
    (expected_cost_tm
      (inst.toPMF (QuickSortTimed L : TimeMT ℕ M (List ℕ)).run)).toReal
    = (expected_qs_cost L.length : ℚ) := by
  sorry

end ARA
