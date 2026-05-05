import ARA.Basic

/-!
  ### Phase 2: Formalizing and Analyzing a More Complex Randomized Algorithm

  Lets now formalize quicksort as an example of a more complex randomized algorithm.

  First lets recall the algorithm in its most general version:
  Quicksort: "Sort a list"

  - Input: A (finite) list of elements of a totally ordered set (S,≤) that is L : List S.
  - Output: A permutation of the input list L that is sorted in non-decreasing
    order w.r.t to the running index and ≤: i < j -> L[i] ≤ L[j].

  Algorithm:
    1. If the list is empty, return the empty list.
    3. Otherwise, select a pivot element p from the list uniformly at random.
    4. Partition the remaining elements into two sublists:
        - L₁ = {x ∈ L\{p} | x < p}
        - L₂ = {x ∈ L\{p} | x ≥ p}
        by doing one traversal of the list, comparing each element to the pivot
        and placing it in the appropriate sublist.
    5. Recursively apply quicksort to L₁ and L₂ (whose lengths are strictly smaller
    than the original list) to obtain sorted sublists S₁ and S₂.
    6. Return the concatenation of S₁, [p], and S₂: S₁ ++ [p] ++ S₂.

  We first implement the algorithm not randomized: QuickSort_NR
  where S = ℕ for simplicity and the pivot is always the
  first element of the list.
-/

namespace ARA

open PMF

def QuickSort_NR : List ℕ → List ℕ := fun
| [] => []
| pivot :: tail =>
  let L1 := tail.filter (fun x => x < pivot)
  let L2 := tail.filter (fun x => x ≥ pivot)
  have h1 : L1.length < (pivot :: tail).length := by
    apply Nat.lt_succ_of_le
    apply List.length_filter_le
  have h2 : L2.length < (pivot :: tail).length := by
    apply Nat.lt_succ_of_le
    apply List.length_filter_le
  let S1 := QuickSort_NR L1
  let S2 := QuickSort_NR L2
  S1 ++ [pivot] ++ S2
  termination_by L => L.length
  decreasing_by
  all_goals grind

#eval QuickSort_NR [3, 1, 4, 1, 5, 9, 2, 6]

/-
Now we can define the randomized version of quicksort,
where the pivot is selected uniformly at random from
the list (assuming of course that pseudorandom number
are uniform random number).

Here since we want to be able to execute/evaluate the code, we
use the IO monad to generate random numbers, which is different
than using the PMF monad in the following way:

The IO monad can be visualized as follow:

Let S be the set of all possible configurations of the computer's memory and environment.
Let α be a type.

IO α consists of functions ("action") of the form S → (α × S).

pure : α → IO α takes a : α and returns a function that takes a state s : S
and returns the pair (a, s) i.e. (pure a) : S → α × S, s ↦ (a, s).

Bind : IO α → (α → IO β) → IO β takes an IO α action act, and a function f : α → IO β
and returns an IO β action that represents the sequential execution of the two actions
i.e. (act.bind f) : S → β × S, s ↦ (f (act s).1) (act s).2
-/
/-!
To be completely pragmatic: Lean cannot access to these states (S) at all and their underlying
representation is not existant. It is not a bit string, it is not a memory map, and it
contains absolutely zero data. It is a trick played on the type checker
to force it to sequence operations correctly.

We split between what happens when we write
the code and what happens when we run it:

1. Compile Time: The Phantom Token

In Lean's internal code, the state of the universe S is defined like this:
''
opaque IO.RealWorld.nonemptyType : NonemptyType.{0}
/-
A representation of "the real world" that's used in `IO` monads to ensure
that `IO` actions are ordered correctly.
-/
@[expose] def IO.RealWorld : Type := IO.RealWorld.nonemptyType.type
''
What is missing: there is no = sign, no data structures, and no bit strings.
It is an opaque type (often called a phantom type).
We tell the mathematical theorem prover that a set called RealWorld exists,
but we intentionally refuse to define what its elements look like.

Because it is opaque, it is mathematically impossible for Lean to
write a pure function that opens up a RealWorld token to "look" at the data
inside. If you cannot look at it, you cannot write mathematical proofs that
depend on it.

Its only job is to act as a dependency baton.
If Step B requires the phantom token produced by Step A,
Lean's type checker is forced to put Step A before Step B
altough there is no actual data being passed around. This is
kinda a syntactical trick to play with Lean's compiler
rules and here for the IO monad it is used to enforce the correct
sequencing of IO operations which serves concrete purposes
(e.g. ensuring that we do not read from a file before writing
to it, or that we do not generate a random number before
seeding the random number generator).

2. Runtime: Type Erasure

If the token contains no data, what actually happens when we run a code with a phantom type ?
- Lean compiles down to C code and during this translation, the Lean
  compiler performs Type Erasure. Because the phantom type contains no concrete
  data and is mathematically irrelevant to the final computed values,
  the compiler simply deletes it.

  The mathematically pure, deeply nested bind functions that pass a dummy
  token around are stripped away, leaving behind raw, imperative C code.

  When our Lean code says IO.rand 0 10, the generated C code does not pass
  a universe token. It literally just calls the underlying C/C++ runtime
  function to ask the operating system for a random number.
-/
/-
We use the key word "Partial" because the function
is not structurally recursive anymore due to the
random pivot selection.
-/

partial def QuickSort_Rand : List ℕ → IO (List ℕ)
| [] => pure []
| L => do
  let idx <- IO.rand 0 (L.length - 1) -- Uniformly select an index at random for the pivot
  let pivot := (L[idx]?).getD 0
  /-
  We do this except handling (if idx is within bound then ..., otherwise we take ...)
  to satisfy the type checker, so that we avoid proving that idx is within the bounds,
  but we know idx is always valid since it is generated in the correct range.
  -/
  let rest := L.eraseIdx idx
  let L1 := rest.filter (fun x => x < pivot)
  let L2 := rest.filter (fun x => x ≥ pivot)
  let S1 ← QuickSort_Rand L1
  let S2 ← QuickSort_Rand L2
  pure (S1 ++ [pivot] ++ S2)

#eval QuickSort_Rand [3, 1, 4, 1, 5, 9, 2, 6]

/-
  Now lets make a QuickSort version using the PMF monad, where we
  can analyze the probability of certain events.

  How do we proceed:

  - Given a list L ≠ [], we want to bind the pivot distribution P (a distribution over ℕ with finite support)
    with the function f (defined recursively) that takes any pivot and returns the pure distribution of the
    sorted list given that pivot. The problem is that the pivot can be out of bounds and we cannot prove that it
    is not, so we cannot directly use bind. We can however use bindOnSupport! Since the pivot distribution is
    supported on L, we can prove that any pivot drawn from it (with positive probability) is in L and thus the
    function f is well defined on the support of the pivot distribution.

  - So, first we can define a pivot distribution that is uniform over the elements of the list L
    (which is equivalent to being uniform over the indices of the list L):
    idx_pivot_dist : PMF ℕ := PMF.uniformOfFintype (Fin L.length) where L is the input list.

  - Secondly, we can define the function ℕ × Prop → PMF (List ℕ) partitioning step that takes any pivot and the
    proof that the pivot is in the list and returns the two sublists:
     fun idx_pivot h_idx_pivot =>
      let pivot := L[idx_pivot]
      let rest := L.eraseIdx idx_pivot

      let L1 := rest.filter (fun x => x < pivot)
      let L2 := rest.filter (fun x => x ≥ pivot)
      do
        let S1 ← QuickSort_A L1
        let S2 ← QuickSort_A L2
        return (S1 ++ [pivot] ++ S2)

-/
noncomputable def QuickSort_A : List ℕ → PMF (List ℕ) := fun
| [] => PMF.pure []
| L@(_::_) =>
  have nonempty : Nonempty (Fin L.length) := ⟨⟨0, by grind⟩⟩

  let idx_pivot_dist := PMF.uniformOfFintype (Fin L.length)

  idx_pivot_dist.bind fun idx_pivot => do
    let pivot := L[idx_pivot]
    let rest := L.eraseIdx idx_pivot
    let L1 := rest.filter (· < pivot)
    let L2 := rest.filter (· ≥ pivot)
    let S1 ← QuickSort_A L1
    let S2 ← QuickSort_A L2
    return (S1 ++ [pivot] ++ S2)

termination_by L => L.length
decreasing_by all_goals grind
-- The definition is surprisingly natural and almost feels like
-- writing the algorithm in pseudo code: so good point.


-- Now we can analyze the probability of certain events.
/--
  Lemma: The probability that QuickSort_A on an empty list returns
  an empty list is exactly 1 (100%).
-/
lemma prob_quicksort_empty : QuickSort_A [] [] = 1 := by
  -- The definition of QuickSort_A on an empty list is just PMF.pure [],
  -- which assigns probability 1 to [] and 0 to any other list.
  unfold QuickSort_A
  simp

/--
  Lemma: A single-element list also deterministically returns itself
  with probability 1.
-/
lemma prob_quicksort_singleton (n : ℕ) : QuickSort_A [n] [n] = 1 := by
-- The pivot distribution is uniform over the single element list,
-- so it is just the Dirac distribution on that element.
  have hunif : PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
    ext a
    have ha : a = 0 := Fin.ext (by omega)
    subst ha
    simp [PMF.uniformOfFintype_apply]
  unfold QuickSort_A
  simp only [List.length_singleton]
  rw [hunif]
  rw [PMF.pure_bind]
-- The function we bind with is the one that takes the pivot
-- and returns the sorted list, which in this case is just
-- the identity function on [n].
  have hdet : (do let S1 ← PMF.pure []; PMF.pure (S1 ++ [n])) [n] = 1 := by
    change ((PMF.pure []).bind (fun S1 => PMF.pure (S1 ++ [n]))) [n] = 1
    simp
  simpa [QuickSort_A, Functor.map] using hdet
-- This was tedious and less natural.


/-
  Lemma: The probability that QuickSort_A on a list of two distinct elements
  returns the sorted list is exactly 1.
-/
lemma prob_quicksort_two_distinct (a b : ℕ) (h : a ≠ b) : QuickSort_A [a, b] [min a b, max a b] = 1 := by
  by_cases hab : a < b
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hab)
    have hmax : max a b = b := Nat.max_eq_right (Nat.le_of_lt hab)
    have hnot : ¬ b < a := Nat.not_lt.mpr (Nat.le_of_lt hab)
    have hfilter : List.filter (fun x => decide (a ≤ x)) [b] = [b] := by
      simp [Nat.le_of_lt hab]
    have hrec : QuickSort_A (List.filter (fun x => decide (a ≤ x)) [b]) [b] = 1 := by
      simpa [hfilter] using prob_quicksort_singleton b
    have ht :
        (do
            let S1 ← PMF.pure []
            let a_1 ← PMF.pure []
            (fun a_2 => S1 ++ a :: (a_1 ++ b :: a_2)) <$> PMF.pure []) [a, b] = 1 := by
      simp [Functor.map]
      change
        ((PMF.pure []).bind
          (fun S1 => (PMF.pure []).bind (fun a_1 => PMF.pure (S1 ++ a :: (a_1 ++ [b])))))
          [a, b] = 1
      simp
    simp [QuickSort_A, hab, hnot, hmin, hmax, hfilter]
    set t : ENNReal :=
      (do
          let S1 ← PMF.pure []
          let a_1 ← PMF.pure []
          (fun a_2 => S1 ++ a :: (a_1 ++ b :: a_2)) <$> PMF.pure []) [a, b]
    have ht' : t = 1 := by
      simpa [t] using ht
    calc
      (2⁻¹ : ENNReal) * t + (2⁻¹ : ENNReal) * t = (2⁻¹ : ENNReal) * 1 + (2⁻¹ : ENNReal) * 1 := by
        simp [ht']
      _ = 1 := by
        simpa [mul_one] using
          (ENNReal.inv_two_add_inv_two : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1))
  · have hba : b < a := lt_of_le_of_ne (Nat.le_of_not_gt hab) (Ne.symm h)
    have hmin : min a b = b := Nat.min_eq_right (Nat.le_of_lt hba)
    have hmax : max a b = a := Nat.max_eq_left (Nat.le_of_lt hba)
    have hnot : ¬ a < b := hab
    have hfilter : List.filter (fun x => decide (b ≤ x)) [a] = [a] := by
      simp [Nat.le_of_lt hba]
    have hrec : QuickSort_A (List.filter (fun x => decide (b ≤ x)) [a]) [a] = 1 := by
      simpa [hfilter] using prob_quicksort_singleton a
    have ht :
        (do
            let x ← PMF.pure []
            let a_1 ← PMF.pure []
            (fun a_2 => x ++ b :: (a_1 ++ a :: a_2)) <$> PMF.pure []) [b, a] = 1 := by
      simp [Functor.map]
      change
        ((PMF.pure []).bind
          (fun x => (PMF.pure []).bind (fun a_1 => PMF.pure (x ++ b :: (a_1 ++ [a])))))
          [b, a] = 1
      simp
    simp [QuickSort_A, hba, hnot, hmin, hmax, hfilter]
    set t : ENNReal :=
      (do
          let x ← PMF.pure []
          let a_1 ← PMF.pure []
          (fun a_2 => x ++ b :: (a_1 ++ a :: a_2)) <$> PMF.pure []) [b, a]
    have ht' : t = 1 := by
      simpa [t] using ht
    calc
      (2⁻¹ : ENNReal) * t + (2⁻¹ : ENNReal) * t = (2⁻¹ : ENNReal) * 1 + (2⁻¹ : ENNReal) * 1 := by
        simp [ht']
      _ = 1 := by
        simpa [mul_one] using
          (ENNReal.inv_two_add_inv_two : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1))
-- This was absolutely non natural and very tedious (did it with a local agent),
-- but it is a good example of the kind of properties we want to be able to
-- prove about randomized algorithms, and this tediousness motivates why we want
-- to have a more general framework for analyzing them.

end ARA
