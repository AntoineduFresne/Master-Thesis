import ARA.Rnd
import ARA.Tactics

/-!
  Future directions for the framework.

  The big picture is a three-layer pipeline:

  1. Write the algorithm once, in pseudo-code style (do-notation), parameterized
     by a typeclass (RandMonad) that abstracts over the source of randomness.
     The same code then instantiates into different monads:
     - IO    → executable version (run it, benchmark it, test it)
     - PMF   → noncomputable probability distribution over outputs (analyze it)
     - Rnd T → joint distribution over (output, cost) pairs (analyze cost too)
     This is what the RandMonad typeclass does: write QuickSort_Gen once, get
     QuickSort_IO, QuickSort_PMF, QuickSort_RndGen for free.

  2. From the PMF or Rnd version, extract the quantities we care about:
     - m.outputDist : PMF α   (what does the algorithm return?)
     - m.costDist   : PMF T   (how much does it cost?)
     These come for free from the definition of Rnd = PMF (α × T).

  3. Prove properties about the extracted distributions:
     - correctness:  m.outputDist = PMF.pure answer
     - complexity:   E[m.costDist] ≤ bound
     - tail bounds:  P(cost > k) ≤ ε

  Layers 1 and 2 exist. Layer 3 is the actual future work.

  The framework is not specialized to quicksort — quicksort is just a demo.
  The goal is to handle different classes of randomized algorithms. Of course
  no single framework can generalize everything, and we'll likely need
  specialized modules for certain algorithm families (e.g. Las Vegas, Monte Carlo,
  randomized data structures), but the typeclass + monad approach should give a
  common backbone.

  Open question on cost tracking:
  Right now the RandMonad typeclass only abstracts randomness, not cost. So cost
  annotations (tick calls) need to be written manually in the Rnd version, separately
  from the generic version. Two possible directions:
  - Extend the typeclass to include a tick primitive, so one generic algorithm has
    both randomness and cost, and when instantiated in IO the ticks are no-ops
    but in Rnd ℕ they accumulate.
  - Keep cost as a separate concern layered on top (manual annotation).
  Both have tradeoffs and the right design is not clear yet. The Rnd monad itself
  is a rough first attempt and will likely be rebuilt — in particular, Rnd should
  probably be generalized via WriterT so that TimeM (deterministic cost) and Rnd
  (probabilistic cost) share the same infrastructure (see Rnd.lean comments).

  Design notes:
  - We represent Rnd T α as PMF (α × T) rather than α → T → ℝ≥0∞ because
    PMF gives normalization, bind, and all Mathlib lemmas for free.
  - We use shallow embedding (algorithms are Lean functions, not an embedded
    language). The cost is that tick annotations are trusted — the user must
    check they match the intended cost model. (see also ARA/notes/literature.txt)
  - Non-termination is a real limitation: PMF requires total mass = 1, meaning
    the algorithm must terminate with probability 1. For Las Vegas algorithms
    (retry until success), we'd need either sub-probability distributions or a
    fuel parameter with limit analysis. PMF.toOuterMeasure can handle mass ≤ 1
    but PMF itself cannot, so this is a structural limitation of the current approach.
  - Extending to continuous distributions (e.g. exponential waiting times) would
    require replacing PMF with MeasureTheory.Measure. This is very far from where
    we are right now — it means dealing with sigma-algebras and measurability proofs
    everywhere, no more nice finite sums. Worth thinking about eventually.

  What is already done:
  - ✓ Correctness of quicksort (QuickSort.lean: always returns sorted permutation)
  - ✓ Rnd monad with cost tracking (Rnd.lean) — rough first version
  - ✓ RandMonad typeclass: one algorithm → IO + PMF + Rnd ℕ for free (below)
  - ✓ Deterministic output = PMF is pure → correctness via induction (QuickSort.lean)

  What remains:
  - Complexity proof: E[comparisons for quicksort] = O(n log n)
  - The ideal goal: a general framework where you write an algorithm f
    and get running_time(f) and probability(f) extracted automatically.
    An algorithm decomposes into steps; each step has its own cost/output distribution;
    composing steps (via bind) gives the overall distributions. The Rnd monad is
    a first step toward this but the extraction + proof automation (Layer 3) is
    where most of the remaining work lies.
  - Generalize TimeM to any monad via WriterT: TimeM T α = (α × T) is cost
    tracking over the identity monad. Rnd T α = PMF (α × T) is cost tracking
    over PMF. Both are WriterT T M for different M. The Rnd monad should probably
    be rebuilt on top of this generalization, so that TimeM, Rnd, and potentially
    a cost-tracking IO version all share the same infrastructure. Whether to use
    Lean's WriterT directly or a custom structure is still open.
  - Better induction infrastructure for correctness proofs
    (the QuickSort proof was painful — can we make it more systematic?)
  - Generalize beyond quicksort to other algorithm families

  This file contains:
  - QuickSort_Rnd: demo of Rnd with manual cost tracking (rough prototype)
  - RandMonad typeclass + QuickSort_Gen: write once, instantiate in IO / PMF / Rnd ℕ
-/

namespace ARA

open PMF ENNReal

/-! ## Demo: QuickSort with Cost Tracking (Rnd monad)

  This version has explicit tick calls for the partition cost, unlike
  QuickSort_RndGen below which is derived from the generic RandMonad
  version and has no cost annotations. So this is the one to use for
  complexity analysis.
-/

/-- QuickSort in the `Rnd ℕ` monad: tracks both probability and comparison count.
    The partition step charges |rest| comparisons. -/
noncomputable def QuickSort_Rnd : List ℕ → Rnd ℕ (List ℕ) := fun
| [] => pure []
| L@(head::tail) => do
  have : Nonempty (Fin L.length) := ⟨⟨0, by grind⟩⟩
  let idx ← Rnd.uniformFintype (Fin L.length)
  let pivot := L[idx]
  let rest := L.eraseIdx idx
  -- charge |rest| comparisons for the partition step
  Rnd.tick rest.length
  let L1 := rest.filter (· < pivot)
  let L2 := rest.filter (· ≥ pivot)
  let S1 ← QuickSort_Rnd L1
  let S2 ← QuickSort_Rnd L2
  pure (S1 ++ [pivot] ++ S2)
termination_by L => L.length
decreasing_by
  all_goals
    have h_rest : (L.eraseIdx idx).length < L.length := by
      rw [List.length_eraseIdx]; grind
    apply Nat.lt_of_le_of_lt
    · apply List.length_filter_le
    · grind

noncomputable def QuickSort_Rnd_outputDist (L : List ℕ) : PMF (List ℕ) :=
  (QuickSort_Rnd L).outputDist

noncomputable def QuickSort_Rnd_costDist (L : List ℕ) : PMF ℕ :=
  (QuickSort_Rnd L).costDist

/-!
## Expected Cost Analysis

To prove E[comparisons] = O(n log n):
1. Define expected cost: `expectedCost m = ∑' (a, c), m.run (a, c) * c`
2. Express as a recurrence: `E[T(n)] = 1/n * ∑ᵢ (n-1 + E[T(i)] + E[T(n-1-i)])`
3. Solve the recurrence in Lean (show it satisfies E[T(n)] ≤ 2n ln n)

Step 1 is automatic via `costDist`. Step 2 needs some work. Step 3 is pure math.
-/

/-- Expected cost of a `Rnd ℕ α` computation. -/
noncomputable def expectedCostNat {α : Type*} (m : Rnd ℕ α) : ℝ≥0∞ :=
  ∑' (p : α × ℕ), m.run p * p.2

/-!
## RandMonad typeclass: write once, instantiate in IO and PMF

The idea: write one algorithm parameterized by a monad with a random index primitive,
then get the IO version (executable) and the PMF version (for analysis) for free by
instantiation. No code duplication.

This is orthogonal to the Rnd monad above:
- Rnd tracks cost + probability in one object
- RandMonad abstracts over IO vs PMF (or Rnd ℕ too — see below)

You can combine both: a `RandMonad (Rnd ℕ)` instance gives you a generic algorithm
that is simultaneously executable (via IO), analyzable (via PMF), and cost-tracking (via Rnd ℕ).
Note: the Rnd ℕ instantiation via RandMonad does NOT charge any cost for pivot selection
(unlike QuickSort_Rnd above which has explicit tick calls). To get cost tracking you still
need to write the algorithm with tick annotations.
-/

class RandMonad (M : Type → Type) [Monad M] where
  randIdx {α} : (L : List α) → 0 < L.length → M (Fin L.length)

-- one algorithm, works in any monad with RandMonad
def QuickSort_Gen [Monad M] [RandMonad M] : List ℕ → M (List ℕ)
  | [] => return []
  | L@(_::_) => do
      let idx ← RandMonad.randIdx L (by grind)
      let pivot := L[idx]
      let rest := L.eraseIdx idx
      let L1 := rest.filter (· < pivot)
      let L2 := rest.filter (· ≥ pivot)
      let S1 ← QuickSort_Gen L1
      let S2 ← QuickSort_Gen L2
      return (S1 ++ [pivot] ++ S2)
  termination_by L => L.length
  decreasing_by all_goals grind

-- IO instance: uses the system RNG
instance : RandMonad IO where
  randIdx L hne := do
    let i ← IO.rand 0 (L.length - 1)
    return ⟨i % L.length, Nat.mod_lt i hne⟩

-- PMF instance: uniform distribution over indices
noncomputable instance : RandMonad PMF where
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
    PMF.uniformOfFintype (Fin L.length)

-- Rnd ℕ instance: uniform distribution, zero cost for pivot selection
-- (cost charged separately via tick if needed)
noncomputable instance : RandMonad (Rnd ℕ) where
  randIdx L hne :=
    have : Nonempty (Fin L.length) := ⟨⟨0, hne⟩⟩
    Rnd.uniformFintype (Fin L.length)

-- executable version
def QuickSort_IO : List ℕ → IO (List ℕ) := QuickSort_Gen

-- PMF analysis version (same code as QuickSort_A in Phase2 but derived here for free)
noncomputable def QuickSort_PMF : List ℕ → PMF (List ℕ) := QuickSort_Gen

-- Rnd ℕ version: both probability and cost accessible (but no tick calls,
-- so cost is always 0 — use QuickSort_Rnd for actual cost analysis)
noncomputable def QuickSort_RndGen : List ℕ → Rnd ℕ (List ℕ) := QuickSort_Gen

end ARA
