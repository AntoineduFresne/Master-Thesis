import ARA.Tests.Phase1
import ARA.Tests.Phase2
import ARA.Tactics

/-!
  ### Phase 3 Demonstrations

  Below we re-prove selected lemmas from Phase 1 and Phase 2 using the
  sandbox toolkit.  Compare the proof lengths with the originals above.
-/

namespace ARA

open ENNReal PMF

/-! ##### Demo 4: QuickSort singleton (Phase 2)
    Original: 15 lines with manual `hunif`, `change`, and monadic rewriting.
    New:      5 lines using `pmf_uniformOfFintype_fin_one`.
-/
lemma prob_quicksort_singleton_auto (n : ℕ) : QuickSort_A [n] [n] = 1 := by
  unfold QuickSort_A
  simp [pmf_uniformOfFintype_fin_one, QuickSort_A, Functor.map]
  change ((PMF.pure []).bind (fun S1 => PMF.pure (S1 ++ [n]))) [n] = 1; simp

/-! ##### Demo 5: Bind over Fin 2 (unit test for pmf_simp)
    Shows how `pmf_simp` reduces a bind over Fin 2 to explicit arithmetic.
-/
example (p : PMF (Fin 2)) (f : Fin 2 → PMF ℕ) (b : ℕ) :
    (p.bind f) b = p 0 * (f 0) b + p 1 * (f 1) b := by
  pmf_simp

/-! ##### Demo 6: Uniform-bind constant-branch collapse
    When every pivot produces the same sorted list, the probability is 1.
-/
example (f : Fin 4 → PMF ℕ) (b : ℕ) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin 4)).bind f) b = v := by
  exact pmf_uniform_fin_bind_const_prob f b v hv


end ARA
