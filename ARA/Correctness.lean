/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.LawfulRandMonad
import ARA.MonadCost

/-!
# Correctness recipes for randomized algorithms

This module packages the generic, algorithm-independent part of a
correctness proof, so that verifying a new uniform-pivot algorithm
reduces to its mathematical content: how the specification interacts
with one branch of the algorithm.

## Dirac correctness (Las Vegas algorithms)

An algorithm is Dirac-correct when its output distribution is a
point mass at the specification value. The recipe for proving
`toPMF (myAlgo args) = PMF.pure (spec args)`:

1. **Spec-transport lemmas** (the mathematics): for each branch, prove
   how the specification commutes with it (e.g. `orderStat_lt_branch`:
   "if the rank falls in the `<`-side, the order statistic of `L` is
   the order statistic of that side"). Tag them `@[spec_transport]`.
2. **Induct**: `induction args using myAlgo.induct`; expose the pivot
   choice with the algorithm's `_eq_bind` decomposition lemma.
3. **Collapse**: `refine toPMF_randIdx_bind_dirac fun i => ?_` reduces
   the goal to a single branch at a fixed pivot `i`.
4. **Discharge the branch**: `dirac_step` pushes `toPMF` through the
   monadic structure (no-op `tick`s vanish, `bind`/`pure` distribute);
   close each case with the inductive hypotheses and the transport
   lemmas — or try `dirac_finish`, which attempts all of step 4 at
   once and leaves open exactly the missing mathematics.

## Distributional correctness (Monte Carlo algorithms)

When the output is genuinely random (e.g. `Karger`), correctness is a
property of the distribution: typically a support statement
(one-sided error) plus a success-probability bound. The analogous
generic primitives are:

* `toPMF_randIdx_bind_apply` — the output probability is the uniform
  average of the branch probabilities (probabilistic analogue of
  `expected_cost_uniform_step`);
* `le_toPMF_randIdx_bind` — lower-bound the success probability by a
  single good pivot;
* `support_toPMF_randIdx_bind` — the support is the union of the
  branch supports.
-/

namespace ARA

/-!
### `Monad`-vs-`PMF` syntactic bridges

`do`-notation produces `>>=`/`pure`, while Mathlib's `PMF` lemmas are
stated for `PMF.bind`/`PMF.pure`. The two are definitionally equal;
these rfl-bridges let `simp`/`rw` cross the gap syntactically.
-/

@[pmf_simp_attr, dirac_simp]
lemma pmf_bind_eq {α β : Type u} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

@[pmf_simp_attr, dirac_simp]
lemma pmf_pure_eq {α : Type*} (a : α) :
    (pure a : PMF α) = PMF.pure a := rfl

/-! ### Dirac correctness -/

/-- **Dirac collapse.** If every pivot branch produces the same point
mass, the uniform pivot choice is invisible: the whole computation is
that point mass. This is the generic closing step of a Las Vegas
correctness proof. -/
theorem toPMF_randIdx_bind_dirac
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M β} {out : β}
    (h : ∀ i, inst.toPMF (f i) = PMF.pure out) :
    inst.toPMF (randIdx L hL >>= f) = PMF.pure out := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx]
  simp only [h]
  exact PMF.bind_const _ _

/-! ### Distributional correctness -/

/-- The output probability of a uniform-pivot algorithm is the uniform
average of the branch probabilities. -/
theorem toPMF_randIdx_bind_apply
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) (b : β) :
    inst.toPMF (randIdx L hL >>= f) b =
      (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, inst.toPMF (f i) b := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  have : NeZero L.length := ⟨hL.ne'⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq]
  exact pmf_uniform_fin_bind_apply _ b

/-- A single good pivot lower-bounds the success probability by its
branch probability divided by the number of pivots. -/
theorem le_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) (b : β) (i₀ : Fin L.length) :
    (L.length : ENNReal)⁻¹ * inst.toPMF (f i₀) b ≤
      inst.toPMF (randIdx L hL >>= f) b := by
  rw [toPMF_randIdx_bind_apply hL f b]
  exact mul_le_mul' le_rfl
    (Finset.single_le_sum (f := fun i => inst.toPMF (f i) b)
      (fun i _ => zero_le) (Finset.mem_univ i₀))

/-- The support of a uniform-pivot algorithm is the union of the branch
supports: every pivot occurs with positive probability. This is the
shape of one-sided-error ("the output is always a valid answer")
correctness statements. -/
theorem support_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} (hL : 0 < L.length)
    (f : Fin L.length → M β) :
    (inst.toPMF (randIdx L hL >>= f)).support =
      ⋃ i, (inst.toPMF (f i)).support := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq, PMF.support_bind]
  simp [PMF.support_uniformOfFintype]

/-! ### Automation -/

attribute [dirac_simp] LawfulRandMonad.toPMF_pure
attribute [dirac_simp] LawfulRandMonad.toPMF_bind
attribute [dirac_simp] MonadCost.tick_default
attribute [dirac_simp] pure_bind bind_pure map_pure

/-- `dirac_step` pushes `toPMF` through one algorithm branch: no-op
`tick`s vanish, `toPMF` distributes over `bind` and evaluates on
`pure`. What remains is the branch's case split plus the recursive
calls, to be closed by the inductive hypotheses and the
`@[spec_transport]` lemmas. -/
scoped macro "dirac_step" : tactic =>
  `(tactic| simp only [dirac_simp])

/-- `dirac_finish` attempts to close a branch goal outright: push
`toPMF` through with `dirac_step`, split the branch's `if`s (when
any), then finish each case from the hypotheses in context (inductive
hypotheses, guard conditions) and the `@[spec_transport]` lemmas.
Best-effort: any leftover goal is exactly the missing mathematics
(typically a guard that needs `omega` before a transport lemma
applies). -/
scoped macro "dirac_finish" : tactic =>
  `(tactic| (dirac_step <;> (try split_ifs) <;>
      simp_all [spec_transport, dirac_simp]))

-- Smoke test: a branch with no case split collapses outright.
example {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (a : ℕ) :
    inst.toPMF (pure a >>= fun x => (pure x : M ℕ)) = PMF.pure a := by
  dirac_finish

end ARA
