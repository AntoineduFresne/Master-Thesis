/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Randomness.LawfulRandMonad
import ARA.Infrastructure.Complexity.MonadCost

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
4. **Discharge the branch**: `toPMF_step` pushes `toPMF` through the
   monadic structure (lawful `tick`s vanish, `bind`/`pure`
   distribute); close each case with the inductive hypotheses and the
   transport lemmas — or try `dirac_finish`, which attempts all of
   step 4 at once and leaves open exactly the missing mathematics.

## Distributional correctness (Monte Carlo algorithms)

When the output is genuinely random (e.g. `Karger`), correctness is a
property of the distribution: typically a support statement
(one-sided error) plus a success-probability bound, and for the exact
tier the full output law. The recipe mirrors the Dirac one — unfold,
peel (`toPMF_step` / `toPMF_tick_bind`), uniform-average the pivot,
discharge each branch, count — with these generic primitives:

* `toPMF_randIdx_bind_apply` — the output probability is the uniform
  average of the branch probabilities (probabilistic analogue of
  `expected_cost_uniform_step`);
* `le_toPMF_randIdx_bind` — lower-bound the success probability by a
  single good pivot;
* `support_toPMF_randIdx_bind` — the support is the union of the
  branch supports;
* `toPMF_bind_pure_apply` / `toPMF_map_apply` (+ their `_eq_zero`
  off-range forms) — pure post-processing along an injective function
  just transports probabilities;
* `mem_support_toPMF_bind_pure` — the support of a post-processed
  computation is the image of the support.
-/

namespace ARA

-- The `>>=`/`pure`/`<$>`-vs-`PMF.bind`/`PMF.pure`/`PMF.map` bridges
-- (`pmf_bind_eq`, `pmf_pure_eq`, `pmf_map_eq`) live in `ARA.Infrastructure.Tactics`;
-- register them for `toPMF_step` too.
attribute [toPMF_simp] pmf_bind_eq pmf_pure_eq pmf_map_eq

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

attribute [toPMF_simp] LawfulRandMonad.toPMF_pure
attribute [toPMF_simp] LawfulRandMonad.toPMF_bind
attribute [toPMF_simp] MonadCost.tick_default
attribute [toPMF_simp] pure_bind bind_pure map_pure

-- The support/pointwise tier: after `toPMF_pure`/`toPMF_bind` have
-- unfolded the subterms (simp works innermost-first), these finish a
-- membership or point-probability goal. Composite `toPMF`-level forms
-- (`mem_support_toPMF_pure`, `toPMF_pure_apply`, …) exist as named
-- API in `LawfulRandMonad` for `rw`-style use.
attribute [toPMF_simp] PMF.mem_support_pure_iff PMF.mem_support_bind_iff
attribute [toPMF_simp] PMF.pure_apply

/-- `toPMF_step` pushes `toPMF` through one algorithm branch: lawful
`tick`s vanish, `toPMF` distributes over `bind` and evaluates on
`pure`. What remains is the branch's case split plus the recursive
calls, to be closed by the inductive hypotheses and (for the Dirac
tier) the `@[spec_transport]` lemmas. Tier-agnostic: the same
normalizer drives Dirac, distributional and support proofs.

Accepts a location: `toPMF_step at h` normalizes a hypothesis — the
form support proofs (`h : out ∈ (…).support`) live on. -/
scoped syntax "toPMF_step" (Lean.Parser.Tactic.location)? : tactic

scoped macro_rules
  | `(tactic| toPMF_step $[$loc:location]?) =>
    `(tactic| simp only [toPMF_simp] $[$loc:location]?)

/-- `dirac_finish` attempts to close a branch goal outright: push
`toPMF` through with `toPMF_step`, split the branch's `if`s (when
any), then finish each case from the hypotheses in context (inductive
hypotheses, guard conditions) and the `@[spec_transport]` lemmas.
Best-effort: any leftover goal is exactly the missing mathematics
(typically a guard that needs `omega` before a transport lemma
applies). -/
scoped macro "dirac_finish" : tactic =>
  `(tactic| (toPMF_step <;> (try split_ifs) <;>
      simp_all [spec_transport, toPMF_simp]))

/-- `dirac_correct f` attempts a Dirac-correctness goal
`toPMF (f … : M _) = PMF.pure (spec …)` in one shot: functional
induction on `f` (`fun_induction` unfolds each equation and quantifies
the IHs over the pivot), collapse of the uniform pivot choice
(`toPMF_randIdx_bind_dirac`), then `dirac_finish` per branch, with a
`rfl` fallback for base cases whose spec reduces definitionally.

Any goal it leaves open is exactly the missing mathematics — state
the `@[spec_transport]` lemma it needs and it will close. -/
scoped macro "dirac_correct" f:ident : tactic =>
  `(tactic| (fun_induction $f <;>
      first
        | (refine toPMF_randIdx_bind_dirac fun i => ?_) <;> dirac_finish
        | dirac_finish
        | (toPMF_step; rfl)
        | skip))

-- Smoke test: a branch with no case split collapses outright.
example {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (a : ℕ) :
    inst.toPMF (pure a >>= fun x => (pure x : M ℕ)) = PMF.pure a := by
  dirac_finish

end ARA
