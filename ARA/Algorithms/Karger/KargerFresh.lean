/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Algorithms.Karger.KargerVariants

/-!
# Karger, fresh-vertex model: delete both endpoints, glue to a new one

The gluing picture of contraction: the drawn edge's two endpoints are
*erased* and a brand-new vertex takes their place, inheriting all
their edges. Nothing breaks in the recursion — the vertex type stays
put, the vertex count drops by one per step, and the whole analysis
below is inherited unchanged.

The costs live elsewhere, and this file makes both concrete:

* **The name supply.** A fresh vertex must come from somewhere. For an
  arbitrary vertex type this needs `Infinite α` plus choice —
  noncomputable, which would kill the `IO` reading. Computably, this
  file fixes `α := ℕ` and picks `max + 1`: the supply *is* `ℕ`'s
  order (`Finset.sup`). Freshness is an actual proof obligation here —
  compare the trivial obligations of the order/enumeration rules.
* **Anonymity.** The merged vertex carries no history, so the run's
  final two vertices are meaningless names and the output can only be
  the cut **value**. (In the supervertex model the final two vertices
  *are* the two sides of the cut.)

Done with the one canonical choice of new vertex that needs no supply
and forgets nothing — `w := u ∪ v` — this model *is* the supervertex
model of the main `Karger` file.
-/

namespace ARA

open scoped ENNReal
open MultiGraph

/-- **The fresh-name rule on `ℕ`**: the merged vertex is one past the
largest vertex ever seen — never previously used. The freshness
obligation is genuine (compare `orderRule`/`enumRule`), and the supply
is `ℕ`'s order in disguise. -/
def freshRule : MergeRule ℕ where
  pick g _ := g.verts.sup id + 1
  fresh := by
    intro g e _ _ h
    obtain ⟨hv, -⟩ := Finset.mem_filter.mp h
    have := Finset.le_sup (f := id) hv
    simp only [id_eq] at this
    omega

/-- Karger's algorithm, gluing to fresh vertices. -/
def KargerFresh {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph ℕ) : M ℕ :=
  KargerVia freshRule g

-- IO version (executable)
def KargerFresh_IO : MultiGraph ℕ → IO ℕ := KargerFresh

#eval KargerFresh_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF ℕ := KargerFresh

/-- One-sided error: the reported value never undershoots the
minimum-cut value. -/
theorem kargerFresh_value_ge
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph ℕ) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ n ∈ 𝒟_{M}[KargerFresh g].support, g.minCutValue ≤ n :=
  kargerVia_value_ge freshRule g hwf h2

/-- A single run reports the minimum-cut value with probability at
least `2 / (n (n - 1))`. -/
theorem kargerFresh_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph ℕ) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerFresh g ∈ {n | n = g.minCutValue}] :=
  kargerVia_success_prob freshRule g hwf h2

/-- Keeping the smallest of `k` reported values succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerFresh_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph ℕ) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify min k (KargerFresh g) = g.minCutValue] :=
  kargerVia_amplified freshRule g hwf h2 k

/-- Expected cost at most `(n - 2) * m` — one tick per edge scanned. -/
theorem kargerFresh_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph ℕ) :
    𝔼_{M}[cost KargerFresh g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  kargerVia_cost_le freshRule g

end ARA
