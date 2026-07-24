/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Algorithms.Karger.KargerVariants
import Mathlib.Data.Sym.Sym2.Order

/-!
# Karger, order model: merge into the smaller endpoint

The contraction rule of the original ARA Karger (before the
supervertex migration): the drawn edge's endpoints merge into their
`inf`. The merge is symmetric — `inf` is commutative — so it is a
genuine function of the unordered edge, and the freshness obligation
is trivial (the pick *is* an endpoint).

**The price is visible in every statement below**: the blanket
`[LinearOrder α]` hypothesis, an assumption with no mathematical
content for the min-cut problem — the graph does not care that its
vertices are ordered. And the output is only the cut *value*: the
surviving `inf`-representatives carry no history, so the partition
would need a representative map threaded through the recursion (this
is exactly the bookkeeping the supervertex model deletes).
-/

namespace ARA

open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α] [LinearOrder α]

omit [DecidableEq α] in
/-- The `inf` of an unordered pair is one of its elements. -/
lemma sym2_inf_mem (e : Sym2 α) : e.inf ∈ e := by
  induction e with
  | _ a b =>
    rw [Sym2.inf_mk]
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h]
      exact Sym2.mem_mk_left a b
    · rw [inf_eq_right.mpr h]
      exact Sym2.mem_mk_right a b

/-- **The order rule**: merge into the smaller endpoint. Freshness is
trivial — the pick is an endpoint, hence not an untouched vertex. -/
def orderRule : MergeRule α where
  pick _ e := e.inf
  fresh _ _ h := (Finset.mem_filter.mp h).2 (sym2_inf_mem _)

/-- Karger's algorithm, merging into the smaller endpoint. -/
def KargerOrder {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M ℕ :=
  KargerVia orderRule g

-- IO version (executable): `ℕ` vertices are linearly ordered.
def KargerOrder_IO : MultiGraph ℕ → IO ℕ := KargerOrder

#eval KargerOrder_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF ℕ := KargerOrder

/-- One-sided error: the reported value never undershoots the
minimum-cut value. -/
theorem kargerOrder_value_ge
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ n ∈ 𝒟_{M}[KargerOrder g].support, g.minCutValue ≤ n :=
  kargerVia_value_ge orderRule g hwf h2

/-- A single run reports the minimum-cut value with probability at
least `2 / (n (n - 1))`. -/
theorem kargerOrder_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerOrder g ∈ {n | n = g.minCutValue}] :=
  kargerVia_success_prob orderRule g hwf h2

/-- Keeping the smallest of `k` reported values succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerOrder_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify min k (KargerOrder g) = g.minCutValue] :=
  kargerVia_amplified orderRule g hwf h2 k

/-- Expected cost at most `(n - 2) * m` — one tick per edge scanned. -/
theorem kargerOrder_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) :
    𝔼_{M}[cost KargerOrder g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  kargerVia_cost_le orderRule g

end ARA
