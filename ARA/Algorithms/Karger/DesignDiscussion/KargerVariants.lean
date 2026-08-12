/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Correctness.Amplify
import ARA.Helpers.MultiGraph
import Mathlib.Data.Sym.Sym2.Order

/-!
# Karger with a pluggable contraction rule

The main `Karger` file runs the contraction loop against an abstract
pick and reports the cut itself. This exhibit runs the same algorithm under every *representative-style*
contraction (the two endpoints of the drawn edge are replaced by a
single vertex `w` of the same type) and shows that the entire
analysis is a function of one choice: how `w` is picked.

A `MergeRule` packages that choice (`pick`) together with the single
obligation the generic cut theory of `ARA.Helpers.MultiGraph` needs:
the picked vertex collides with no *untouched* vertex (`fresh`).
Everything else is proved here once, for every rule:

* `kargerVia_value_ge`: one-sided error: the reported value never
  undershoots the minimum-cut value;
* `kargerVia_success_prob`: the reported value *is* the minimum-cut
  value with probability at least `2 / (n (n - 1))`;
* `kargerVia_amplified`: keeping the smallest of `k` reported values
  succeeds with probability at least `1 − (1 − 2/(n(n−1)))^k`;
* `kargerVia_cost_le`: expected cost at most `(n - 2) * m`.

The three rules (`orderRule`, `enumRule`, `freshRule`, at the end of
this file) each discharge `fresh` in their own way, which is precisely
where each model pays its price (a `LinearOrder`, an injective
labelling, a name supply). `Karger.lean` runs the same rules with
cut-level output.

## What a rename model *cannot* give

The merged vertex carries no history, so the algorithm here returns
only the cut value (`M ℕ`), not the cut: recovering the partition
would need a representative map threaded through the recursion — which
is exactly what `Karger.lean` does (`rep`). The supervertex
alternative, where a vertex *is* the set of original vertices merged
into it, is a design narrative now: `Variants.lean` records the
discussion, and the supervertex section of
`ARA/Helpers/MultiGraph.lean` keeps the exhibit. See
`KargerVariants.md` for the full comparison.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-- A representative-style contraction rule: how to pick the merged
vertex for a drawn edge, together with the one obligation the generic
cut theory needs: the pick collides with no *untouched* vertex (it
may well be one of the two endpoints). -/
structure MergeRule (α : Type) [DecidableEq α] where
  /-- The merged vertex for the edge `e` of the current graph `g`. -/
  pick : MultiGraph α → Sym2 α → α
  /-- Freshness: the pick is never a vertex that survives untouched. -/
  fresh : ∀ {g : MultiGraph α} {e : Sym2 α}, g.WF → e ∈ g.edges →
    pick g e ∉ g.verts.filter (· ∉ e)

variable (R : MergeRule α)

/-! ## One contraction step under a rule -/

/-- Contract the `i`-th listed edge into the vertex the rule picks. -/
def contractVia (g : MultiGraph α) (i : Fin g.edges.length) : MultiGraph α :=
  g.contractEdgeTo g.edges[(i : ℕ)] (R.pick g g.edges[(i : ℕ)])

theorem MultiGraph.WF.contractVia {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) : (contractVia R g i).WF :=
  hwf.contractEdgeTo

lemma card_verts_contractVia {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) :
    (contractVia R g i).verts.card + 1 = g.verts.card :=
  card_verts_contractEdgeTo (R.fresh hwf (List.getElem_mem _))
    (hwf.incidence _ (List.getElem_mem _)) (hwf.loopless _ (List.getElem_mem _))

lemma length_edges_contractVia_le (g : MultiGraph α) (i : Fin g.edges.length) :
    (contractVia R g i).edges.length ≤ g.edges.length :=
  length_edges_contractEdgeTo_le ..

lemma minCutValue_le_contractVia {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (contractVia R g i).minCutValue :=
  minCutValue_le_contractEdgeTo hwf (R.fresh hwf (List.getElem_mem _))
    (hwf.incidence _ (List.getElem_mem _)) (hwf.loopless _ (List.getElem_mem _))
    h3

/-! ## Algorithm -/

/-- Perform `fuel` uniformly-random edge contractions under the rule
(stopping early if no edge remains). Each pass ticks once per edge,
exactly like the pick loop in `Karger.lean`. -/
def contractAuxVia {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → MultiGraph α → M (MultiGraph α)
  | 0, g => pure g
  | k + 1, g =>
    if h : 0 < g.edges.length then do
      MonadCost.tick g.edges.length
      let i ← randIdx g.edges h
      contractAuxVia k (contractVia R g i)
    else
      pure g

/-- Karger's algorithm under a contraction rule. Contract random
edges until two vertices remain and report the number of surviving
parallel edges, the value of the cut the run found. The vertex type
never changes, but the output is only the value: the merged
vertices carry no history. -/
def KargerVia {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M ℕ := do
  let h ← contractAuxVia R (g.verts.card - 2) g
  pure h.edges.length

/-! ## Helper lemmas for the analysis

The `>>=`/`pure`-vs-`PMF.bind`/`PMF.pure` bridges (`pmf_bind_eq`,
`pmf_pure_eq`) come from `ARA.Infrastructure.Tactics`. -/

/-- A `Fin`-indexed sum of a function of the list entries is the sum
over the mapped list. -/
lemma sum_univ_getElem {β : Type} (l : List β) (f : β → ℝ≥0∞) :
    (∑ i : Fin l.length, f l[(i : ℕ)]) = (l.map f).sum := by
  rw [← List.ofFn_getElem_eq_map l f, List.sum_ofFn]

/-- Summing `q` over the entries *not* satisfying `p` counts them. -/
lemma sum_map_ite_zero {β : Type} (p : β → Prop) [DecidablePred p]
    (q : ℝ≥0∞) :
    ∀ l : List β,
      (l.map fun e => if p e then 0 else q).sum =
        ((l.length - l.countP fun e => decide (p e) : ℕ) : ℝ≥0∞) * q
  | [] => by simp
  | e :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_ite_zero p q l]
    have hle : (l.countP fun e => decide (p e)) ≤ l.length :=
      List.countP_le_length
    by_cases hp : p e
    · have hc : ((e :: l).countP fun e => decide (p e)) =
          (l.countP fun e => decide (p e)) + 1 := by
        simp [hp]
      rw [if_pos hp, hc, zero_add, List.length_cons]
      congr 2
      omega
    · have hc : ((e :: l).countP fun e => decide (p e)) =
          (l.countP fun e => decide (p e)) := by
        simp [hp]
      rw [if_neg hp, hc, List.length_cons]
      have h1 : l.length + 1 - (l.countP fun e => decide (p e)) =
          (l.length - (l.countP fun e => decide (p e))) + 1 := by omega
      rw [h1, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- The arithmetic core of the survival induction: if the current graph
has `m > 0` edges and `k + s + 3` vertices, and the fixed minimum
cut has `c ≤ m` crossing edges with `c * (k + s + 3) ≤ 2 * m` (the
counting bound), then picking a non-crossing edge and surviving
afterwards with probability `N / ((k+s+2)(k+s+1))` beats
`N / ((k+s+3)(k+s+2))`. -/
lemma step_bound {m c k s N : ℕ} (hm : 0 < m) (hc : c ≤ m)
    (hbound : c * (k + s + 3) ≤ 2 * m) :
    ((N : ℕ) : ℝ≥0∞) / (((k + s + 3) * (k + s + 2) : ℕ) : ℝ≥0∞) ≤
      ((m : ℕ) : ℝ≥0∞)⁻¹ *
        (((m - c : ℕ) : ℝ≥0∞) *
          (((N : ℕ) : ℝ≥0∞) / (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞))) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + c := ⟨m - c, by omega⟩
  have hdc : d + c - c = d := by omega
  rw [hdc]
  -- `(d + c)(k + s + 1) ≤ d(k + s + 3)` from the counting bound.
  have hkey : (d + c) * (k + s + 1) ≤ d * (k + s + 3) := by nlinarith
  -- Rewrite the right-hand side as a single natural fraction.
  have hrw : (((d + c : ℕ) : ℝ≥0∞))⁻¹ *
      (((d : ℕ) : ℝ≥0∞) *
        (((N : ℕ) : ℝ≥0∞) / (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞))) =
      ((d * N : ℕ) : ℝ≥0∞) /
        (((d + c) * ((k + s + 2) * (k + s + 1)) : ℕ) : ℝ≥0∞) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul (d + c), Nat.cast_mul d,
      ENNReal.mul_inv (Or.inl (by exact_mod_cast hm.ne'))
        (Or.inl (ENNReal.natCast_ne_top _))]
    push_cast
    ring
  rw [hrw]
  -- Cross-multiply and conclude in `ℕ`.
  refine ennreal_div_le_div_nat (by positivity) (by positivity) ?_
  have h2 := Nat.mul_le_mul_left (N * (k + s + 2)) hkey
  calc N * ((d + c) * ((k + s + 2) * (k + s + 1)))
      = N * (k + s + 2) * ((d + c) * (k + s + 1)) := by ring
    _ ≤ N * (k + s + 2) * (d * (k + s + 3)) := h2
    _ = d * N * ((k + s + 3) * (k + s + 2)) := by ring

/-! ## The run invariant -/

/-- The run invariant of the rule-driven contraction loop, for an
arbitrary stopping target `t` with fuel `k = card − t` (`KargerVia`
reads it at `t = 2`): well-formedness, the card window, a genuine end
state, monotonicity of the edge count and of the minimum-cut value.
(No `Tracks`: a rename model has no partition to track.) -/
theorem support_contractAuxVia
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (t : ℕ) (ht2 : 2 ≤ t) :
    ∀ (k : ℕ) (g : MultiGraph α), g.WF → g.verts.card = k + t →
      ∀ h ∈ 𝒟_{M}[contractAuxVia R k g].support,
        h.WF ∧ t ≤ h.verts.card ∧ h.verts.card ≤ g.verts.card ∧
          (h.verts.card = t ∨ h.edges = []) ∧
          h.edges.length ≤ g.edges.length ∧
          g.minCutValue ≤ h.minCutValue := by
  intro k g
  induction k, g using contractAuxVia.induct (R := R) with
  | case1 g =>
    intro hwf hcard h hh
    rw [contractAuxVia.eq_1] at hh
    toPMF_step at hh
    subst hh
    exact ⟨hwf, by omega, le_rfl, Or.inl (by omega), le_rfl, le_rfl⟩
  | case2 k g hm ih =>
    intro hwf hcard h hh
    rw [contractAuxVia.eq_2, dif_pos hm] at hh
    simp only [toPMF_simp, inst.toPMF_randIdx] at hh
    obtain ⟨i, -, hi⟩ := hh
    have hcard' := card_verts_contractVia R hwf i
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih i (hwf.contractVia R i)
      (by omega) h hi
    exact ⟨h1, h2, by omega, h4,
      le_trans h5 (length_edges_contractVia_le R g i),
      le_trans (minCutValue_le_contractVia R hwf i (by omega)) h6⟩
  | case3 k g hm =>
    intro hwf hcard h hh
    rw [contractAuxVia.eq_2, dif_neg hm] at hh
    toPMF_step at hh
    subst hh
    exact ⟨hwf, by omega, le_rfl,
      Or.inr (List.eq_nil_of_length_eq_zero (by omega)), le_rfl, le_rfl⟩

/-! ## Survival of the minimum cut

The proof is Karger's, verbatim: fix a minimum cut, count its crossing
edges, contract a non-crossing one. Only the per-step transport lemma
(`minCutValue_contractEdgeTo_of_notCrossing`) knows which model runs.
Note there is no disjointness hypothesis: freshness comes from the
rule. -/

theorem success_contractAuxVia
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (s : ℕ) :
    ∀ (k : ℕ) (g : MultiGraph α), g.WF →
      g.verts.card = k + (s + 2) →
      (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
          (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞) ≤
        ℙ_{M}[contractAuxVia R k g ∈ {h | h.minCutValue = g.minCutValue}] := by
  intro k g
  induction k, g using contractAuxVia.induct (R := R) with
  | case1 g =>
    intro hwf hcard
    have hone : prob (PMF.pure g)
        {h : MultiGraph α | h.minCutValue = g.minCutValue} = 1 :=
      prob_pure_of_mem rfl
    rw [contractAuxVia.eq_1, inst.toPMF_pure, pmf_pure_eq, hone,
      show ((0 + s + 2) * (0 + s + 1) : ℕ) = ((s + 2) * (s + 1) : ℕ) by ring,
      ENNReal.div_self (Nat.cast_ne_zero.mpr (by positivity))
        (ENNReal.natCast_ne_top _)]
  | case2 k g hm ih =>
    intro hwf hcard
    · -- Main case: pick a uniform edge, recurse.
      rw [contractAuxVia.eq_2, dif_pos hm, toPMF_tick_bind,
        prob_toPMF_randIdx_bind]
      -- Fix a minimum cut `S`.
      obtain ⟨S, hS, hSval⟩ := exists_minCut g (by omega)
      -- The branch success probability as a function of the contracted edge.
      set F : Sym2 α → ℝ≥0∞ := fun e =>
        prob (inst.toPMF (contractAuxVia R k
            (g.contractEdgeTo e (R.pick g e)) : M _))
          {h | h.minCutValue = g.minCutValue} with hF
      have hsum : (∑ i : Fin g.edges.length,
          prob (inst.toPMF (contractAuxVia R k (contractVia R g i) : M _))
            {h | h.minCutValue = g.minCutValue}) = (g.edges.map F).sum := by
        rw [← sum_univ_getElem g.edges F]
        rfl
      rw [hsum]
      -- Every non-crossing edge contributes at least the IH bound.
      have hbranch : ∀ e ∈ g.edges,
          (if Crossing S e then 0 else
            (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
              (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞)) ≤ F e := by
        intro e he
        by_cases hcr : Crossing S e
        · simp [hcr]
        · rw [if_neg hcr, hF]
          obtain ⟨i, hilen, rfl⟩ := List.getElem_of_mem he
          have hmem := hwf.incidence _ he
          have hnd := hwf.loopless _ he
          have hcard' : (g.contractEdgeTo g.edges[i]
              (R.pick g g.edges[i])).verts.card = k + (s + 2) := by
            have := card_verts_contractEdgeTo (R.fresh hwf he) hmem hnd
            omega
          rw [← minCutValue_contractEdgeTo_of_notCrossing hwf
            (R.fresh hwf he) hmem hnd (by omega) hS hSval hcr]
          exact ih ⟨i, hilen⟩ hwf.contractEdgeTo hcard'
      -- Count the non-crossing edges: `m - c` of them.
      have hcount : (g.edges.map fun e =>
          (if Crossing S e then 0 else
            (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
              (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞))).sum =
          ((g.edges.length - g.cutValue S : ℕ) : ℝ≥0∞) *
            ((((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
              (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞)) :=
        sum_map_ite_zero (Crossing S) _ g.edges
      -- Chain the bounds.
      refine le_trans ?_ (mul_le_mul' le_rfl
        (le_trans (le_of_eq hcount.symm) (List.sum_le_sum hbranch)))
      rw [hSval]
      -- Arithmetic: the counting bound closes the step.
      have hc_le : g.minCutValue ≤ g.edges.length :=
        minCutValue_le_length g (by omega)
      have hbound : g.minCutValue * (k + s + 3) ≤ 2 * g.edges.length := by
        have := card_mul_minCutValue_le g hwf (by omega)
        rw [hcard] at this
        calc g.minCutValue * (k + s + 3)
            = (k + 1 + (s + 2)) * g.minCutValue := by ring
          _ ≤ 2 * g.edges.length := this
      have := step_bound (N := (s + 2) * (s + 1)) hm hc_le hbound
      rw [show ((k + 1 + s + 2) * (k + 1 + s + 1) : ℕ) =
          ((k + s + 3) * (k + s + 2) : ℕ) by ring]
      exact this
  | case3 k g hm =>
    intro _ _
    · -- No edges left: the graph is unchanged, success with probability `1`.
      have hone : prob (PMF.pure g)
          {h : MultiGraph α | h.minCutValue = g.minCutValue} = 1 :=
        prob_pure_of_mem rfl
      rw [contractAuxVia.eq_2, dif_neg hm, inst.toPMF_pure, pmf_pure_eq, hone]
      rw [ENNReal.div_le_iff
        (Nat.cast_ne_zero.mpr (by positivity :
          ((k + 1 + s + 2) * (k + 1 + s + 1) : ℕ) ≠ 0))
        (ENNReal.natCast_ne_top _), one_mul]
      exact_mod_cast Nat.mul_le_mul (by omega : s + 2 ≤ k + 1 + s + 2)
        (by omega : s + 1 ≤ k + 1 + s + 1)

/-! ## Main theorems -/

private lemma kargerVia_eq_map {M} [Monad M] [LawfulMonad M] [RandMonad M]
    [MonadCost ℕ M] (g : MultiGraph α) :
    (KargerVia R g : M ℕ)
      = (fun h => h.edges.length) <$>
          contractAuxVia R (g.verts.card - 2) g := by
  rw [map_eq_bind_pure_comp]
  rfl

/-- One-sided error. Every value a run reports is at least the
minimum-cut value. -/
theorem kargerVia_value_ge
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ n ∈ 𝒟_{M}[KargerVia R g].support, g.minCutValue ≤ n := by
  intro n hn
  unfold KargerVia at hn
  obtain ⟨h, hh, rfl⟩ := mem_support_toPMF_bind_pure.mp hn
  obtain ⟨hwf', h2', -, -, -, hmin⟩ :=
    support_contractAuxVia (M := M) R 2 le_rfl (g.verts.card - 2) g hwf
      (by omega) h hh
  exact le_trans hmin (minCutValue_le_length h h2')

/-- A single run under any rule *reports the minimum-cut value* with
probability at least `2 / (n (n - 1))`. -/
theorem kargerVia_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerVia R g ∈ {n | n = g.minCutValue}] := by
  have hmain := success_contractAuxVia (M := M) R (s := 0)
    (g.verts.card - 2) g hwf (by omega)
  rw [show ((0 + 2) * (0 + 1) : ℕ) = 2 by norm_num,
    show g.verts.card - 2 + 0 + 2 = g.verts.card by omega,
    show g.verts.card - 2 + 0 + 1 = g.verts.card - 1 by omega] at hmain
  rw [kargerVia_eq_map, LawfulRandMonad.toPMF_map, pmf_map_eq, prob_map]
  refine le_trans (by exact_mod_cast hmain)
    (prob_mono_of_support fun h hh hev => ?_)
  obtain ⟨hwf', h2', -, hend, -, -⟩ :=
    support_contractAuxVia (M := M) R 2 le_rfl (g.verts.card - 2) g hwf
      (by omega) h hh
  show h.edges.length = g.minCutValue
  rcases hend with hcard2 | hnil
  · exact (length_eq_minCutValue_of_card_two hwf' hcard2).trans hev
  · have hlen : h.edges.length = 0 := by rw [hnil]; rfl
    have hmin0 : h.minCutValue = 0 :=
      Nat.le_zero.mp (le_trans (minCutValue_le_length h h2') (le_of_eq hlen))
    rw [hlen, ← hev, hmin0]

/-- Amplified. Keep the smallest of `k` reported values: the
result is the minimum-cut value with probability at least
`1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerVia_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify min k (KargerVia R g) = g.minCutValue] :=
  amplify_min_success (kargerVia_value_ge R g hwf h2)
    (by simpa [Set.setOf_eq_eq_singleton, prob_singleton]
      using kargerVia_success_prob R g hwf h2) k

/-! ## Complexity -/

/-- Expected cost of the rule-driven contraction loop: at most
`fuel * m`, for arbitrary graphs. -/
lemma expected_cost_contractAuxVia
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (k : ℕ) (g : MultiGraph α),
      𝔼_{M}[cost (contractAuxVia R k g : TimeMT ℕ M (MultiGraph α))] ≤
        (k : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  intro k g
  induction k, g using contractAuxVia.induct (R := R) with
  | case1 g =>
    rw [contractAuxVia.eq_1, expected_cost_toPMF_pure]
    exact bot_le
  | case2 k g hm ih =>
    rw [contractAuxVia.eq_2, dif_pos hm, MonadCost.tick_timeMT,
      expected_cost_toPMF_tick_bind, expected_cost_uniform_step]
    refine le_trans (add_le_add le_rfl (uniform_avg_le_of_forall
      (fun i => le_trans (ih i) (mul_le_mul' le_rfl
        (Nat.cast_le.mpr (length_edges_contractVia_le R g i)))) hm.ne')) ?_
    rw [show ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 by push_cast; ring]
    rw [add_mul, one_mul, add_comm]
  | case3 k g hm =>
    rw [contractAuxVia.eq_2, dif_neg hm, expected_cost_toPMF_pure]
    exact bot_le

/-- Expected complexity: with one tick per edge scanned during a
contraction pass, any rule runs in expected cost at most `(n - 2) * m`.
This holds for arbitrary inputs. -/
theorem kargerVia_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) :
    𝔼_{M}[cost KargerVia R g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  unfold KargerVia
  rw [expected_cost_toPMF_bind_pure]
  exact expected_cost_contractAuxVia R _ g

/-! ## The three merge rules

Each rule discharges `fresh` in its own way, which is where each model
pays: a `LinearOrder` on the vertex type, an injective labelling as
data, a name supply pinning the type to `ℕ`. `KargerVia` runs them at
value-level output here; `Karger.lean` runs them at cut level. -/

section OrderRule

variable [LinearOrder α]

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

/-- The order rule: merge into the smaller endpoint. Freshness is
trivial, the pick is an endpoint, hence not an untouched vertex. -/
def orderRule : MergeRule α where
  pick _ e := e.inf
  fresh _ _ h := (Finset.mem_filter.mp h).2 (sym2_inf_mem _)

end OrderRule

/-- The endpoint of smaller label, well-defined on the unordered edge
*because* the labelling is injective: a tie forces the endpoints to be
equal. -/
def enumPick (ℓ : α ↪ ℕ) : Sym2 α → α :=
  Sym2.lift ⟨fun u v => if ℓ u ≤ ℓ v then u else v, fun u v => by
    show (if ℓ u ≤ ℓ v then u else v) = if ℓ v ≤ ℓ u then v else u
    rcases lt_trichotomy (ℓ u) (ℓ v) with h | h | h
    · rw [if_pos h.le, if_neg (not_le.mpr h)]
    · cases ℓ.injective h
      simp
    · rw [if_neg (not_le.mpr h), if_pos h.le]⟩

omit [DecidableEq α] in
/-- The pick is always one of the two endpoints. -/
lemma enumPick_mem (ℓ : α ↪ ℕ) (e : Sym2 α) : enumPick ℓ e ∈ e := by
  induction e with
  | _ u v =>
    show (if ℓ u ≤ ℓ v then u else v) ∈ s(u, v)
    split_ifs
    · exact Sym2.mem_mk_left u v
    · exact Sym2.mem_mk_right u v

/-- The enumeration rule: merge into the endpoint of smaller label.
Freshness is trivial, the pick is an endpoint. -/
def enumRule (ℓ : α ↪ ℕ) : MergeRule α where
  pick _ e := enumPick ℓ e
  fresh _ _ h := (Finset.mem_filter.mp h).2 (enumPick_mem _ _)

/-- The fresh-name rule on `ℕ`: the merged vertex is one past the
largest vertex ever seen, never previously used. The freshness
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

/-- Demo graph: two triangles joined by a single bridge, the global
minimum cut is `1` (the bridge). -/
def kargerDemo : MultiGraph ℕ where
  verts := {0, 1, 2, 3, 4, 5}
  edges := [s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3), s(2, 3)]

/-! ### A demo vertex type without order

Six cities, no `LinearOrder` anywhere: the labelling is data. Same
shape as `kargerDemo`, two triangles joined by one bridge, minimum
cut `1`. -/

inductive City | zrh | gva | bsl | ber | lug | lau
  deriving DecidableEq

open City in
/-- An explicit injective labelling, data handed to the algorithm. -/
def cityLabel : City ↪ ℕ :=
  ⟨fun c => match c with
    | zrh => 0 | gva => 1 | bsl => 2 | ber => 3 | lug => 4 | lau => 5,
   fun a b h => by cases a <;> cases b <;> simp_all⟩

open City in
def cityDemo : MultiGraph City where
  verts := {zrh, gva, bsl, ber, lug, lau}
  edges := [s(zrh, gva), s(gva, bsl), s(bsl, zrh),
            s(ber, lug), s(lug, lau), s(lau, ber), s(bsl, ber)]

end ARA
