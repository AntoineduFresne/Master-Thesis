/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Correctness.Amplify
import ARA.Helpers.MultiGraph

/-!
# Karger's randomized minimum-cut algorithm

Karger's algorithm contracts a uniformly random edge until two
supervertices remain; the two survivors are the sides of a cut of the
original graph, the surviving parallel edges are its crossing edges,
and it is a global minimum cut with probability at least
`2 / (n (n - 1))`.

## Graph model

The algorithm runs on the **supervertex** graphs of
`ARA.Helpers.MultiGraph`: it first replaces every vertex by its
singleton (`MultiGraph.super`), and from then on each vertex of the
working graph is the `Finset` of original vertices merged into it.
Contracting an edge `s(S, T)` merges its endpoints into `S ∪ T` — a
symmetric operation, so contraction is a genuine function of the
*unordered* edge, with no order, no choice and no tie-break, and the
vertex type is preserved so the loop is a plain recursion. The
`Tracks` invariant (supervertices partition the original vertex set,
cuts flatten with equal value) is what a run maintains; the final
vertex set *is* the reported cut, with no extra bookkeeping.

Sampling a uniform edge from the edge list picks an edge with
probability proportional to its multiplicity (parallel edges are
repeated in the list).

## Architecture

As for `Quicksort` and `Quickselect`, a single definition
(`contractAux` / `Karger`) parameterized by `RandMonad` and
`MonadCost ℕ` serves as executable program (`M = IO`), as
specification (`M = PMF`), and as timed algorithm (`M = TimeMT ℕ M'`).

## Main results

* `karger_finds_min` — a single run returns an actual **minimum cut**
  — both surviving sides are genuine cuts of value exactly
  `minCutValue` — with probability at least `2 / (n (n - 1))`, where
  `n = g.verts.card`. Hence `O(n² log n)` independent repetitions find
  a minimum cut with high probability (`karger_amplified`).
* `karger_isCut` — one-sided error: *every* output is a partition into
  genuine cuts of the reported value, and the reported value never
  undershoots the minimum.
* `success_contractAux` — **survival of the minimum cut through
  partial contraction**, the kernel shared with Karger–Stein:
  contracting from `k + (s+2)` down to `s+2` supervertices preserves
  the minimum-cut value with probability at least
  `(s+2)(s+1) / ((k+s+2)(k+s+1))`. Karger is the case `s = 0`;
  Karger–Stein recurses on `s + 2 ≈ n/√2`, where the bound is `≥ 1/2`.
* `karger_cost_le` — with one tick per edge scanned during a
  contraction pass, the expected cost is at most `(n - 2) * m` where
  `m = g.edges.length`.

The success-probability proof follows the classical argument: fix a
minimum cut of value `c`; every vertex has degree at least `c` (else
its singleton would be a smaller cut), so `c * n ≤ 2 * m` by the
handshake identity and a uniformly random edge crosses the cut with
probability at most `2 / n`. Contracting a non-crossing edge preserves
the minimum-cut value (`minCutValue_contractEdge_of_notCrossing`), so
the product `∏ᵢ (1 - 2/(n - i))` telescopes to the stated bound.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-! ## Algorithm -/

/-- Perform `fuel` uniformly-random edge contractions (stopping early
if no edge remains). Each pass ticks once per edge: contracting
relabels and filters the whole edge list. -/
def contractAux {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → MultiGraph (Finset α) → M (MultiGraph (Finset α))
  | 0, g => pure g
  | k + 1, g =>
    if h : 0 < g.edges.length then do
      MonadCost.tick g.edges.length
      let i ← randIdx g.edges h
      contractAux k (g.contract i)
    else
      pure g

/-- **Karger's algorithm.** Contract uniformly random edges until two
supervertices remain, then return the **partition** they induce — each
surviving supervertex is the set of original vertices merged into it,
i.e. one side of the cut — together with the number of surviving
parallel edges (the cut's value). This is the textbook statement: the
algorithm finds a cut `{S, S̄}`, and reports its value. -/
def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) := do
  let h ← contractAux (g.verts.card - 2) g.super
  pure (h.verts, h.edges.length)

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed)
def Karger_IO : MultiGraph ℕ → IO (Finset (Finset ℕ) × ℕ) := Karger

/-- Demo graph: two triangles joined by a single bridge — the global
minimum cut is `1` (the bridge). -/
def kargerDemo : MultiGraph ℕ where
  verts := {0, 1, 2, 3, 4, 5}
  edges := [s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3), s(2, 3)]

#eval Karger_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) := Karger

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable)
def Karger_IO_Timed : MultiGraph ℕ → TimeMT ℕ IO (Finset (Finset ℕ) × ℕ) := Karger

#eval (Karger_IO_Timed kargerDemo).run

-- PMF timed version (noncomputable specification)
noncomputable example : MultiGraph ℕ → TimeMT ℕ PMF (Finset (Finset ℕ) × ℕ) := Karger

/-! ## Helper lemmas for the analysis

The `>>=`/`pure`-vs-`PMF.bind`/`PMF.pure` bridges (`pmf_bind_eq`,
`pmf_pure_eq`) come from `ARA.Infrastructure.Tactics`. -/

/-- A `Fin`-indexed sum of a function of the list entries is the sum
over the mapped list. -/
private lemma sum_univ_getElem {β : Type} (l : List β) (f : β → ℝ≥0∞) :
    (∑ i : Fin l.length, f l[(i : ℕ)]) = (l.map f).sum := by
  rw [← List.ofFn_getElem_eq_map l f, List.sum_ofFn]

/-- Summing `q` over the entries *not* satisfying `p` counts them. -/
private lemma sum_map_ite_zero {β : Type} (p : β → Prop) [DecidablePred p]
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
has `m > 0` edges and `k + s + 3` supervertices, and the fixed minimum
cut has `c ≤ m` crossing edges with `c * (k + s + 3) ≤ 2 * m` (the
counting bound), then picking a non-crossing edge and surviving
afterwards with probability `N / ((k+s+2)(k+s+1))` beats
`N / ((k+s+3)(k+s+2))`. -/
private lemma step_bound {m c k s N : ℕ} (hm : 0 < m) (hc : c ≤ m)
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

/-! ## The run invariant

Everything a finished run guarantees on its support: well-formedness,
at least two supervertices, a genuine end state (two supervertices or
no edges), and the `Tracks` partition invariant against the original
graph. -/

private lemma support_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α} :
    ∀ (k : ℕ) (g : MultiGraph (Finset α)), g.WF → g.verts.card = k + 2 →
      Tracks g₀ g →
      ∀ h ∈ 𝒟[contractAux k g | M].support,
        h.WF ∧ 2 ≤ h.verts.card ∧ (h.verts.card = 2 ∨ h.edges = []) ∧
          Tracks g₀ h := by
  intro k
  induction k with
  | zero =>
    intro g hwf hcard ht h hh
    rw [contractAux.eq_1] at hh
    toPMF_step at hh
    subst hh
    exact ⟨hwf, by omega, Or.inl hcard, ht⟩
  | succ k ih =>
    intro g hwf hcard ht h hh
    by_cases hm : 0 < g.edges.length
    · rw [contractAux.eq_2, dif_pos hm] at hh
      simp only [toPMF_simp, inst.toPMF_randIdx] at hh
      obtain ⟨i, -, hi⟩ := hh
      exact ih (g.contract i) (hwf.contract i)
        (by have := card_verts_contract hwf ht.disj i; omega)
        (ht.contract hwf i) h hi
    · rw [contractAux.eq_2, dif_neg hm] at hh
      toPMF_step at hh
      subst hh
      exact ⟨hwf, by omega,
        Or.inr (List.eq_nil_of_length_eq_zero (by omega)), ht⟩

/-! ## Survival of the minimum cut -/

/-- **Survival of the minimum cut through partial contraction** — the
kernel of both Karger's and Karger–Stein's analyses. Contracting a
well-formed supervertex graph with pairwise-disjoint supervertices
from `k + (s+2)` down to `s+2` supervertices preserves the minimum-cut
value with probability at least `(s+2)(s+1) / ((k+s+2)(k+s+1))`.

For `s = 0` (full contraction to two supervertices) this is Karger's
`2/(n(n−1))`; for `s + 2 ≈ n/√2` it is the `≥ 1/2` survival bound the
Karger–Stein recursion consumes. -/
theorem success_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (s : ℕ) :
    ∀ (k : ℕ) (g : MultiGraph (Finset α)), g.WF → SupDisjoint g →
      g.verts.card = k + (s + 2) →
      (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
          (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞) ≤
        ℙ[contractAux k g ∈ {h | h.minCutValue = g.minCutValue} | M] := by
  intro k
  induction k with
  | zero =>
    intro g hwf hdisj hcard
    have hone : prob (PMF.pure g)
        {h : MultiGraph (Finset α) | h.minCutValue = g.minCutValue} = 1 :=
      prob_pure_of_mem rfl
    rw [contractAux.eq_1, inst.toPMF_pure, pmf_pure_eq, hone,
      show ((0 + s + 2) * (0 + s + 1) : ℕ) = ((s + 2) * (s + 1) : ℕ) by ring,
      ENNReal.div_self (Nat.cast_ne_zero.mpr (by positivity))
        (ENNReal.natCast_ne_top _)]
  | succ k ih =>
    intro g hwf hdisj hcard
    by_cases hm : 0 < g.edges.length
    · -- Main case: pick a uniform edge, recurse.
      rw [contractAux.eq_2, dif_pos hm, toPMF_tick_bind, prob_toPMF_randIdx_bind]
      -- Fix a minimum cut `S`.
      obtain ⟨S, hS, hSval⟩ := exists_minCut g (by omega)
      -- The branch success probability as a function of the contracted edge.
      set F : Sym2 (Finset α) → ℝ≥0∞ := fun e =>
        prob (inst.toPMF (contractAux k (g.contractEdge e) : M _))
          {h | h.minCutValue = g.minCutValue} with hF
      have hsum : (∑ i : Fin g.edges.length,
          prob (inst.toPMF (contractAux k (g.contract i) : M _))
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
          have hmem := hwf.incidence e he
          have hnd := hwf.loopless e he
          have hcard' : (g.contractEdge e).verts.card = k + (s + 2) := by
            have := card_verts_contractEdge hdisj hmem hnd
            omega
          have hmc : (g.contractEdge e).minCutValue = g.minCutValue :=
            minCutValue_contractEdge_of_notCrossing hwf hdisj hmem hnd
              (by omega) hS hSval hcr
          have hih := ih (g.contractEdge e) hwf.contractEdge
            (hdisj.contractEdge hmem) hcard'
          rw [hmc] at hih
          exact hih
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
    · -- No edges left: the graph is unchanged, success with probability `1`.
      have hone : prob (PMF.pure g)
          {h : MultiGraph (Finset α) | h.minCutValue = g.minCutValue} = 1 :=
        prob_pure_of_mem rfl
      rw [contractAux.eq_2, dif_neg hm, inst.toPMF_pure, pmf_pure_eq, hone]
      rw [ENNReal.div_le_iff
        (Nat.cast_ne_zero.mpr (by positivity :
          ((k + 1 + s + 2) * (k + 1 + s + 1) : ℕ) ≠ 0))
        (ENNReal.natCast_ne_top _), one_mul]
      exact_mod_cast Nat.mul_le_mul (by omega : s + 2 ≤ k + 1 + s + 2)
        (by omega : s + 1 ≤ k + 1 + s + 1)

/-! ## Karger's theorem -/

private lemma karger_eq_map {M} [Monad M] [LawfulMonad M] [RandMonad M]
    [MonadCost ℕ M] (g : MultiGraph α) :
    (Karger g : M (Finset (Finset α) × ℕ))
      = (fun h => (h.verts, h.edges.length)) <$>
          contractAux (g.verts.card - 2) g.super := by
  rw [map_eq_bind_pure_comp]
  rfl

/-- Everything a single run guarantees, unconditionally: the reported
set is a partition into genuine cuts of `g`, each of value exactly the
reported number, and that number never undershoots the minimum. -/
theorem karger_isCut
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟[Karger g | M].support,
      (∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2) ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  unfold Karger at ho
  obtain ⟨h, hh, rfl⟩ := mem_support_toPMF_bind_pure.mp ho
  obtain ⟨hwf', h2', hend, ht⟩ :=
    support_contractAux (M := M) (g.verts.card - 2) g.super hwf.super
      (by rw [card_verts_super]; omega) (Tracks.super g) h hh
  refine ⟨fun S hS => ⟨ht.isCut_mem h2' hS, ht.cutValue_mem hwf' hend hS⟩, ?_⟩
  obtain ⟨S, hS⟩ := Finset.card_pos.mp (by omega : 0 < h.verts.card)
  rw [← ht.cutValue_mem hwf' hend hS]
  exact minCutValue_le (ht.isCut_mem h2' hS)

/-- A single run *reports the minimum-cut value* with probability at
least `2 / (n (n - 1))` — the value-level bound the induction proves;
`karger_finds_min` below is its cut-level (textbook) form. -/
theorem karger_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[Karger g ∈ {o | o.2 = g.minCutValue} | M] := by
  have hmain := success_contractAux (M := M) (s := 0) (g.verts.card - 2) g.super
    hwf.super (supDisjoint_super g) (by rw [card_verts_super]; omega)
  rw [minCutValue_super h2,
    show ((0 + 2) * (0 + 1) : ℕ) = 2 by norm_num,
    show g.verts.card - 2 + 0 + 2 = g.verts.card by omega,
    show g.verts.card - 2 + 0 + 1 = g.verts.card - 1 by omega] at hmain
  rw [karger_eq_map, LawfulRandMonad.toPMF_map, pmf_map_eq, prob_map]
  refine le_trans (by exact_mod_cast hmain)
    (prob_mono_of_support fun h hh hev => ?_)
  obtain ⟨hwf', h2', hend, -⟩ :=
    support_contractAux (M := M) (g.verts.card - 2) g.super hwf.super
      (by rw [card_verts_super]; omega) (Tracks.super g) h hh
  -- On the support, "the minimum cut survived" implies "the reported
  -- edge count is the original minimum-cut value".
  show h.edges.length = g.minCutValue
  rcases hend with hcard2 | hnil
  · exact (length_eq_minCutValue_of_card_two hwf' hcard2).trans hev
  · have hlen : h.edges.length = 0 := by rw [hnil]; rfl
    have hmin0 : h.minCutValue = 0 :=
      Nat.le_zero.mp (le_trans (minCutValue_le_length h h2') (le_of_eq hlen))
    rw [hlen, ← hev, hmin0]

/-- **Karger's theorem.** A single run returns an actual **minimum
cut** — every reported side is a genuine cut of `g` of value exactly
`minCutValue` — with probability at least `2 / (n (n − 1))`. Obtained
from the value-level bound by strengthening the event along the run's
support invariant (`karger_isCut`), not by re-induction. -/
theorem karger_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[Karger g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue} | M] := by
  refine le_trans (karger_success_prob g hwf h2)
    (prob_mono_of_support fun o ho hval => ?_)
  obtain ⟨hall, -⟩ := karger_isCut g hwf h2 o ho
  exact fun S hS => ⟨(hall S hS).1, (hall S hS).2.trans hval⟩

/-- **Amplified Karger.** Run the algorithm `k` times and keep the
cut of smallest reported value: the result reports the minimum-cut
value with probability at least `1 − (1 − 2/(n(n−1)))^k`, so
`O(n² log n)` repetitions find a minimum cut with high probability.
Selecting by the reported value (`argmin Prod.snd`) costs nothing —
the run already computed it. -/
theorem karger_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ[amplify (argmin Prod.snd) k (Karger g)
          ∈ {o | o.2 = g.minCutValue} | M] :=
  amplify_argmin_success
    (fun o ho => (karger_isCut g hwf h2 o ho).2)
    (karger_success_prob g hwf h2) k

/-! ## Complexity

Each contraction round ticks `m' = ` (current number of edges): the
contraction pass relabels and filters the whole edge list. Since
contraction never adds edges, every round costs at most `m` and there
are at most `n - 2` rounds, giving expected cost at most `(n - 2) m`.
The bound holds for **arbitrary** graphs — no well-formedness needed. -/

/-- Expected cost of the contraction loop: at most `fuel * m`. -/
private lemma expected_cost_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (k : ℕ) (g : MultiGraph (Finset α)),
      𝔼_runtime[(contractAux k g : TimeMT ℕ M (MultiGraph (Finset α)))] ≤
        (k : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  intro k
  induction k with
  | zero =>
    intro g
    rw [contractAux.eq_1, expected_cost_toPMF_pure]
    exact bot_le
  | succ k ih =>
    intro g
    by_cases hm : 0 < g.edges.length
    · rw [contractAux.eq_2, dif_pos hm, MonadCost.tick_timeMT,
        expected_cost_toPMF_tick_bind, expected_cost_uniform_step]
      -- Each branch recurses on at most `m` edges, so the uniform
      -- average of the branch costs is at most `k * m`.
      refine le_trans (add_le_add le_rfl (uniform_avg_le_of_forall
        (fun i => le_trans (ih (g.contract i)) (mul_le_mul' le_rfl
          (Nat.cast_le.mpr (length_edges_contract_le g i)))) hm.ne')) ?_
      rw [show ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 by push_cast; ring]
      rw [add_mul, one_mul, add_comm]
    · rw [contractAux.eq_2, dif_neg hm, expected_cost_toPMF_pure]
      exact bot_le

/-- **Expected complexity of Karger's algorithm.** With one tick per
edge scanned during a contraction pass, running `Karger` on a graph
with `n` vertices and `m` edges costs at most `(n - 2) * m` in
expectation — for arbitrary inputs. -/
theorem karger_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) :
    𝔼_runtime[Karger g | M] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  unfold Karger
  rw [expected_cost_toPMF_bind_pure]
  refine le_trans (expected_cost_contractAux _ g.super) ?_
  exact le_of_eq (by rw [length_edges_super])

/-- Finiteness of the expected cost — a free corollary of the
`(n - 2) m` bound. -/
lemma expected_cost_karger_ne_top
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] (g : MultiGraph α) :
    𝔼_runtime[Karger g | M] ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le g)

/-- Real-valued corollary: the expected cost is at most `(n - 2) * m`. -/
theorem karger_cost_le_real
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] (g : MultiGraph α) :
    𝔼ℝ_runtime[Karger g | M] ≤
      ((g.verts.card - 2 : ℕ) : ℝ) * (g.edges.length : ℝ) := by
  have := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le (M := M) g)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
  exact this

/-! ## Amplification: repetition finds the minimum cut

A single contraction run succeeds with probability only `Ω(1/n²)`, but
Karger is one-sided — the reported value never undershoots — so keeping
the best cut over independent runs succeeds as soon as any single run
does. The generic `amplify` combinator turns this into a theorem. -/

/-- Amplified cost: `k + 1` runs cost at most `k + 1` times the
single-run bound `(n − 2) m`. -/
theorem karger_amplified_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) (k : ℕ) :
    𝔼_runtime[amplify (argmin Prod.snd) (k + 1) (Karger g) | M] ≤
      (k + 1 : ℝ≥0∞) *
        (((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
  rw [expected_cost_amplify]
  exact mul_le_mul' le_rfl (karger_cost_le g)

end ARA
