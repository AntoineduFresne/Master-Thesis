/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Correctness.Amplify
import Mathlib.Order.Lattice.Nat

/-!
# Karger's randomized minimum-cut algorithm

Karger's algorithm contracts a uniformly random edge until two
supervertices remain; the surviving parallel edges form a cut of the
original graph, and it is a global minimum cut with probability at
least `2 / (n (n - 1))`.

## Graph model

The algorithm operates on an executable multigraph `MultiGraph α`:
a `Finset` of vertices plus a `List` of edges, parallel edges
repeated (one list entry per copy). Sampling an edge uniformly from
the list therefore picks an edge with probability proportional to its
multiplicity, so no weighted-choice primitive is needed.

The cut/contraction theory is ported from Basil Rohner's GraphLib
branch until they are merged to the main branch.

Two deliberate adaptations:

* GraphLib's `contract` deduplicates parallel edges to stay inside
  simple graphs; here parallel edges are kept, since Karger's
  success-probability analysis is valid on multigraphs.
* GraphLib's `Set`-based graphs are noncomputable; `MultiGraph` is
  executable, so the same definition runs under `IO` and is analyzed
  under `PMF`.

## Architecture

As for `Quicksort` and `Quickselect`, a single definition
(`contractAux` / `Karger`) parameterized by `RandMonad` and
`MonadCost ℕ` serves as executable program (`M = IO`), as
specification (`M = PMF`), and as timed algorithm (`M = TimeMT ℕ M'`).

## Main results

* `karger_correct` — over any `LawfulRandMonad`, every value the
  algorithm can output is at least the true minimum-cut value: Karger
  is a one-sided (Monte Carlo) approximation that never undershoots.
* `karger_success_prob` — the output equals the minimum-cut
  value with probability at least `2 / (n (n - 1))`, where
  `n = g.verts.card`. Hence `O(n² log n)` independent repetitions
  find a minimum cut with high probability.
* `karger_cost_le` — with one tick per edge scanned
  during a contraction pass, the expected cost is at most
  `(n - 2) * m` where `m = g.edges.length`.

The success-probability proof follows the classical argument: fix a
minimum cut `S` of value `c`; every vertex has degree at least `c`
(else its singleton would be a smaller cut), so `c * n ≤ 2 * m` by the
handshake identity and a uniformly random edge crosses `S` with
probability at most `2 / n`. Contracting a non-crossing edge preserves
`S` (`isCut_contractEdge_of_notCrossing`) and cannot decrease the
minimum-cut value (`exists_isCut_lift`), so the bound
`∏ᵢ (1 - 2/(n - i)) = 2/(n (n-1))` follows by induction on the number
of contractions.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal

variable {α : Type} [DecidableEq α]

/-! ## The multigraph model -/

/-- A multigraph: a vertex set plus an edge list, with parallel edges
repeated (one entry per copy) and no loops. This is the executable
counterpart of GraphLib's weighted `SimpleGraph`; multiplicities are
realized by repetition instead of weights. -/
structure MultiGraph (α : Type) where
  /-- The (super)vertices currently present. -/
  verts : Finset α
  /-- The edge list; each parallel edge is listed once per copy. -/
  edges : List (α × α)

namespace MultiGraph

/-- Well-formedness: every edge joins two *distinct* vertices of the
graph. All analysis lemmas assume it; `contractEdge` preserves it. -/
structure WF (g : MultiGraph α) : Prop where
  /-- First endpoints are vertices. -/
  mem_fst : ∀ e ∈ g.edges, e.1 ∈ g.verts
  /-- Second endpoints are vertices. -/
  mem_snd : ∀ e ∈ g.edges, e.2 ∈ g.verts
  /-- No loops. -/
  ne_of_mem : ∀ e ∈ g.edges, e.1 ≠ e.2

/-! ### Cuts

Ported from GraphLib's `Cuts/Basic.lean` (`Cut`, `weight`,
`isSTCut`, `stMinCutValue`), specialized to unweighted multigraphs:
the weight of a cut is the number of crossing edges, counted with
multiplicity. -/

/-- Edge `e` crosses the vertex set `S` if exactly one endpoint lies
in `S`. -/
def Crossing (S : Finset α) (e : α × α) : Prop := ¬(e.1 ∈ S ↔ e.2 ∈ S)

instance (S : Finset α) : DecidablePred (Crossing S) := fun e => by
  unfold Crossing; infer_instance

/-- The value of the cut induced by `S`: the number of crossing edges,
counted with multiplicity (GraphLib's `Cut.weight` with unit weights). -/
def cutValue (g : MultiGraph α) (S : Finset α) : ℕ :=
  g.edges.countP fun e => decide (Crossing S e)

/-- `S` induces a (proper, global) cut of `g`: it consists of vertices,
and both sides are nonempty. -/
structure IsCut (g : MultiGraph α) (S : Finset α) : Prop where
  /-- The cut set consists of vertices. -/
  subset : S ⊆ g.verts
  /-- The near side is nonempty. -/
  nonempty : S.Nonempty
  /-- The far side is nonempty. -/
  proper : ∃ v ∈ g.verts, v ∉ S

/-- The global minimum-cut value (GraphLib's `stMinCutValue` pattern:
an `sInf` over achievable cut values, quantified over all cuts instead
of `s`-`t` separators). -/
noncomputable def minCutValue (g : MultiGraph α) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = c}

lemma minCutValue_le {g : MultiGraph α} {S : Finset α} (h : g.IsCut S) :
    g.minCutValue ≤ g.cutValue S :=
  Nat.sInf_le ⟨S, h, rfl⟩

omit [DecidableEq α] in
/-- Any graph with at least two vertices has a cut (a singleton). -/
lemma exists_isCut (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    ∃ S : Finset α, g.IsCut S := by
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
  refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, Finset.singleton_nonempty a, b, hb, ?_⟩
  simp [hab.symm]

/-- The minimum cut value is achieved by some cut. -/
lemma exists_minCut (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = g.minCutValue := by
  obtain ⟨S, hS⟩ := exists_isCut g h2
  have hne : {c : ℕ | ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = c}.Nonempty :=
    ⟨g.cutValue S, S, hS, rfl⟩
  exact Nat.sInf_mem hne

lemma cutValue_le_length (g : MultiGraph α) (S : Finset α) :
    g.cutValue S ≤ g.edges.length :=
  List.countP_le_length

/-- The minimum cut is at most the total edge count. -/
lemma minCutValue_le_length (g : MultiGraph α) (h2 : 2 ≤ g.verts.card) :
    g.minCutValue ≤ g.edges.length := by
  obtain ⟨S, hS⟩ := exists_isCut g h2
  exact le_trans (minCutValue_le hS) (cutValue_le_length g S)

/-! ### Degrees and the handshake bound

The key quantitative fact behind Karger's analysis: every vertex
degree is at least the minimum-cut value (its singleton is a cut), so
`n * minCut ≤ Σ deg = 2 * m`. -/

/-- The degree of `v`: the number of incident edges, with multiplicity. -/
def degree (g : MultiGraph α) (v : α) : ℕ :=
  g.edges.countP fun e => decide (e.1 = v ∨ e.2 = v)

/-- In a loopless graph, the cut of a singleton is the degree. -/
lemma cutValue_singleton (g : MultiGraph α) (hwf : g.WF) (v : α) :
    g.cutValue {v} = g.degree v := by
  unfold cutValue degree
  refine List.countP_congr fun e he => ?_
  have hne := hwf.ne_of_mem e he
  simp only [decide_eq_true_eq, Crossing, Finset.mem_singleton]
  grind

private lemma sum_degree_aux (V : Finset α) (l : List (α × α))
    (hl : ∀ e ∈ l, e.1 ∈ V ∧ e.2 ∈ V ∧ e.1 ≠ e.2) :
    (∑ v ∈ V, l.countP fun e => decide (e.1 = v ∨ e.2 = v)) = 2 * l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e (by simp)
    have hl' : ∀ e' ∈ l, e'.1 ∈ V ∧ e'.2 ∈ V ∧ e'.1 ≠ e'.2 :=
      fun e' he' => hl e' (by simp [he'])
    simp only [List.countP_cons, decide_eq_true_eq]
    rw [Finset.sum_add_distrib, ih hl']
    -- The indicator of incidence sums to `2`: each edge has exactly two
    -- distinct endpoints, both in `V`.
    have hfilter : {v ∈ V | e.1 = v ∨ e.2 = v} = ({e.1, e.2} : Finset α) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h | h⟩
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (rfl | rfl)
        · exact ⟨he.1, Or.inl rfl⟩
        · exact ⟨he.2.1, Or.inr rfl⟩
    have hind : (∑ v ∈ V, if e.1 = v ∨ e.2 = v then 1 else 0) = 2 := by
      simp only [Finset.sum_boole, Nat.cast_id]
      rw [hfilter, Finset.card_insert_of_notMem (by simp [he.2.2]),
        Finset.card_singleton]
    rw [hind, List.length_cons]
    omega

/-- **Handshake identity**: degrees sum to twice the edge count. -/
lemma sum_degree (g : MultiGraph α) (hwf : g.WF) :
    ∑ v ∈ g.verts, g.degree v = 2 * g.edges.length :=
  sum_degree_aux g.verts g.edges fun e he =>
    ⟨hwf.mem_fst e he, hwf.mem_snd e he, hwf.ne_of_mem e he⟩

/-- Every degree bounds the minimum cut from above. -/
lemma minCutValue_le_degree (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) {v : α} (hv : v ∈ g.verts) :
    g.minCutValue ≤ g.degree v := by
  rw [← cutValue_singleton g hwf v]
  refine minCutValue_le ⟨Finset.singleton_subset_iff.mpr hv,
    Finset.singleton_nonempty v, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
  by_cases hav : a = v
  · subst hav
    exact ⟨b, hb, by simp [hab.symm]⟩
  · exact ⟨a, ha, by simp [hav]⟩

/-- The Karger counting bound: `n * minCut ≤ 2 * m`. -/
lemma card_mul_minCutValue_le (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    g.verts.card * g.minCutValue ≤ 2 * g.edges.length := by
  calc g.verts.card * g.minCutValue
      = ∑ _v ∈ g.verts, g.minCutValue := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ g.verts, g.degree v :=
        Finset.sum_le_sum fun v hv => minCutValue_le_degree g hwf h2 hv
    _ = 2 * g.edges.length := sum_degree g hwf

/-! ### Contraction

Ported from GraphLib's `Contractions/Basic.lean`: `redirect` is
`redirectEdge` and `contractEdge` is `contract` (minus the parallel-
edge deduplication, which Karger's multigraph analysis must not do). -/

/-- Redirect a vertex: `v` becomes `u`, everything else is unchanged
(GraphLib's `redirectEdge`, per endpoint). -/
def redirect (u v x : α) : α := if x = v then u else x

lemma redirect_mem_erase {V : Finset α} {u v x : α}
    (hu : u ∈ V) (hne : u ≠ v) (hx : x ∈ V) :
    redirect u v x ∈ V.erase v := by
  unfold redirect
  split_ifs with h
  · exact Finset.mem_erase.mpr ⟨hne, hu⟩
  · exact Finset.mem_erase.mpr ⟨h, hx⟩

/-- **Contract** `v` into `u`: remove `v` from the vertex set, redirect
every edge touching `v` to `u`, and drop the resulting loops (the
parallel copies of `(u, v)` itself). Parallel edges are kept. -/
def contractEdge (g : MultiGraph α) (u v : α) : MultiGraph α where
  verts := g.verts.erase v
  edges := (g.edges.map fun e => (redirect u v e.1, redirect u v e.2)).filter
    fun e => decide (e.1 ≠ e.2)

@[simp] lemma verts_contractEdge (g : MultiGraph α) (u v : α) :
    (g.contractEdge u v).verts = g.verts.erase v := rfl

@[simp] lemma edges_contractEdge (g : MultiGraph α) (u v : α) :
    (g.contractEdge u v).edges =
      (g.edges.map fun e => (redirect u v e.1, redirect u v e.2)).filter
        fun e => decide (e.1 ≠ e.2) := rfl

/-- Contraction preserves well-formedness. -/
theorem WF.contractEdge {g : MultiGraph α} (hwf : g.WF) {u v : α}
    (hu : u ∈ g.verts) (hne : u ≠ v) : (g.contractEdge u v).WF := by
  refine ⟨?_, ?_, ?_⟩ <;> intro e' he' <;>
    · simp only [edges_contractEdge, List.mem_filter, List.mem_map,
        decide_eq_true_eq] at he'
      obtain ⟨⟨e, he, rfl⟩, hne'⟩ := he'
      first
        | exact redirect_mem_erase hu hne (hwf.mem_fst e he)
        | exact redirect_mem_erase hu hne (hwf.mem_snd e he)
        | exact hne'

/-- Contraction removes exactly one vertex. -/
lemma card_verts_contractEdge (g : MultiGraph α) {u v : α} (hv : v ∈ g.verts) :
    (g.contractEdge u v).verts.card + 1 = g.verts.card := by
  rw [verts_contractEdge]
  exact Finset.card_erase_add_one hv

/-- Contraction never increases the edge count. -/
lemma length_edges_contractEdge_le (g : MultiGraph α) (u v : α) :
    (g.contractEdge u v).edges.length ≤ g.edges.length :=
  le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map ..))

/-- Transport of cut values along contraction: if membership in `S'`
after redirection agrees pointwise with membership in `S`, the two cuts
have the same value. Crossing edges are never dropped (a loop cannot
cross), and dropped edges never cross. -/
private lemma cutValue_contractEdge_of_pointwise {g : MultiGraph α}
    (hwf : g.WF) {u v : α} {S' S : Finset α}
    (hpt : ∀ x : α, redirect u v x ∈ S' ↔ x ∈ S) :
    (g.contractEdge u v).cutValue S' = g.cutValue S := by
  unfold cutValue
  rw [edges_contractEdge, List.countP_filter, List.countP_map]
  refine List.countP_congr fun e he => ?_
  have hne := hwf.ne_of_mem e he
  have h1 := hpt e.1
  have h2 := hpt e.2
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, Crossing]
  grind

/-- **Cut lifting** (soundness of contraction): every cut of the
contracted graph comes from a cut of `g` with the *same* value. Hence
contraction can only increase the minimum-cut value. -/
lemma exists_isCut_lift {g : MultiGraph α} (hwf : g.WF) {u v : α}
    (hv : v ∈ g.verts) {S' : Finset α}
    (h : (g.contractEdge u v).IsCut S') :
    ∃ S : Finset α, g.IsCut S ∧ g.cutValue S = (g.contractEdge u v).cutValue S' := by
  have hsub : S' ⊆ g.verts.erase v := h.subset
  have hvS' : v ∉ S' := fun hmem => Finset.notMem_erase v g.verts (hsub hmem)
  obtain ⟨w, hw, hwS'⟩ := h.proper
  rw [verts_contractEdge] at hw
  have hw' := Finset.mem_erase.mp hw
  by_cases hu' : u ∈ S'
  · refine ⟨insert v S', ⟨?_, ⟨v, Finset.mem_insert_self v S'⟩, w, hw'.2, ?_⟩, ?_⟩
    · exact Finset.insert_subset_iff.mpr
        ⟨hv, hsub.trans (Finset.erase_subset ..)⟩
    · simp [Finset.mem_insert, hw'.1, hwS']
    · refine (cutValue_contractEdge_of_pointwise hwf fun x => ?_).symm
      by_cases hxv : x = v <;>
        simp [redirect, hxv, hu', Finset.mem_insert, hvS']
  · refine ⟨S', ⟨hsub.trans (Finset.erase_subset ..), h.nonempty, w, hw'.2, hwS'⟩, ?_⟩
    refine (cutValue_contractEdge_of_pointwise hwf fun x => ?_).symm
    by_cases hxv : x = v <;> simp [redirect, hxv, hu', hvS']

/-- **Cut survival**: contracting an edge that does *not* cross `S`
keeps `S` a cut of the same value (with `v` removed from it). -/
lemma isCut_contractEdge_of_notCrossing {g : MultiGraph α} (hwf : g.WF)
    {u v : α} (hu : u ∈ g.verts) (hne : u ≠ v) {S : Finset α}
    (hS : g.IsCut S) (hnc : ¬Crossing S (u, v)) :
    (g.contractEdge u v).IsCut (S.erase v) ∧
      (g.contractEdge u v).cutValue (S.erase v) = g.cutValue S := by
  have hiff : u ∈ S ↔ v ∈ S := by simpa [Crossing] using hnc
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rw [verts_contractEdge]
      exact Finset.erase_subset_erase v hS.subset
    · by_cases hvS : v ∈ S
      · exact ⟨u, Finset.mem_erase.mpr ⟨hne, hiff.mpr hvS⟩⟩
      · rw [Finset.erase_eq_of_notMem hvS]; exact hS.nonempty
    · obtain ⟨w, hw, hwS⟩ := hS.proper
      rw [verts_contractEdge]
      by_cases hwv : w = v
      · subst hwv
        exact ⟨u, Finset.mem_erase.mpr ⟨hne, hu⟩,
          fun hmem => hwS (hiff.mp (Finset.mem_of_mem_erase hmem))⟩
      · exact ⟨w, Finset.mem_erase.mpr ⟨hwv, hw⟩,
          fun hmem => hwS (Finset.mem_of_mem_erase hmem)⟩
  · refine cutValue_contractEdge_of_pointwise hwf fun x => ?_
    by_cases hxv : x = v <;>
      simp [redirect, hxv, Finset.mem_erase, hne, hiff]

/-- Contraction never decreases the minimum-cut value. -/
lemma minCutValue_le_contractEdge {g : MultiGraph α} (hwf : g.WF) {u v : α}
    (hv : v ∈ g.verts) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contractEdge u v).minCutValue := by
  have h2' : 2 ≤ (g.contractEdge u v).verts.card := by
    have := card_verts_contractEdge (u := u) g hv
    omega
  obtain ⟨S', hS', hval⟩ := exists_minCut _ h2'
  obtain ⟨S, hS, hval2⟩ := exists_isCut_lift hwf hv hS'
  rw [← hval, ← hval2]
  exact minCutValue_le hS

/-- Contracting an edge that avoids a fixed minimum cut preserves the
minimum-cut value exactly. -/
lemma minCutValue_contractEdge_of_notCrossing {g : MultiGraph α} (hwf : g.WF)
    {u v : α} (hu : u ∈ g.verts) (hv : v ∈ g.verts) (hne : u ≠ v)
    (h3 : 3 ≤ g.verts.card) {S : Finset α} (hS : g.IsCut S)
    (hmin : g.cutValue S = g.minCutValue) (hnc : ¬Crossing S (u, v)) :
    (g.contractEdge u v).minCutValue = g.minCutValue := by
  obtain ⟨hcut', hval'⟩ := isCut_contractEdge_of_notCrossing hwf hu hne hS hnc
  refine le_antisymm ?_ (minCutValue_le_contractEdge hwf hv h3)
  calc (g.contractEdge u v).minCutValue
      ≤ (g.contractEdge u v).cutValue (S.erase v) := minCutValue_le hcut'
    _ = g.cutValue S := hval'
    _ = g.minCutValue := hmin

/-! ### Two-vertex graphs

When two supervertices remain, *every* edge crosses *every* cut, so the
edge count is exactly the minimum-cut value. -/

/-- In a well-formed graph on two vertices, every cut consists of all
the edges. -/
lemma cutValue_of_card_two {g : MultiGraph α} (hwf : g.WF)
    (hcard : g.verts.card = 2) {S : Finset α} (hS : g.IsCut S) :
    g.cutValue S = g.edges.length := by
  unfold cutValue
  rw [List.countP_eq_length]
  intro e he
  have h1 := hwf.mem_fst e he
  have h2 := hwf.mem_snd e he
  have h3 := hwf.ne_of_mem e he
  obtain ⟨x, y, hxy, hV⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨s, hsS⟩ := hS.nonempty
  obtain ⟨w, hwV, hwS⟩ := hS.proper
  have hsV := hS.subset hsS
  rw [hV] at h1 h2 hsV hwV
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 hsV hwV
  simp only [decide_eq_true_eq, Crossing]
  grind

/-- On two vertices the edge count *is* the minimum-cut value. -/
lemma length_eq_minCutValue_of_card_two {g : MultiGraph α} (hwf : g.WF)
    (hcard : g.verts.card = 2) :
    g.edges.length = g.minCutValue := by
  obtain ⟨S, hS, hval⟩ := exists_minCut g (le_of_eq hcard.symm)
  rw [← hval, cutValue_of_card_two hwf hcard hS]

/-! ### Contraction of a listed edge -/

/-- Contract the `i`-th edge of the list: merge its second endpoint
into its first. -/
def contract (g : MultiGraph α) (i : Fin g.edges.length) : MultiGraph α :=
  g.contractEdge (g.edges[(i : ℕ)]).1 (g.edges[(i : ℕ)]).2

lemma WF.contract {g : MultiGraph α} (hwf : g.WF) (i : Fin g.edges.length) :
    (g.contract i).WF :=
  hwf.contractEdge (hwf.mem_fst _ (List.getElem_mem _))
    (hwf.ne_of_mem _ (List.getElem_mem _))

lemma card_verts_contract {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) :
    (g.contract i).verts.card + 1 = g.verts.card :=
  card_verts_contractEdge g (hwf.mem_snd _ (List.getElem_mem _))

lemma length_edges_contract_le (g : MultiGraph α) (i : Fin g.edges.length) :
    (g.contract i).edges.length ≤ g.edges.length :=
  length_edges_contractEdge_le g _ _

lemma minCutValue_le_contract {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contract i).minCutValue :=
  minCutValue_le_contractEdge hwf (hwf.mem_snd _ (List.getElem_mem _)) h3

end MultiGraph

/-! ## Algorithm -/

open MultiGraph

/-- Perform `fuel` uniformly-random edge contractions (stopping early
if no edge remains). Each pass ticks once per edge: contracting
relabels and filters the whole edge list. -/
def contractAux {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → MultiGraph α → M (MultiGraph α)
  | 0, g => pure g
  | k + 1, g =>
    if h : 0 < g.edges.length then do
      MonadCost.tick g.edges.length
      let i ← (haveI : NeZero g.edges.length := ⟨h.ne'⟩
        RandMonad.randFin g.edges.length)
      contractAux k (g.contract i)
    else
      pure g

/-- **Karger's algorithm.** Contract uniformly random edges until two
supervertices remain, then report the number of surviving edges — the
value of the cut induced by the two supervertices. -/
def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M ℕ := do
  let g' ← contractAux (g.verts.card - 2) g
  pure g'.edges.length

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed)
def Karger_IO : MultiGraph ℕ → IO ℕ := Karger

/-- Demo graph: two triangles joined by a single bridge — the global
minimum cut is `1` (the bridge). -/
def kargerDemo : MultiGraph ℕ where
  verts := {0, 1, 2, 3, 4, 5}
  edges := [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]

#eval Karger_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF ℕ := Karger

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable)
def Karger_IO_Timed : MultiGraph ℕ → TimeMT ℕ IO ℕ := Karger

#eval (Karger_IO_Timed kargerDemo).run

-- PMF timed version (noncomputable specification)
noncomputable example : MultiGraph ℕ → TimeMT ℕ PMF ℕ := Karger

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

-- `ennreal_div_le_div_nat` (natural-fraction comparison by
-- cross-multiplication) now lives in `ARA.Infrastructure.Tactics`;
-- Schwartz–Zippel is its second client.

/-- The arithmetic core of Karger's induction step: if the current
graph has `m > 0` edges and `k + 3` vertices, and the fixed minimum cut
has `c ≤ m` crossing edges with `c * (k + 3) ≤ 2 * m` (the counting
bound), then picking a non-crossing edge and succeeding afterwards with
probability `2 / ((k+2)(k+1))` beats `2 / ((k+3)(k+2))`. -/
private lemma karger_step_bound {m c k : ℕ} (hm : 0 < m) (hc : c ≤ m)
    (hbound : c * (k + 3) ≤ 2 * m) :
    (2 : ℝ≥0∞) / (((k + 3) * (k + 2) : ℕ) : ℝ≥0∞) ≤
      ((m : ℕ) : ℝ≥0∞)⁻¹ *
        (((m - c : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞))) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + c := ⟨m - c, by omega⟩
  have hdc : d + c - c = d := by omega
  rw [hdc]
  -- `(d + c)(k + 1) ≤ d(k + 3)` from the counting bound.
  have hkey : (d + c) * (k + 1) ≤ d * (k + 3) := by nlinarith
  -- Rewrite the right-hand side as a single natural fraction.
  have hrw : (((d + c : ℕ) : ℝ≥0∞))⁻¹ *
      (((d : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞))) =
      ((d * 2 : ℕ) : ℝ≥0∞) / (((d + c) * ((k + 2) * (k + 1)) : ℕ) : ℝ≥0∞) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul (d + c), Nat.cast_mul d,
      ENNReal.mul_inv (Or.inl (by exact_mod_cast hm.ne'))
        (Or.inl (ENNReal.natCast_ne_top _))]
    push_cast
    ring
  rw [hrw]
  -- Cross-multiply and conclude in `ℕ`.
  refine ennreal_div_le_div_nat (by positivity) (by positivity) ?_
  have h2 := Nat.mul_le_mul_left (2 * (k + 2)) hkey
  calc 2 * ((d + c) * ((k + 2) * (k + 1)))
      = 2 * (k + 2) * ((d + c) * (k + 1)) := by ring
    _ ≤ 2 * (k + 2) * (d * (k + 3)) := h2
    _ = d * 2 * ((k + 3) * (k + 2)) := by ring

/-! ## Correctness: Karger never undershoots

The output of `Karger` is always the value of *some* cut of the input
graph, hence at least the minimum-cut value. Together with the success
probability below, this makes `Karger` a one-sided Monte Carlo
algorithm: taking the minimum over repetitions only improves the
estimate and equals `minCutValue` with high probability. -/

private lemma support_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] :
    ∀ (k : ℕ) (g : MultiGraph α), g.WF → g.verts.card = k + 2 →
      ∀ g' ∈ (inst.toPMF (contractAux k g : M (MultiGraph α))).support,
        g.minCutValue ≤ g'.edges.length := by
  intro k
  induction k with
  | zero =>
    intro g hwf hcard g' hg'
    rw [contractAux.eq_1, inst.toPMF_pure, pmf_pure_eq] at hg'
    rw [show g' = g by simpa [PMF.support_pure] using hg']
    exact minCutValue_le_length g (by omega)
  | succ k ih =>
    intro g hwf hcard g' hg'
    by_cases hm : 0 < g.edges.length
    · rw [contractAux.eq_2, dif_pos hm] at hg'
      simp only [toPMF_simp, inst.toPMF_randFin] at hg'
      obtain ⟨i, -, hi⟩ := (PMF.mem_support_bind_iff _ _ _).mp hg'
      refine le_trans (minCutValue_le_contract hwf i (by omega))
        (ih (g.contract i) (hwf.contract i)
          (by have := card_verts_contract hwf i; omega) g' hi)
    · rw [contractAux.eq_2, dif_neg hm, inst.toPMF_pure, pmf_pure_eq] at hg'
      rw [show g' = g by simpa [PMF.support_pure] using hg']
      exact minCutValue_le_length g (by omega)

/-- **Correctness (one-sided error).** Over any `LawfulRandMonad`,
every value `Karger` can output is at least the true minimum-cut value:
the algorithm never undershoots. -/
theorem karger_correct
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ c ∈ 𝒟[Karger g | M].support,
      g.minCutValue ≤ c := by
  intro c hc
  unfold Karger at hc
  obtain ⟨g', hg', rfl⟩ := mem_support_toPMF_bind_pure.mp hc
  exact support_contractAux (g.verts.card - 2) g hwf (by omega) g' hg'

/-- Correctness at `M = PMF`. -/
theorem karger_correct_pmf (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    ∀ c ∈ (Karger g : PMF ℕ).support, g.minCutValue ≤ c :=
  karger_correct (M := PMF) g hwf h2

/-! ## Success probability -/


/-- Success probability of the contraction loop: on a well-formed graph
with `k + 2` vertices, `k` rounds of uniform random contraction end in
a graph whose edge count equals the *original* minimum-cut value with
probability at least `2 / ((k+2)(k+1))`. Induction on `k`, following
the classical argument. -/
private lemma success_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] :
    ∀ (k : ℕ) (g : MultiGraph α), g.WF → g.verts.card = k + 2 →
      (2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞) ≤
        inst.toPMF
          ((contractAux k g >>= fun g' => pure g'.edges.length : M ℕ))
          g.minCutValue := by
  intro k
  induction k with
  | zero =>
    intro g hwf hcard
    rw [contractAux.eq_1, pure_bind, inst.toPMF_pure, pmf_pure_eq]
    -- The two-vertex graph's edge count is exactly the min-cut value.
    rw [PMF.pure_apply, if_pos (length_eq_minCutValue_of_card_two hwf hcard).symm]
    rw [show ((0 + 2) * (0 + 1) : ℕ) = 2 by norm_num]
    rw [ENNReal.div_le_iff (by simp) (ENNReal.natCast_ne_top 2), one_mul]
    exact_mod_cast Nat.le_refl 2
  | succ k ih =>
    intro g hwf hcard
    by_cases hm : 0 < g.edges.length
    · -- Main case: pick a uniform edge, recurse.
      rw [contractAux.eq_2, dif_pos hm]
      simp only [bind_assoc]
      -- Peel the tick at the PMF level (rw stops at binders, so the
      -- per-edge recursive binds stay intact for `hsum`).
      rw [toPMF_tick_bind]
      rw [inst.toPMF_bind, inst.toPMF_randFin, pmf_bind_eq, PMF.bind_apply]
      have hne : Nonempty (Fin g.edges.length) := ⟨⟨0, hm⟩⟩
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [tsum_fintype, ← Finset.mul_sum]
      -- Fix a minimum cut `S`.
      obtain ⟨S, hS, hSval⟩ := exists_minCut g (by omega)
      -- The branch value as a function of the contracted edge.
      set F : α × α → ℝ≥0∞ := fun e =>
        inst.toPMF
          ((contractAux k (g.contractEdge e.1 e.2) >>=
            fun g' => pure g'.edges.length : M ℕ))
          g.minCutValue with hF
      have hsum : (∑ i : Fin g.edges.length,
          inst.toPMF
            ((contractAux k (g.contract i) >>=
              fun g' => pure g'.edges.length : M ℕ))
            g.minCutValue) = (g.edges.map F).sum := by
        rw [← sum_univ_getElem g.edges F]
        rfl
      rw [hsum]
      -- Every non-crossing edge contributes at least the IH bound.
      have hbranch : ∀ e ∈ g.edges,
          (if Crossing S e then 0 else
            (2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞)) ≤ F e := by
        intro e he
        by_cases hcr : Crossing S e
        · simp [hcr]
        · rw [if_neg hcr, hF]
          have hu := hwf.mem_fst e he
          have hv := hwf.mem_snd e he
          have hene := hwf.ne_of_mem e he
          have hwf' := hwf.contractEdge hu hene
          have hcard' : (g.contractEdge e.1 e.2).verts.card = k + 2 := by
            have := card_verts_contractEdge (u := e.1) g hv
            omega
          have hmc : (g.contractEdge e.1 e.2).minCutValue = g.minCutValue :=
            minCutValue_contractEdge_of_notCrossing hwf hu hv hene (by omega)
              hS hSval (by simpa using hcr)
          have := ih (g.contractEdge e.1 e.2) hwf' hcard'
          rw [hmc] at this
          exact this
      -- Count the non-crossing edges: `m - c` of them.
      have hcount : (g.edges.map fun e =>
          (if Crossing S e then 0 else
            (2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞))).sum =
          ((g.edges.length - g.cutValue S : ℕ) : ℝ≥0∞) *
            ((2 : ℝ≥0∞) / (((k + 2) * (k + 1) : ℕ) : ℝ≥0∞)) :=
        sum_map_ite_zero (Crossing S) _ g.edges
      -- Chain the bounds.
      refine le_trans ?_ (mul_le_mul' le_rfl
        (le_trans (le_of_eq hcount.symm) (List.sum_le_sum hbranch)))
      rw [hSval]
      -- Arithmetic: `2/((k+3)(k+2)) ≤ m⁻¹ (m - c) 2/((k+2)(k+1))`.
      have hc_le : g.minCutValue ≤ g.edges.length :=
        minCutValue_le_length g (by omega)
      have hbound : g.minCutValue * (k + 3) ≤ 2 * g.edges.length := by
        have := card_mul_minCutValue_le g hwf (by omega)
        rw [hcard] at this
        calc g.minCutValue * (k + 3) = (k + 1 + 2) * g.minCutValue := by ring
          _ ≤ 2 * g.edges.length := this
      have := karger_step_bound hm hc_le hbound
      rw [show ((k + 1 + 2) * (k + 1 + 1) : ℕ) = ((k + 3) * (k + 2) : ℕ) by ring]
      exact this
    · -- No edges left: the graph is edgeless, so its min cut is `0` and
      -- the reported value `0` is exact — success with probability `1`.
      rw [contractAux.eq_2, dif_neg hm, pure_bind, inst.toPMF_pure, pmf_pure_eq]

      have hzero : g.minCutValue = 0 :=
        Nat.le_zero.mp (le_trans (minCutValue_le_length g (by omega)) (by omega))
      rw [PMF.pure_apply, if_pos (by omega : g.minCutValue = g.edges.length)]
      rw [ENNReal.div_le_iff
        (by exact_mod_cast (by positivity : ((k + 1 + 2) * (k + 1 + 1) : ℕ) ≠ 0))
        (ENNReal.natCast_ne_top _), one_mul]
      exact_mod_cast (by nlinarith : 2 ≤ (k + 1 + 2) * (k + 1 + 1))

/-- **Success probability of Karger's algorithm.** Over any
`LawfulRandMonad`, a single run outputs the exact minimum-cut value
with probability at least `2 / (n (n - 1))`, where `n = g.verts.card`.
Consequently `O(n² log n)` independent repetitions find a minimum cut
with high probability. -/
theorem karger_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[Karger g = g.minCutValue | M] := by
  have hmain := success_contractAux (M := M) (g.verts.card - 2) g hwf (by omega)
  have harith : (g.verts.card - 2 + 2) * (g.verts.card - 2 + 1) =
      g.verts.card * (g.verts.card - 1) := by
    rw [show g.verts.card - 2 + 2 = g.verts.card by omega,
      show g.verts.card - 2 + 1 = g.verts.card - 1 by omega]
  rw [harith] at hmain
  exact hmain

/-- Success probability at `M = PMF`. -/
theorem karger_success_prob_pmf (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      (Karger g : PMF ℕ) g.minCutValue :=
  karger_success_prob (M := PMF) g hwf h2

/-! ## Complexity

Each contraction round ticks `m' = ` (current number of edges): the
contraction pass relabels and filters the whole edge list. Since
contraction never adds edges, every round costs at most `m` and there
are at most `n - 2` rounds, giving expected cost at most `(n - 2) m`.
The bound holds for **arbitrary** graphs — no well-formedness needed. -/

/-- Expected cost of the contraction loop: at most `fuel * m`. -/
private lemma expected_cost_contractAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] :
    ∀ (k : ℕ) (g : MultiGraph α),
      𝔼_runtime[(contractAux k g : TimeMT ℕ M (MultiGraph α))] ≤
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
    · rw [contractAux.eq_2, dif_pos hm]
      haveI : NeZero g.edges.length := ⟨hm.ne'⟩
      cost_step
      rw [inst.toPMF_randFin, tsum_fintype]
      have hne : Nonempty (Fin g.edges.length) := ⟨⟨0, hm⟩⟩
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [← Finset.mul_sum]
      -- Average of the branch costs: each branch recurses on at most
      -- `m` edges, so the average is at most `k * m`.
      have hsum : (∑ i : Fin g.edges.length,
          𝔼_runtime[(contractAux k (g.contract i) : TimeMT ℕ M (MultiGraph α))]) ≤
          (g.edges.length : ℝ≥0∞) * ((k : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
        refine le_trans (Finset.sum_le_sum fun i _ => le_trans (ih (g.contract i))
          (mul_le_mul' le_rfl
            (Nat.cast_le.mpr (length_edges_contract_le g i)))) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      refine le_trans (add_le_add le_rfl (uniform_avg_le hsum hm.ne')) ?_
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
  rw [expected_cost_toPMF_bind]
  simp only [expected_cost_toPMF_pure, mul_zero, tsum_zero, add_zero]
  exact expected_cost_contractAux _ g

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
Karger is one-sided — outputs never undershoot — so the *minimum* over
independent runs succeeds as soon as any single run does. The generic
`amplify` combinator turns this into a theorem. -/

/-- **Amplified Karger.** Run the contraction algorithm `k` times and
keep the smallest cut value found: the result is the exact minimum-cut
value with probability at least `1 − (1 − 2/(n(n−1)))^k`, so the
failure probability decays geometrically and `O(n² log n)` repetitions
find a minimum cut with high probability. -/
theorem karger_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ[amplify min k (Karger g) = g.minCutValue | M] :=
  amplify_min_success (fun c hc => karger_correct g hwf h2 c hc)
    (karger_success_prob g hwf h2) k

/-- Amplified cost: `k + 1` runs cost at most `k + 1` times the
single-run bound `(n − 2) m`. -/
theorem karger_amplified_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) (k : ℕ) :
    𝔼_runtime[amplify min (k + 1) (Karger g) | M] ≤
      (k + 1 : ℝ≥0∞) * (((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
  rw [expected_cost_amplify]
  exact mul_le_mul' le_rfl (karger_cost_le g)

end ARA
