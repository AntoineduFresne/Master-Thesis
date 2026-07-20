/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Mathlib.Tactic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Sym.Sym2.Order

/-!
# Executable undirected multigraphs: cuts and contraction

Pure graph theory, shared by the contraction algorithms (`Karger`, and
`Karger–Stein` / Benczúr–Karger sparsification to come). Nothing here
mentions randomness, cost, or `PMF`: it is Mathlib-only mathematics,
and it is the part of the Karger development that ARA does **not**
claim as its own contribution.

## Standing in for GraphLib

This file is a deliberate stand-in for `sorrachai/GraphLib`, which is
not yet importable (its branches are on `v4.30.0-rc2`, ours is
`v4.31.0`, and `main` has no cut theory yet). The definitions are
aligned with it so the eventual swap is mechanical:

* endpoints are `Sym2 α`, matching GraphLib's `Edge.endpoints`
  (`GraphLib/Graph/Basic.lean`) and Weixuan Yuan's `abbrev Edge := Sym2`;
* `WF` is their `incidence` / `loopless` pair;
* `redirect`/`contractEdge` follow their `redirectEdge`/`contract`, and
  redirection acts through `Sym2.map` as in their `mapEdge`.

Two divergences, both forced by executability and documented at their
definitions: multiplicity is carried by repetition in a `List` rather
than by an `Edge.edgeLabel` over a noncomputable `Set` (our
`List (Sym2 α)` is their `Set (Edge α (Fin m))` with the list position
as the label), and contraction merges one endpoint into the other
rather than quotienting the vertex type by a `Setoid`, so the vertex
type survives the contraction loop.

When GraphLib publishes on a matching toolchain, this file should
shrink to an adapter.
-/

namespace ARA

variable {α : Type} [DecidableEq α]

/-! ## The multigraph model -/

/-- An **undirected** multigraph: a vertex set plus an edge list, with
parallel edges repeated (one entry per copy) and no loops.

Endpoints are a `Sym2 α`, Mathlib's unordered pair, matching GraphLib's
`Edge.endpoints` (`GraphLib/Graph/Basic.lean`) and Weixuan's
`abbrev Edge := Sym2`. Orientation is therefore not merely irrelevant,
it is *inexpressible*: `s(u, v)` and `s(v, u)` are the same term.

We diverge from GraphLib on multiplicity only. GraphLib distinguishes
parallel edges by an `edgeLabel` and stores edges in a `Set`, which is
noncomputable; here an edge is repeated once per copy in a `List`, so
that drawing an edge uniformly *with multiplicity* is just
`randFin edges.length` and the development stays executable. Our
`List (Sym2 α)` is exactly GraphLib's `Set (Edge α (Fin m))` with the
list position playing the role of the label. -/
structure MultiGraph (α : Type) where
  /-- The (super)vertices currently present. -/
  verts : Finset α
  /-- The edge list; each parallel edge is listed once per copy. -/
  edges : List (Sym2 α)

namespace MultiGraph

/-- Well-formedness: every edge joins two *distinct* vertices of the
graph. Field names follow GraphLib's `incidence` / `loopless`. -/
structure WF (g : MultiGraph α) : Prop where
  /-- Every endpoint of an edge is a vertex. -/
  incidence : ∀ e ∈ g.edges, ∀ v ∈ e, v ∈ g.verts
  /-- No edge is a loop. -/
  loopless : ∀ e ∈ g.edges, ¬ e.IsDiag

/-! ### Cuts

Ported from GraphLib's `Cuts/Basic.lean` (`Cut`, `weight`,
`isSTCut`, `stMinCutValue`), specialized to unweighted multigraphs:
the weight of a cut is the number of crossing edges, counted with
multiplicity. -/

/-- The crossing test, as a `Bool`, built with `Sym2.lift`. The
symmetry argument is the *well-definedness obligation* of the lift, so
a direction-sensitive crossing predicate cannot even be written down —
this is what makes the model undirected by construction rather than by
after-the-fact proof. -/
def crossingB (S : Finset α) : Sym2 α → Bool :=
  Sym2.lift ⟨fun a b => decide (a ∈ S) != decide (b ∈ S), fun _ _ => bne_comm ..⟩

/-- Edge `e` crosses the vertex set `S` if exactly one endpoint lies
in `S`. -/
def Crossing (S : Finset α) (e : Sym2 α) : Prop := crossingB S e = true

instance (S : Finset α) : DecidablePred (Crossing S) :=
  fun e => inferInstanceAs (Decidable (crossingB S e = true))

@[simp] lemma crossing_mk (S : Finset α) (a b : α) :
    Crossing S s(a, b) ↔ ¬(a ∈ S ↔ b ∈ S) := by
  show (decide (a ∈ S) != decide (b ∈ S)) = true ↔ _
  simp only [bne_iff_ne, ne_eq, decide_eq_decide]

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
`n * minCut ≤ Σ deg = 2 * m`. Note `degree` is the *incidence* degree
— `v ∈ e` for the unordered edge `e` — which is why the handshake
identity below reads `2 * m` and not `m`. -/

/-- The degree of `v`: the number of incident edges, with multiplicity. -/
def degree (g : MultiGraph α) (v : α) : ℕ :=
  g.edges.countP fun e => decide (v ∈ e)

/-- In a loopless graph, the cut of a singleton is the degree. -/
lemma cutValue_singleton (g : MultiGraph α) (hwf : g.WF) (v : α) :
    g.cutValue {v} = g.degree v := by
  unfold cutValue degree
  refine List.countP_congr fun e he => ?_
  have hnd := hwf.loopless e he
  clear he
  revert hnd
  induction e with
  | _ a b =>
    intro hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    simp only [crossing_mk, Finset.mem_singleton, Sym2.mem_iff]
    grind

/-- Each edge contributes exactly `2` to the sum of degrees: it has two
distinct endpoints, both vertices. -/
private lemma sum_incident_eq_two {V : Finset α} {e : Sym2 α}
    (hmem : ∀ v ∈ e, v ∈ V) (hnd : ¬ e.IsDiag) :
    (∑ v ∈ V, if v ∈ e then 1 else 0) = 2 := by
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha : a ∈ V := hmem a (Sym2.mem_mk_left a b)
    have hb : b ∈ V := hmem b (Sym2.mem_mk_right a b)
    have hfilter : {v ∈ V | v ∈ s(a, b)} = ({a, b} : Finset α) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Sym2.mem_iff]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (rfl | rfl) <;> simp [ha, hb]
    simp only [Finset.sum_boole, Nat.cast_id]
    rw [hfilter, Finset.card_insert_of_notMem (by simp [hnd]),
      Finset.card_singleton]

private lemma sum_degree_aux (V : Finset α) (l : List (Sym2 α))
    (hl : ∀ e ∈ l, (∀ v ∈ e, v ∈ V) ∧ ¬ e.IsDiag) :
    (∑ v ∈ V, l.countP fun e => decide (v ∈ e)) = 2 * l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    have he := hl e (by simp)
    have hl' : ∀ e' ∈ l, (∀ v ∈ e', v ∈ V) ∧ ¬ e'.IsDiag :=
      fun e' he' => hl e' (by simp [he'])
    simp only [List.countP_cons, decide_eq_true_eq]
    rw [Finset.sum_add_distrib, ih hl', sum_incident_eq_two he.1 he.2,
      List.length_cons]
    omega

/-- **Handshake identity**: degrees sum to twice the edge count. -/
lemma sum_degree (g : MultiGraph α) (hwf : g.WF) :
    ∑ v ∈ g.verts, g.degree v = 2 * g.edges.length :=
  sum_degree_aux g.verts g.edges fun e he =>
    ⟨hwf.incidence e he, hwf.loopless e he⟩

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
edge deduplication, which Karger's multigraph analysis must not do).
Redirection acts on endpoints through `Sym2.map`, exactly as in
Weixuan's `Contractions.lean` (`def mapEdge : Edge α → Edge β :=
Sym2.map π`); we merge one vertex into another instead of quotienting
by a `Setoid`, so that the vertex *type* does not change and the
contraction loop stays a plain recursion. -/

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
parallel copies of `s(u, v)` itself). Parallel edges are kept. -/
def contractEdge (g : MultiGraph α) (u v : α) : MultiGraph α where
  verts := g.verts.erase v
  edges := (g.edges.map (Sym2.map (redirect u v))).filter fun e => !e.IsDiag

@[simp] lemma verts_contractEdge (g : MultiGraph α) (u v : α) :
    (g.contractEdge u v).verts = g.verts.erase v := rfl

@[simp] lemma edges_contractEdge (g : MultiGraph α) (u v : α) :
    (g.contractEdge u v).edges =
      (g.edges.map (Sym2.map (redirect u v))).filter fun e => !e.IsDiag := rfl

/-- Contraction preserves well-formedness. -/
theorem WF.contractEdge {g : MultiGraph α} (hwf : g.WF) {u v : α}
    (hu : u ∈ g.verts) (hne : u ≠ v) : (g.contractEdge u v).WF := by
  constructor
  · intro e' he' w hw
    simp only [edges_contractEdge, List.mem_filter, List.mem_map] at he'
    obtain ⟨⟨e, he, rfl⟩, -⟩ := he'
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hw
    exact redirect_mem_erase hu hne (hwf.incidence e he x hx)
  · intro e' he'
    simp only [edges_contractEdge, List.mem_filter] at he'
    simpa using he'.2

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
    (hpt : ∀ x ∈ g.verts, (redirect u v x ∈ S' ↔ x ∈ S)) :
    (g.contractEdge u v).cutValue S' = g.cutValue S := by
  unfold cutValue
  rw [edges_contractEdge, List.countP_filter, List.countP_map]
  refine List.countP_congr fun e he => ?_
  have hnd := hwf.loopless e he
  have hmem := hwf.incidence e he
  clear he
  revert hnd hmem
  induction e with
  | _ a b =>
    intro hnd hmem
    rw [Sym2.mk_isDiag_iff] at hnd
    have h1 := hpt a (hmem a (Sym2.mem_mk_left a b))
    have h2 := hpt b (hmem b (Sym2.mem_mk_right a b))
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq,
      Sym2.map_mk, crossing_mk, Bool.not_eq_true', decide_eq_false_iff_not,
      Sym2.mk_isDiag_iff]
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
    refine (cutValue_contractEdge_of_pointwise hwf fun x _ => ?_).symm
    by_cases hxv : x = v <;> simp [redirect, hxv, hu', hvS']

/-- **Cut survival**: contracting an edge that does *not* cross `S`
keeps `S` a cut of the same value (with `v` removed from it). -/
lemma isCut_contractEdge_of_notCrossing {g : MultiGraph α} (hwf : g.WF)
    {u v : α} (hu : u ∈ g.verts) (hne : u ≠ v) {S : Finset α}
    (hS : g.IsCut S) (hnc : ¬Crossing S s(u, v)) :
    (g.contractEdge u v).IsCut (S.erase v) ∧
      (g.contractEdge u v).cutValue (S.erase v) = g.cutValue S := by
  have hiff : u ∈ S ↔ v ∈ S := by simpa using hnc
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
  · refine cutValue_contractEdge_of_pointwise hwf fun x _ => ?_
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
    (hmin : g.cutValue S = g.minCutValue) (hnc : ¬Crossing S s(u, v)) :
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
  have hmem := hwf.incidence e he
  have hnd := hwf.loopless e he
  clear he
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have h1 : a ∈ g.verts := hmem a (Sym2.mem_mk_left a b)
    have h2 : b ∈ g.verts := hmem b (Sym2.mem_mk_right a b)
    obtain ⟨x, y, hxy, hV⟩ := Finset.card_eq_two.mp hcard
    obtain ⟨s, hsS⟩ := hS.nonempty
    obtain ⟨w, hwV, hwS⟩ := hS.proper
    have hsV := hS.subset hsS
    rw [hV] at h1 h2 hsV hwV
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 hsV hwV
    simp only [decide_eq_true_eq, crossing_mk]
    grind

/-- On two vertices the edge count *is* the minimum-cut value. -/
lemma length_eq_minCutValue_of_card_two {g : MultiGraph α} (hwf : g.WF)
    (hcard : g.verts.card = 2) :
    g.edges.length = g.minCutValue := by
  obtain ⟨S, hS, hval⟩ := exists_minCut g (le_of_eq hcard.symm)
  rw [← hval, cutValue_of_card_two hwf hcard hS]

/-! ### Tracking the supervertices

Karger's algorithm returns a **cut**, not just its value, so a run has
to remember which original vertices were merged together. `Tracks g₀ g r`
is that bookkeeping invariant: `r` sends each original vertex to the
supervertex it currently sits in, and — the load-bearing clause —
every cut of the contracted graph pulls back along `r` to a cut of
`g₀` of the *same value*. The inductive step is
`cutValue_contractEdge_of_pointwise`, one contraction at a time. -/

/-- A cut value only depends on which *vertices* lie in the cut set. -/
lemma cutValue_congr_of_verts {g : MultiGraph α} (hwf : g.WF) {S T : Finset α}
    (h : ∀ x ∈ g.verts, (x ∈ S ↔ x ∈ T)) : g.cutValue S = g.cutValue T := by
  unfold cutValue
  refine List.countP_congr fun e he => ?_
  have hmem := hwf.incidence e he
  clear he
  revert hmem
  induction e with
  | _ a b =>
    intro hmem
    have h1 := h a (hmem a (Sym2.mem_mk_left a b))
    have h2 := h b (hmem b (Sym2.mem_mk_right a b))
    simp only [crossing_mk]
    grind

/-- The pullback of `S'` along `r`, as a subset of `g₀`'s vertices. -/
def pullback (g₀ : MultiGraph α) (r : α → α) (S' : Finset α) : Finset α :=
  g₀.verts.filter fun x => r x ∈ S'

/-- `r` tracks the contraction of `g₀` down to `g`. -/
structure Tracks (g₀ g : MultiGraph α) (r : α → α) : Prop where
  /-- Every original vertex sits in some current supervertex. -/
  maps : ∀ x ∈ g₀.verts, r x ∈ g.verts
  /-- Every current supervertex contains an original vertex. -/
  onto : ∀ y ∈ g.verts, ∃ x ∈ g₀.verts, r x = y
  /-- Cuts pull back along `r` with the same value. -/
  cut : ∀ S' : Finset α, g.cutValue S' = g₀.cutValue (g₀.pullback r S')

/-- The identity tracks a graph against itself. -/
lemma Tracks.refl (g₀ : MultiGraph α) (hwf : g₀.WF) : Tracks g₀ g₀ id := by
  refine ⟨fun x hx => hx, fun y hy => ⟨y, hy, rfl⟩, fun S' => ?_⟩
  refine cutValue_congr_of_verts hwf fun x hx => ?_
  simp [pullback, hx]

/-- Tracking survives one contraction. -/
lemma Tracks.contractEdge {g₀ g : MultiGraph α} {r : α → α}
    (hwf₀ : g₀.WF) (hwf : g.WF) (ht : Tracks g₀ g r) {u v : α}
    (hu : u ∈ g.verts) (hne : u ≠ v) :
    Tracks g₀ (g.contractEdge u v) (redirect u v ∘ r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact redirect_mem_erase hu hne (ht.maps x hx)
  · intro y hy
    rw [verts_contractEdge] at hy
    obtain ⟨hyv, hyg⟩ := Finset.mem_erase.mp hy
    obtain ⟨x, hx, rfl⟩ := ht.onto y hyg
    exact ⟨x, hx, by simp [Function.comp_apply, redirect, hyv]⟩
  · intro S''
    rw [cutValue_contractEdge_of_pointwise (S := g.pullback (redirect u v) S'')
        hwf (fun x hx => by simp [pullback, hx]), ht.cut]
    refine cutValue_congr_of_verts hwf₀ fun x hx => ?_
    simp only [pullback, Finset.mem_filter, Function.comp_apply, hx, true_and,
      ht.maps x hx]

/-! ### Contraction of a listed edge

Contracting `s(u, v)` has to keep one of the two endpoints, and the two
choices give *isomorphic but not equal* graphs — so contraction is not
a function of the unordered edge alone. GraphLib resolves this by
quotienting the vertex type by a `Setoid`, which changes the vertex
type at every round and would stop the contraction loop from being a
plain recursion. We instead fix the survivor with the linear order on
`α` (keep `inf`, merge away `sup`). Only this executable layer needs
`[LinearOrder α]`; the cut theory above needs just `[DecidableEq α]`. -/

section Indexed
variable [LinearOrder α]

omit [DecidableEq α] in
/-- An edge is recovered from its endpoints in order. -/
theorem sym2_mk_inf_sup (e : Sym2 α) : s(e.inf, e.sup) = e := by
  induction e with
  | _ a b =>
    rcases le_total a b with h | h <;>
      simp [Sym2.inf_mk, Sym2.sup_mk, h, Sym2.eq_swap]

omit [DecidableEq α] in
theorem sym2_inf_mem (e : Sym2 α) : e.inf ∈ e := by
  induction e with
  | _ a b => rcases le_total a b with h | h <;> simp [Sym2.inf_mk, h]

omit [DecidableEq α] in
theorem sym2_sup_mem (e : Sym2 α) : e.sup ∈ e := by
  induction e with
  | _ a b => rcases le_total a b with h | h <;> simp [Sym2.sup_mk, h]

omit [DecidableEq α] in
theorem sym2_inf_ne_sup {e : Sym2 α} (h : ¬ e.IsDiag) : e.inf ≠ e.sup := by
  induction e with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at h
    rcases lt_or_gt_of_ne h with hlt | hlt <;>
      simp [Sym2.inf_mk, Sym2.sup_mk] <;> exact h

/-- Contract the undirected edge `e`, merging its larger endpoint into
its smaller one. -/
def contract' (g : MultiGraph α) (e : Sym2 α) : MultiGraph α :=
  g.contractEdge e.inf e.sup

/-- Contract the `i`-th edge of the list. -/
def contract (g : MultiGraph α) (i : Fin g.edges.length) : MultiGraph α :=
  g.contract' g.edges[(i : ℕ)]

lemma WF.contract {g : MultiGraph α} (hwf : g.WF) (i : Fin g.edges.length) :
    (g.contract i).WF :=
  hwf.contractEdge
    (hwf.incidence _ (List.getElem_mem _) _ (sym2_inf_mem _))
    (sym2_inf_ne_sup (hwf.loopless _ (List.getElem_mem _)))

lemma card_verts_contract {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) :
    (g.contract i).verts.card + 1 = g.verts.card :=
  card_verts_contractEdge g
    (hwf.incidence _ (List.getElem_mem _) _ (sym2_sup_mem _))

lemma length_edges_contract_le (g : MultiGraph α) (i : Fin g.edges.length) :
    (g.contract i).edges.length ≤ g.edges.length :=
  length_edges_contractEdge_le g _ _

lemma minCutValue_le_contract {g : MultiGraph α} (hwf : g.WF)
    (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contract i).minCutValue :=
  minCutValue_le_contractEdge hwf
    (hwf.incidence _ (List.getElem_mem _) _ (sym2_sup_mem _)) h3

end Indexed

end MultiGraph

open MultiGraph

variable [LinearOrder α]

/-! ## Reading the cut off a tracked contraction -/

/-- The cut reported by a finished run: the set of original vertices
that were merged into the same supervertex as the smallest vertex.
(The complementary fibre induces the same cut.) -/
def cutOf (g : MultiGraph α) (r : α → α) : Finset α :=
  if h : g.verts.Nonempty then
    g.verts.filter fun x => r x = r (g.verts.min' h)
  else ∅

lemma cutOf_eq_pullback (g₀ : MultiGraph α) (r : α → α)
    (h : g₀.verts.Nonempty) :
    cutOf g₀ r = g₀.pullback r {r (g₀.verts.min' h)} := by
  simp [cutOf, MultiGraph.pullback, h]

/-- The returned set really is a cut of the original graph. -/
lemma isCut_cutOf {g₀ g : MultiGraph α} {r : α → α} (ht : Tracks g₀ g r)
    (h2 : 2 ≤ g.verts.card) (h : g₀.verts.Nonempty) :
    g₀.IsCut (cutOf g₀ r) := by
  rw [cutOf_eq_pullback g₀ r h]
  set m := g₀.verts.min' h with hm
  have hmv : m ∈ g₀.verts := g₀.verts.min'_mem h
  refine ⟨Finset.filter_subset _ _, ⟨m, ?_⟩, ?_⟩
  · simp [MultiGraph.pullback, hmv]
  · -- some other supervertex exists, and it has an original vertex in it
    obtain ⟨y, hy, hyne⟩ : ∃ y ∈ g.verts, y ≠ r m := by
      obtain ⟨a, b, ha, hb, hab⟩ :=
        Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
      by_cases hav : a = r m
      · exact ⟨b, hb, by rw [← hav]; exact fun hc => hab hc.symm⟩
      · exact ⟨a, ha, hav⟩
    obtain ⟨x, hx, rfl⟩ := ht.onto y hy
    exact ⟨x, hx, by simp [MultiGraph.pullback, hx, hyne]⟩

/-- **The bridge.** The cut a run returns has exactly the value that
run reports: `cutValue` of the output equals the surviving edge count,
which is what `kargerValue` is analysed as. -/
lemma cutValue_cutOf {g₀ g : MultiGraph α} (hwf : g.WF)
    {r : α → α} (ht : Tracks g₀ g r)
    (hend : g.verts.card = 2 ∨ g.edges = []) (h : g₀.verts.Nonempty) :
    g₀.cutValue (cutOf g₀ r) = g.edges.length := by
  rw [cutOf_eq_pullback g₀ r h, ← ht.cut]
  set m := g₀.verts.min' h with hm
  have hmv : m ∈ g₀.verts := g₀.verts.min'_mem h
  rcases hend with hcard | hnil
  · refine cutValue_of_card_two hwf hcard ?_
    refine ⟨Finset.singleton_subset_iff.mpr (ht.maps m hmv),
      Finset.singleton_nonempty _, ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ :=
      Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
    by_cases hav : a = r m
    · exact ⟨b, hb, by simp [← hav, Ne.symm hab]⟩
    · exact ⟨a, ha, by simp [hav]⟩
  · simp [MultiGraph.cutValue, hnil]

end ARA
