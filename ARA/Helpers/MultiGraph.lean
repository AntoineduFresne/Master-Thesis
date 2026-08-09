/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Tactic
import Mathlib.Order.Lattice.Nat

/-!
# Executable undirected multigraphs: cuts and contraction

Pure graph theory, shared by the contraction algorithms (`Karger`, and
`Karger–Stein` / Benczúr–Karger sparsification to come). Nothing here
mentions randomness, cost, or `PMF`: it is Mathlib-only mathematics,
and it is the part of the Karger development that ARA does not
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
as the label), and contraction is the supervertex `∪`-merge on
`MultiGraph (Finset β)` rather than a quotient of the vertex type by a
`Setoid`: merging is symmetric, so contraction is a genuine function
of the unordered edge (no order, no choice, no tie-break), and the
vertex type survives the contraction loop.

When GraphLib publishes on a matching toolchain, this file should
shrink to an adapter.
-/

namespace ARA

variable {α : Type} [DecidableEq α]

/-! ## The multigraph model -/

/-- An undirected multigraph: a vertex set plus an edge list, with
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
a direction-sensitive crossing predicate cannot even be written down,
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
(`v ∈ e` for the unordered edge `e`), which is why the handshake
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

/-- Handshake identity: degrees sum to twice the edge count. -/
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

/-! ### Transport of cut values along an endpoint relabelling -/

/-- If membership after relabelling agrees pointwise with membership
before, relabelling every edge and dropping the resulting loops
preserves the crossing count: crossing edges are never dropped (a loop
cannot cross), and dropped edges never cross. The engine behind every
contraction lemma below. -/
private lemma countP_crossing_map_filter {g : MultiGraph α} (hwf : g.WF)
    (f : α → α) {S' S : Finset α}
    (hpt : ∀ x ∈ g.verts, (f x ∈ S' ↔ x ∈ S)) :
    ((g.edges.map (Sym2.map f)).filter fun e => !e.IsDiag).countP
      (fun e => decide (Crossing S' e)) = g.cutValue S := by
  unfold cutValue
  rw [List.countP_filter, List.countP_map]
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

/-- A cut value only depends on which *vertices* lie in the cut set.
(Kept as the general weight-invariance principle of the cut tier;
Benczúr–Karger sparsification is the intended next client.) -/
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

/-! ### Generic endpoint-merge (rename) contraction

Every representative-style contraction has the same shape: the two
endpoints of the contracted edge leave the vertex set, a single merged
vertex `w` enters, every edge is redirected through the merge, and the
loops this creates (the parallel copies of the contracted edge) are
dropped. The models differ only in how `w` is chosen: the smaller
endpoint under a linear order, the endpoint of smaller label under an
upfront enumeration, a brand-new vertex, or the union of the endpoint
supervertices (the supervertex model below).

The entire cut theory needs exactly one hypothesis about that
choice: `w` collides with no *untouched* vertex,
`w ∉ g.verts.filter (· ∉ e)`, since `w` may well be one of the endpoints.
Everything else (cut lifting, cut survival, preservation of the
minimum-cut value along a non-crossing contraction) is proved here
once, and each model instantiates it by discharging the freshness
obligation, which is precisely where each model pays its price. -/

section Rename

variable {β : Type} [DecidableEq β]

/-- Redirect under the merge of the endpoints of `e` into `w`: both
endpoints become `w`, everything else is unchanged. -/
def redirectTo (e : Sym2 β) (w : β) (x : β) : β :=
  if x ∈ e then w else x

/-- Contract the edge `e` into the vertex `w`: the endpoints leave,
`w` enters, every edge is redirected through `redirectTo e w` and the
resulting loops are dropped; parallel edges are kept. -/
def contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) : MultiGraph β where
  verts := insert w (g.verts.filter (· ∉ e))
  edges := (g.edges.map (Sym2.map (redirectTo e w))).filter fun e' => !e'.IsDiag

@[simp] lemma verts_contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).verts = insert w (g.verts.filter (· ∉ e)) := rfl

@[simp] lemma edges_contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).edges =
      (g.edges.map (Sym2.map (redirectTo e w))).filter fun e' => !e'.IsDiag := rfl

/-- Merging removes exactly one vertex: two leave, `w` enters fresh. -/
lemma card_verts_contractEdgeTo {g : MultiGraph β} {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) :
    (g.contractEdgeTo e w).verts.card + 1 = g.verts.card := by
  rw [verts_contractEdgeTo, Finset.card_insert_of_notMem hfresh]
  clear hfresh
  revert hmem hnd
  induction e with
  | _ a b =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha := hmem a (Sym2.mem_mk_left a b)
    have hb := hmem b (Sym2.mem_mk_right a b)
    have hfil : g.verts.filter (· ∉ s(a, b)) = g.verts \ {a, b} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton, Sym2.mem_iff]
    have hsub : ({a, b} : Finset β) ⊆ g.verts :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    have h2le : 2 ≤ g.verts.card := by
      calc 2 = ({a, b} : Finset β).card := (Finset.card_pair hnd).symm
        _ ≤ g.verts.card := Finset.card_le_card hsub
    rw [hfil, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Finset.card_pair hnd]
    omega

/-- Rename contraction preserves well-formedness, with no hypothesis on
`w` needed. -/
theorem WF.contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} : (g.contractEdgeTo e w).WF := by
  constructor
  · intro e' he' x hx
    simp only [edges_contractEdgeTo, List.mem_filter, List.mem_map] at he'
    obtain ⟨⟨e₀, he₀, rfl⟩, -⟩ := he'
    obtain ⟨x₀, hx₀, rfl⟩ := Sym2.mem_map.mp hx
    have hxv := hwf.incidence e₀ he₀ x₀ hx₀
    rw [verts_contractEdgeTo]
    unfold redirectTo
    split_ifs with hxe
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxv, hxe⟩)
  · intro e' he'
    simp only [edges_contractEdgeTo, List.mem_filter] at he'
    simpa using he'.2

/-- Rename contraction never increases the edge count. -/
lemma length_edges_contractEdgeTo_le (g : MultiGraph β) (e : Sym2 β) (w : β) :
    (g.contractEdgeTo e w).edges.length ≤ g.edges.length :=
  le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map ..))

/-- Cut-value transport along one rename contraction: if membership in
`S'` after redirection agrees pointwise with membership in `S`, the
two cuts have the same value. -/
lemma cutValue_contractEdgeTo_of_pointwise {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} {S' S : Finset β}
    (hpt : ∀ x ∈ g.verts, (redirectTo e w x ∈ S' ↔ x ∈ S)) :
    (g.contractEdgeTo e w).cutValue S' = g.cutValue S :=
  countP_crossing_map_filter hwf _ hpt

/-- Cut lifting (soundness): every cut of the contracted graph
comes from a cut of `g` with the *same* value. Hence rename
contraction can only increase the minimum-cut value. No hypothesis on
`w` needed. -/
lemma exists_isCut_lift_contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} (hmem : ∀ x ∈ e, x ∈ g.verts)
    {S' : Finset β} (h : (g.contractEdgeTo e w).IsCut S') :
    ∃ S, g.IsCut S ∧ g.cutValue S = (g.contractEdgeTo e w).cutValue S' := by
  revert hmem
  induction e with
  | _ a b =>
    intro hmem
    have ha := hmem a (Sym2.mem_mk_left a b)
    refine ⟨g.verts.filter (redirectTo s(a, b) w · ∈ S'),
      ⟨Finset.filter_subset _ _, ?_, ?_⟩, ?_⟩
    · obtain ⟨Y, hY⟩ := h.nonempty
      have hYv := h.subset hY
      rw [verts_contractEdgeTo] at hYv
      rcases Finset.mem_insert.mp hYv with rfl | hYf
      · refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
        simpa [redirectTo, Sym2.mem_mk_left] using hY
      · obtain ⟨hYv', hYe⟩ := Finset.mem_filter.mp hYf
        refine ⟨Y, Finset.mem_filter.mpr ⟨hYv', ?_⟩⟩
        simpa [redirectTo, hYe] using hY
    · obtain ⟨W, hW, hWS⟩ := h.proper
      rw [verts_contractEdgeTo] at hW
      rcases Finset.mem_insert.mp hW with rfl | hWf
      · refine ⟨a, ha, fun hc => ?_⟩
        have := (Finset.mem_filter.mp hc).2
        rw [redirectTo, if_pos (Sym2.mem_mk_left a b)] at this
        exact hWS this
      · obtain ⟨hWv, hWe⟩ := Finset.mem_filter.mp hWf
        refine ⟨W, hWv, fun hc => ?_⟩
        have := (Finset.mem_filter.mp hc).2
        rw [redirectTo, if_neg hWe] at this
        exact hWS this
    · exact (cutValue_contractEdgeTo_of_pointwise hwf fun x hx => by
        simp [Finset.mem_filter, hx]).symm

/-- Cut survival: contracting an edge that does not cross a cut
`S` into a fresh-enough `w` keeps a merge-image of `S` a cut of the
same value. -/
lemma exists_isCut_contractEdgeTo_of_notCrossing {g : MultiGraph β}
    (hwf : g.WF) {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag)
    {S : Finset β} (hS : g.IsCut S) (hnc : ¬ Crossing S e) :
    ∃ S', (g.contractEdgeTo e w).IsCut S' ∧
      (g.contractEdgeTo e w).cutValue S' = g.cutValue S := by
  revert hmem hnd hnc hfresh
  induction e with
  | _ a b =>
    intro hfresh hmem hnd hnc
    rw [Sym2.mk_isDiag_iff] at hnd
    have ha := hmem a (Sym2.mem_mk_left a b)
    have hb := hmem b (Sym2.mem_mk_right a b)
    have hiff : a ∈ S ↔ b ∈ S := by simpa using hnc
    by_cases hain : a ∈ S
    · -- both endpoints inside: the merged vertex joins the cut
      refine ⟨insert w (S.filter (· ∉ s(a, b))),
        ⟨?_, ⟨_, Finset.mem_insert_self ..⟩, ?_⟩, ?_⟩
      · rw [verts_contractEdgeTo]
        exact Finset.insert_subset_insert _
          (Finset.filter_subset_filter _ hS.subset)
      · obtain ⟨W, hWv, hWS⟩ := hS.proper
        have hWe : W ∉ s(a, b) := by
          rw [Sym2.mem_iff]
          push Not
          exact ⟨fun hc => hWS (hc ▸ hain), fun hc => hWS (hc ▸ hiff.mp hain)⟩
        refine ⟨W, ?_, ?_⟩
        · rw [verts_contractEdgeTo]
          exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hWv, hWe⟩)
        · intro hc
          rcases Finset.mem_insert.mp hc with hcU | hcf
          · exact hfresh (hcU ▸ Finset.mem_filter.mpr ⟨hWv, hWe⟩)
          · exact hWS (Finset.mem_filter.mp hcf).1
      · refine cutValue_contractEdgeTo_of_pointwise hwf fun x hx => ?_
        by_cases hxe : x ∈ s(a, b)
        · simp only [redirectTo, if_pos hxe]
          constructor
          · intro _
            rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact hain
            · exact hiff.mp hain
          · intro _
            exact Finset.mem_insert_self ..
        · simp only [redirectTo, if_neg hxe]
          rw [Finset.mem_insert]
          constructor
          · rintro (rfl | hxf)
            · exact absurd (Finset.mem_filter.mpr ⟨hx, hxe⟩) hfresh
            · exact (Finset.mem_filter.mp hxf).1
          · intro hxS
            exact Or.inr (Finset.mem_filter.mpr ⟨hxS, hxe⟩)
    · -- neither endpoint inside: the cut survives verbatim
      have hbin : b ∉ S := fun hc => hain (hiff.mpr hc)
      have hwnot : w ∉ S := by
        intro hc
        by_cases hwe : w ∈ s(a, b)
        · rcases Sym2.mem_iff.mp hwe with rfl | rfl
          · exact hain hc
          · exact hbin hc
        · exact hfresh (Finset.mem_filter.mpr ⟨hS.subset hc, hwe⟩)
      refine ⟨S, ⟨?_, hS.nonempty, ?_⟩, ?_⟩
      · intro Y hY
        rw [verts_contractEdgeTo]
        refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hS.subset hY, ?_⟩)
        rw [Sym2.mem_iff]
        push Not
        exact ⟨fun hc => hain (hc ▸ hY), fun hc => hbin (hc ▸ hY)⟩
      · exact ⟨w, by rw [verts_contractEdgeTo]; exact Finset.mem_insert_self ..,
          hwnot⟩
      · refine cutValue_contractEdgeTo_of_pointwise hwf fun x hx => ?_
        by_cases hxe : x ∈ s(a, b)
        · simp only [redirectTo, if_pos hxe]
          constructor
          · intro hc
            exact absurd hc hwnot
          · intro hc
            rcases Sym2.mem_iff.mp hxe with rfl | rfl
            · exact absurd hc hain
            · exact absurd hc hbin
        · simp only [redirectTo, if_neg hxe]

/-- Rename contraction never decreases the minimum-cut value. -/
lemma minCutValue_le_contractEdgeTo {g : MultiGraph β} (hwf : g.WF)
    {e : Sym2 β} {w : β} (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contractEdgeTo e w).minCutValue := by
  have h2' : 2 ≤ (g.contractEdgeTo e w).verts.card := by
    have := card_verts_contractEdgeTo hfresh hmem hnd
    omega
  obtain ⟨S', hS', hval⟩ := exists_minCut _ h2'
  obtain ⟨S, hScut, hval2⟩ := exists_isCut_lift_contractEdgeTo hwf hmem hS'
  rw [← hval, ← hval2]
  exact minCutValue_le hScut

/-- Contracting an edge that avoids a fixed minimum cut into a
fresh-enough `w` preserves the minimum-cut value exactly, the
per-step fact of every rename-model Karger analysis. -/
lemma minCutValue_contractEdgeTo_of_notCrossing {g : MultiGraph β}
    (hwf : g.WF) {e : Sym2 β} {w : β}
    (hfresh : w ∉ g.verts.filter (· ∉ e))
    (hmem : ∀ x ∈ e, x ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card)
    {S : Finset β} (hS : g.IsCut S)
    (hmin : g.cutValue S = g.minCutValue) (hnc : ¬ Crossing S e) :
    (g.contractEdgeTo e w).minCutValue = g.minCutValue := by
  obtain ⟨S', hcut', hval'⟩ :=
    exists_isCut_contractEdgeTo_of_notCrossing hwf hfresh hmem hnd hS hnc
  refine le_antisymm ?_ (minCutValue_le_contractEdgeTo hwf hfresh hmem hnd h3)
  calc (g.contractEdgeTo e w).minCutValue
      ≤ (g.contractEdgeTo e w).cutValue S' := minCutValue_le hcut'
    _ = g.cutValue S := hval'
    _ = g.minCutValue := hmin

end Rename

/-! ### Supervertex contraction

Contracting `s(S, T)` must produce a single merged vertex, and any
rule that *keeps one of the two* is not a function of the unordered
edge, the two choices give isomorphic but unequal graphs (this was
the old `[LinearOrder α]` artifact: keep `inf`, merge away `sup`).
The supervertex model dissolves the problem: vertices are `Finset β`
of original vertices and merging is `S ∪ T`, which is symmetric, so
contraction is a genuine function of `Sym2 (Finset β)`, with no order
and no choice, and the vertex type is preserved so the contraction
loop stays a plain recursion. It is the rename contraction above at
`w := unionOf e`, and its cut theory is instantiated from the generic
lemmas.

The price is an invariant: the supervertices must be pairwise
disjoint (`SupDisjoint`), since without it the merged vertex can collide
with a third supervertex and contraction drops the vertex count by
two. Disjointness is exactly what discharges the generic freshness
obligation (`unionOf_notMem_filter`). -/

section Super

variable {β : Type} [DecidableEq β]

/-- The union of the two endpoints of an unordered edge, well-defined
by commutativity of `∪` (a genuine `Sym2.lift`: this symmetry is the
point of the supervertex model). -/
def unionOf : Sym2 (Finset β) → Finset β :=
  Sym2.lift ⟨(· ∪ ·), Finset.union_comm⟩

@[simp] lemma unionOf_mk (S T : Finset β) : unionOf s(S, T) = S ∪ T := rfl

/-- Redirect a supervertex under the `∪`-merge of the endpoints of
`e`: both endpoints become their union, everything else is unchanged.
Symmetric in the two endpoints by construction. -/
def redirectS (e : Sym2 (Finset β)) (X : Finset β) : Finset β :=
  if X ∈ e then unionOf e else X

/-- The supervertices are pairwise disjoint, the invariant that makes
the `∪`-merge well-behaved. -/
def SupDisjoint (g : MultiGraph (Finset β)) : Prop :=
  ∀ S ∈ g.verts, ∀ T ∈ g.verts, S ≠ T → Disjoint S T

/-- Contract the edge `e` by the supervertex merge: its two
endpoints leave the vertex set, their union enters, every edge is
redirected through `redirectS e` and the resulting loops (the parallel
copies of `e` itself) are dropped; parallel edges are kept. A genuine
function of the *unordered* edge. -/
def contractEdge (g : MultiGraph (Finset β)) (e : Sym2 (Finset β)) :
    MultiGraph (Finset β) where
  verts := insert (unionOf e) (g.verts.filter (· ∉ e))
  edges := (g.edges.map (Sym2.map (redirectS e))).filter fun e' => !e'.IsDiag

@[simp] lemma verts_contractEdge (g : MultiGraph (Finset β)) (e : Sym2 (Finset β)) :
    (g.contractEdge e).verts = insert (unionOf e) (g.verts.filter (· ∉ e)) := rfl

@[simp] lemma edges_contractEdge (g : MultiGraph (Finset β)) (e : Sym2 (Finset β)) :
    (g.contractEdge e).edges =
      (g.edges.map (Sym2.map (redirectS e))).filter fun e' => !e'.IsDiag := rfl

/-- Under disjointness the merged vertex is *fresh*: it cannot coincide
with any supervertex other than the merged endpoints themselves. -/
lemma unionOf_notMem_filter {g : MultiGraph (Finset β)} (hdisj : SupDisjoint g)
    {e : Sym2 (Finset β)} (hmem : ∀ X ∈ e, X ∈ g.verts) (hnd : ¬ e.IsDiag) :
    unionOf e ∉ g.verts.filter (· ∉ e) := by
  revert hmem hnd
  induction e with
  | _ S T =>
    intro hmem hnd
    rw [Sym2.mk_isDiag_iff] at hnd
    intro hU
    obtain ⟨hUv, hUe⟩ := Finset.mem_filter.mp hU
    simp only [unionOf_mk] at hUv hUe
    have hS := hmem S (Sym2.mem_mk_left S T)
    have hT := hmem T (Sym2.mem_mk_right S T)
    have hneS : S ∪ T ≠ S := fun hc => hUe (by rw [hc]; exact Sym2.mem_mk_left S T)
    have hneT : S ∪ T ≠ T := fun hc => hUe (by rw [hc]; exact Sym2.mem_mk_right S T)
    have hSe : S = ∅ := by
      have : Disjoint S S :=
        ((hdisj _ hUv _ hS hneS).mono_left Finset.subset_union_left)
      simpa using disjoint_self.mp this
    have hTe : T = ∅ := by
      have : Disjoint T T :=
        ((hdisj _ hUv _ hT hneT).mono_left Finset.subset_union_right)
      simpa using disjoint_self.mp this
    exact hnd (hSe.trans hTe.symm)

/-- Contraction removes exactly one supervertex: two leave, their
union enters, and it is *fresh*, by disjointness. -/
lemma card_verts_contractEdge {g : MultiGraph (Finset β)} (hdisj : SupDisjoint g)
    {e : Sym2 (Finset β)} (hmem : ∀ X ∈ e, X ∈ g.verts) (hnd : ¬ e.IsDiag) :
    (g.contractEdge e).verts.card + 1 = g.verts.card :=
  card_verts_contractEdgeTo (unionOf_notMem_filter hdisj hmem hnd) hmem hnd

/-- Contraction preserves well-formedness. -/
theorem WF.contractEdge {g : MultiGraph (Finset β)} (hwf : g.WF)
    {e : Sym2 (Finset β)} : (g.contractEdge e).WF :=
  hwf.contractEdgeTo (e := e) (w := unionOf e)

/-- Contraction preserves pairwise disjointness of the supervertices. -/
lemma SupDisjoint.contractEdge {g : MultiGraph (Finset β)} (hdisj : SupDisjoint g)
    {e : Sym2 (Finset β)} (hmem : ∀ X ∈ e, X ∈ g.verts) :
    SupDisjoint (g.contractEdge e) := by
  revert hmem
  induction e with
  | _ S T =>
    intro hmem A hA B hB hAB
    rw [verts_contractEdge] at hA hB
    have hS := hmem S (Sym2.mem_mk_left S T)
    have hT := hmem T (Sym2.mem_mk_right S T)
    have hkey : ∀ W ∈ g.verts.filter (· ∉ s(S, T)),
        Disjoint (unionOf s(S, T)) W := by
      intro W hW
      obtain ⟨hWv, hWe⟩ := Finset.mem_filter.mp hW
      rw [Sym2.mem_iff] at hWe
      push Not at hWe
      rw [unionOf_mk]
      exact Finset.disjoint_union_left.mpr
        ⟨(hdisj S hS W hWv fun hc => hWe.1 hc.symm),
         (hdisj T hT W hWv fun hc => hWe.2 hc.symm)⟩
    rcases Finset.mem_insert.mp hA with rfl | hAf
    · rcases Finset.mem_insert.mp hB with rfl | hBf
      · exact absurd rfl hAB
      · exact hkey B hBf
    · rcases Finset.mem_insert.mp hB with rfl | hBf
      · exact (hkey A hAf).symm
      · exact hdisj A (Finset.mem_filter.mp hAf).1 B (Finset.mem_filter.mp hBf).1 hAB

/-- Contraction never increases the edge count. -/
lemma length_edges_contractEdge_le (g : MultiGraph (Finset β)) (e : Sym2 (Finset β)) :
    (g.contractEdge e).edges.length ≤ g.edges.length :=
  le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map ..))

/-- Cut-value transport along one contraction: if membership in `𝒮'`
after redirection agrees pointwise with membership in `𝒮`, the two
cuts have the same value. -/
lemma cutValue_contractEdge_of_pointwise {g : MultiGraph (Finset β)} (hwf : g.WF)
    {e : Sym2 (Finset β)} {𝒮' 𝒮 : Finset (Finset β)}
    (hpt : ∀ X ∈ g.verts, (redirectS e X ∈ 𝒮' ↔ X ∈ 𝒮)) :
    (g.contractEdge e).cutValue 𝒮' = g.cutValue 𝒮 :=
  countP_crossing_map_filter hwf _ hpt

/-- Cut lifting (soundness of contraction): every cut of the
contracted graph comes from a cut of `g` with the *same* value. Hence
contraction can only increase the minimum-cut value. -/
lemma exists_isCut_lift {g : MultiGraph (Finset β)} (hwf : g.WF)
    {e : Sym2 (Finset β)} (hmem : ∀ X ∈ e, X ∈ g.verts)
    {𝒮' : Finset (Finset β)} (h : (g.contractEdge e).IsCut 𝒮') :
    ∃ 𝒮, g.IsCut 𝒮 ∧ g.cutValue 𝒮 = (g.contractEdge e).cutValue 𝒮' :=
  exists_isCut_lift_contractEdgeTo hwf hmem h

/-- Cut survival: contracting an edge that does not cross a cut
`𝒮` keeps a merge-image of `𝒮` a cut of the same value. -/
lemma exists_isCut_contractEdge_of_notCrossing {g : MultiGraph (Finset β)}
    (hwf : g.WF) (hdisj : SupDisjoint g) {e : Sym2 (Finset β)}
    (hmem : ∀ X ∈ e, X ∈ g.verts) (hnd : ¬ e.IsDiag)
    {𝒮 : Finset (Finset β)} (h𝒮 : g.IsCut 𝒮) (hnc : ¬ Crossing 𝒮 e) :
    ∃ 𝒮', (g.contractEdge e).IsCut 𝒮' ∧
      (g.contractEdge e).cutValue 𝒮' = g.cutValue 𝒮 :=
  exists_isCut_contractEdgeTo_of_notCrossing hwf
    (unionOf_notMem_filter hdisj hmem hnd) hmem hnd h𝒮 hnc

/-- Contraction never decreases the minimum-cut value. -/
lemma minCutValue_le_contractEdge {g : MultiGraph (Finset β)} (hwf : g.WF)
    (hdisj : SupDisjoint g) {e : Sym2 (Finset β)}
    (hmem : ∀ X ∈ e, X ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contractEdge e).minCutValue :=
  minCutValue_le_contractEdgeTo hwf
    (unionOf_notMem_filter hdisj hmem hnd) hmem hnd h3

/-- Contracting an edge that avoids a fixed minimum cut preserves the
minimum-cut value exactly, the per-step fact of Karger's analysis. -/
lemma minCutValue_contractEdge_of_notCrossing {g : MultiGraph (Finset β)}
    (hwf : g.WF) (hdisj : SupDisjoint g) {e : Sym2 (Finset β)}
    (hmem : ∀ X ∈ e, X ∈ g.verts) (hnd : ¬ e.IsDiag) (h3 : 3 ≤ g.verts.card)
    {𝒮 : Finset (Finset β)} (h𝒮 : g.IsCut 𝒮)
    (hmin : g.cutValue 𝒮 = g.minCutValue) (hnc : ¬ Crossing 𝒮 e) :
    (g.contractEdge e).minCutValue = g.minCutValue :=
  minCutValue_contractEdgeTo_of_notCrossing hwf
    (unionOf_notMem_filter hdisj hmem hnd) hmem hnd h3 h𝒮 hmin hnc

/-! ### Contraction of a listed edge -/

/-- Contract the `i`-th edge of the list. -/
def contract (g : MultiGraph (Finset β)) (i : Fin g.edges.length) :
    MultiGraph (Finset β) :=
  g.contractEdge g.edges[(i : ℕ)]

lemma WF.contract {g : MultiGraph (Finset β)} (hwf : g.WF)
    (i : Fin g.edges.length) : (g.contract i).WF :=
  hwf.contractEdge

lemma SupDisjoint.contract {g : MultiGraph (Finset β)} (hdisj : SupDisjoint g)
    (hwf : g.WF) (i : Fin g.edges.length) : SupDisjoint (g.contract i) :=
  hdisj.contractEdge (hwf.incidence _ (List.getElem_mem _))

lemma card_verts_contract {g : MultiGraph (Finset β)} (hwf : g.WF)
    (hdisj : SupDisjoint g) (i : Fin g.edges.length) :
    (g.contract i).verts.card + 1 = g.verts.card :=
  card_verts_contractEdge hdisj (hwf.incidence _ (List.getElem_mem _))
    (hwf.loopless _ (List.getElem_mem _))

lemma length_edges_contract_le (g : MultiGraph (Finset β)) (i : Fin g.edges.length) :
    (g.contract i).edges.length ≤ g.edges.length :=
  length_edges_contractEdge_le g _

lemma minCutValue_le_contract {g : MultiGraph (Finset β)} (hwf : g.WF)
    (hdisj : SupDisjoint g) (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (g.contract i).minCutValue :=
  minCutValue_le_contractEdge hwf hdisj (hwf.incidence _ (List.getElem_mem _))
    (hwf.loopless _ (List.getElem_mem _)) h3

/-! ### The supervertex embedding -/

/-- Enter the supervertex world: each vertex becomes its singleton.
The contraction loop starts here, and the supervertices it merges are
exactly the fibres a run has accumulated, the final vertex set *is*
the reported cut, with no extra bookkeeping. -/
def super (g : MultiGraph β) : MultiGraph (Finset β) where
  verts := g.verts.image fun a => {a}
  edges := g.edges.map (Sym2.map fun a => {a})

@[simp] lemma verts_super (g : MultiGraph β) :
    (g.super).verts = g.verts.image fun a => {a} := rfl

@[simp] lemma edges_super (g : MultiGraph β) :
    (g.super).edges = g.edges.map (Sym2.map fun a => {a}) := rfl

lemma card_verts_super (g : MultiGraph β) :
    (g.super).verts.card = g.verts.card :=
  Finset.card_image_of_injective _ fun _ _ h => Finset.singleton_injective h

lemma length_edges_super (g : MultiGraph β) :
    (g.super).edges.length = g.edges.length :=
  List.length_map ..

theorem WF.super {g : MultiGraph β} (hwf : g.WF) : (g.super).WF := by
  constructor
  · intro e' he' Y hY
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp hY
    exact Finset.mem_image_of_mem _ (hwf.incidence e he a ha)
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    revert he
    induction e with
    | _ a b =>
      intro he hd
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff] at hd
      exact hwf.loopless _ he
        (Sym2.mk_isDiag_iff.mpr (Finset.singleton_injective hd))

lemma supDisjoint_super (g : MultiGraph β) : SupDisjoint (g.super) := by
  intro A hA B hB hAB
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hB
  exact Finset.disjoint_singleton.mpr fun hc => hAB (hc ▸ rfl)

/-! ### Tracking the supervertices -/

/-- The supervertex graph `g` tracks `g₀`: its vertices are
pairwise-disjoint nonempty sets of original vertices covering all of
them, and every cut of `g` flattens (`⋃`) to a cut of `g₀` of the same
value. A contraction run maintains this invariant, and at the end the
surviving supervertices are, verbatim, the sides of the reported cut. -/
structure Tracks (g₀ : MultiGraph β) (g : MultiGraph (Finset β)) : Prop where
  /-- Every supervertex consists of original vertices. -/
  subset : ∀ S ∈ g.verts, S ⊆ g₀.verts
  /-- Every supervertex is nonempty. -/
  nonempty : ∀ S ∈ g.verts, S.Nonempty
  /-- The supervertices are pairwise disjoint. -/
  disj : SupDisjoint g
  /-- Every original vertex sits in some supervertex. -/
  covers : ∀ a ∈ g₀.verts, ∃ S ∈ g.verts, a ∈ S
  /-- Cuts flatten with the same value. -/
  cut : ∀ 𝒮 ⊆ g.verts, g.cutValue 𝒮 = g₀.cutValue (𝒮.biUnion id)

/-- The singleton embedding tracks the original graph. -/
lemma Tracks.super (g : MultiGraph β) : Tracks g g.super := by
  refine ⟨?_, ?_, supDisjoint_super g, ?_, ?_⟩
  · intro S hS
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.singleton_subset_iff.mpr ha
  · intro S hS
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.singleton_nonempty a
  · intro a ha
    exact ⟨{a}, Finset.mem_image_of_mem _ ha, Finset.mem_singleton_self a⟩
  · intro 𝒮 h𝒮
    have hkey : ∀ a : β, (a ∈ 𝒮.biUnion id ↔ {a} ∈ 𝒮) := by
      intro a
      simp only [Finset.mem_biUnion, id]
      constructor
      · rintro ⟨Y, hY, haY⟩
        obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp (h𝒮 hY)
        rw [Finset.mem_singleton] at haY
        exact haY ▸ hY
      · intro h
        exact ⟨{a}, h, Finset.mem_singleton_self a⟩
    unfold cutValue
    rw [edges_super, List.countP_map]
    refine List.countP_congr fun e he => ?_
    induction e with
    | _ a b =>
      simp only [Function.comp_apply, Sym2.map_mk, crossing_mk,
        hkey a, hkey b]

/-- Tracking survives one `∪`-merge contraction of a listed edge. -/
lemma Tracks.contractEdge {g₀ : MultiGraph β} {g : MultiGraph (Finset β)}
    (hwf : g.WF) (ht : Tracks g₀ g) {e : Sym2 (Finset β)} (he : e ∈ g.edges) :
    Tracks g₀ (g.contractEdge e) := by
  have hmem := hwf.incidence e he
  have hnd := hwf.loopless e he
  clear he
  revert hmem hnd
  induction e with
  | _ S T =>
    intro hmem hnd
    have hS := hmem S (Sym2.mem_mk_left S T)
    have hT := hmem T (Sym2.mem_mk_right S T)
    refine ⟨?_, ?_, ht.disj.contractEdge hmem, ?_, ?_⟩
    · intro A hA
      rw [verts_contractEdge] at hA
      rcases Finset.mem_insert.mp hA with rfl | hAf
      · rw [unionOf_mk]
        exact Finset.union_subset (ht.subset S hS) (ht.subset T hT)
      · exact ht.subset A (Finset.mem_filter.mp hAf).1
    · intro A hA
      rw [verts_contractEdge] at hA
      rcases Finset.mem_insert.mp hA with rfl | hAf
      · rw [unionOf_mk]
        exact (ht.nonempty S hS).mono Finset.subset_union_left
      · exact ht.nonempty A (Finset.mem_filter.mp hAf).1
    · intro a ha
      obtain ⟨A, hA, haA⟩ := ht.covers a ha
      by_cases hAe : A ∈ s(S, T)
      · refine ⟨unionOf s(S, T), Finset.mem_insert_self .., ?_⟩
        rw [unionOf_mk]
        rcases Sym2.mem_iff.mp hAe with rfl | rfl
        · exact Finset.mem_union_left _ haA
        · exact Finset.mem_union_right _ haA
      · exact ⟨A, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hA, hAe⟩), haA⟩
    · intro 𝒮' h𝒮'
      rw [cutValue_contractEdge_of_pointwise
          (𝒮 := g.verts.filter (redirectS s(S, T) · ∈ 𝒮')) hwf
          (fun X hX => by simp [Finset.mem_filter, hX]),
        ht.cut _ (Finset.filter_subset _ _)]
      congr 1
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter, id]
      constructor
      · rintro ⟨X, ⟨hXv, hX𝒮'⟩, haX⟩
        by_cases hXe : X ∈ s(S, T)
        · rw [redirectS, if_pos hXe] at hX𝒮'
          refine ⟨unionOf s(S, T), hX𝒮', ?_⟩
          rw [unionOf_mk]
          rcases Sym2.mem_iff.mp hXe with rfl | rfl
          · exact Finset.mem_union_left _ haX
          · exact Finset.mem_union_right _ haX
        · rw [redirectS, if_neg hXe] at hX𝒮'
          exact ⟨X, hX𝒮', haX⟩
      · rintro ⟨Y, hY𝒮', haY⟩
        have hYv' := h𝒮' hY𝒮'
        rw [verts_contractEdge] at hYv'
        rcases Finset.mem_insert.mp hYv' with rfl | hYf
        · rw [unionOf_mk] at haY
          rcases Finset.mem_union.mp haY with ha | ha
          · exact ⟨S, ⟨hS, by
              rw [redirectS, if_pos (Sym2.mem_mk_left S T)]; exact hY𝒮'⟩, ha⟩
          · exact ⟨T, ⟨hT, by
              rw [redirectS, if_pos (Sym2.mem_mk_right S T)]; exact hY𝒮'⟩, ha⟩
        · obtain ⟨hYv, hYe⟩ := Finset.mem_filter.mp hYf
          exact ⟨Y, ⟨hYv, by rw [redirectS, if_neg hYe]; exact hY𝒮'⟩, haY⟩

/-- Tracking survives contracting the `i`-th listed edge. -/
lemma Tracks.contract {g₀ : MultiGraph β} {g : MultiGraph (Finset β)}
    (hwf : g.WF) (ht : Tracks g₀ g) (i : Fin g.edges.length) :
    Tracks g₀ (g.contract i) :=
  ht.contractEdge hwf (List.getElem_mem _)

/-! ### Reading the cut off the surviving supervertices -/

/-- Every surviving supervertex is a genuine cut of the tracked graph. -/
lemma Tracks.isCut_mem {g₀ : MultiGraph β} {g : MultiGraph (Finset β)}
    (ht : Tracks g₀ g) (h2 : 2 ≤ g.verts.card) {S : Finset β}
    (hS : S ∈ g.verts) : g₀.IsCut S := by
  refine ⟨ht.subset S hS, ht.nonempty S hS, ?_⟩
  obtain ⟨T, hT, hTS⟩ : ∃ T ∈ g.verts, T ≠ S := by
    obtain ⟨A, B, hA, hB, hAB⟩ := Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
    by_cases hAS : A = S
    · exact ⟨B, hB, fun hc => hAB (hAS.trans hc.symm)⟩
    · exact ⟨A, hA, hAS⟩
  obtain ⟨b, hb⟩ := ht.nonempty T hT
  exact ⟨b, ht.subset T hT hb,
    fun hbS => Finset.disjoint_left.mp (ht.disj T hT S hS hTS) hb hbS⟩

/-- The bridge: when a run finishes (two supervertices remain, or
no edges do) every surviving supervertex cuts the tracked graph with
value exactly the number of surviving edges. -/
lemma Tracks.cutValue_mem {g₀ : MultiGraph β} {g : MultiGraph (Finset β)}
    (hwf : g.WF) (ht : Tracks g₀ g)
    (hend : g.verts.card = 2 ∨ g.edges = []) {S : Finset β}
    (hS : S ∈ g.verts) : g₀.cutValue S = g.edges.length := by
  have h1 := ht.cut {S} (Finset.singleton_subset_iff.mpr hS)
  rw [Finset.singleton_biUnion, id] at h1
  rcases hend with hcard | hnil
  · rw [← h1]
    refine cutValue_of_card_two hwf hcard
      ⟨Finset.singleton_subset_iff.mpr hS, Finset.singleton_nonempty S, ?_⟩
    obtain ⟨T, hT, hTS⟩ : ∃ T ∈ g.verts, T ≠ S := by
      obtain ⟨A, B, hA, hB, hAB⟩ := Finset.one_lt_card_iff.mp (show 1 < g.verts.card by omega)
      by_cases hAS : A = S
      · exact ⟨B, hB, fun hc => hAB (hAS.trans hc.symm)⟩
      · exact ⟨A, hA, hAS⟩
    exact ⟨T, hT, by simp [hTS]⟩
  · rw [← h1]
    simp [cutValue, hnil]

/-- Flattening any cut of the supervertex graph yields a cut of the
tracked graph (of the same value, by `Tracks.cut`). -/
lemma Tracks.isCut_biUnion {g₀ : MultiGraph β} {g : MultiGraph (Finset β)}
    (ht : Tracks g₀ g) {𝒮 : Finset (Finset β)} (h𝒮 : g.IsCut 𝒮) :
    g₀.IsCut (𝒮.biUnion id) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨Y, hY, haY⟩ := Finset.mem_biUnion.mp ha
    exact ht.subset Y (h𝒮.subset hY) haY
  · obtain ⟨Y, hY⟩ := h𝒮.nonempty
    obtain ⟨a, ha⟩ := ht.nonempty Y (h𝒮.subset hY)
    exact ⟨a, Finset.mem_biUnion.mpr ⟨Y, hY, ha⟩⟩
  · obtain ⟨W, hWv, hW𝒮⟩ := h𝒮.proper
    obtain ⟨b, hb⟩ := ht.nonempty W hWv
    refine ⟨b, ht.subset W hWv hb, fun hc => ?_⟩
    obtain ⟨Y, hY, hbY⟩ := Finset.mem_biUnion.mp hc
    exact Finset.disjoint_left.mp
      (ht.disj Y (h𝒮.subset hY) W hWv fun hc' => hW𝒮 (hc' ▸ hY)) hbY hb

/-- The supervertex embedding preserves the minimum-cut value. -/
lemma minCutValue_super {g : MultiGraph β} (h2 : 2 ≤ g.verts.card) :
    (g.super).minCutValue = g.minCutValue := by
  have ht := Tracks.super g
  have h2' : 2 ≤ (g.super).verts.card := by rw [card_verts_super]; exact h2
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hS, hval⟩ := exists_minCut g h2
    have hcut : (g.super).IsCut (S.image fun a => {a}) := by
      refine ⟨?_, hS.nonempty.image _, ?_⟩
      · rw [verts_super]
        exact Finset.image_subset_image hS.subset
      · obtain ⟨v, hv, hvS⟩ := hS.proper
        refine ⟨{v}, by rw [verts_super]; exact Finset.mem_image_of_mem _ hv,
          fun hc => ?_⟩
        obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hc
        exact hvS (Finset.singleton_injective hwv ▸ hw)
    have hval2 : (g.super).cutValue (S.image fun a => {a}) = g.cutValue S := by
      rw [ht.cut _ hcut.subset]
      congr 1
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_image, id]
      constructor
      · rintro ⟨Y, ⟨c, hc, rfl⟩, haY⟩
        rw [Finset.mem_singleton] at haY
        exact haY ▸ hc
      · intro ha
        exact ⟨{a}, ⟨a, ha, rfl⟩, Finset.mem_singleton_self a⟩
    rw [← hval, ← hval2]
    exact minCutValue_le hcut
  · obtain ⟨𝒮, h𝒮, hval⟩ := exists_minCut _ h2'
    rw [← hval, ht.cut 𝒮 h𝒮.subset]
    exact minCutValue_le (ht.isCut_biUnion h𝒮)

end Super

end MultiGraph

end ARA
