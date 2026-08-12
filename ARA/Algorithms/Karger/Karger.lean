/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Algorithms.Karger.DesignDiscussion.KargerVariants

/-!
# Karger with an abstract pick: the cut, not just its value

In a contraction the two endpoints of the drawn edge leave and one
vertex `w` enters. Someone has to produce `w`. Here that someone is a
parameter, `pick : MultiGraph α → Sym2 α → α`. Merge into the smaller
endpoint, into the endpoint of smaller label, into a brand-new name:
each is one pick, and this file runs Karger once for all of them. The
vertex type never changes along a run, so the loop is a plain
recursion (`contractPick`). It carries no fuel: the guard is the state
of the graph, and termination is the edge count, which drops at every
step because the drawn edge becomes a loop and is filtered out.

Two ideas carry the file.

*`pick` defines, `fresh` proves.* Nothing is asked of `pick` to write
or run the algorithm; even termination is unconditional. Every theorem
asks exactly one thing of it (`MergeRule.fresh`): the merged vertex
collides with no untouched vertex. That single hypothesis is where the
order, labelling and fresh-name models each pay, in their own way.

*`rep` remembers what the merge forgets.* A merged vertex carries no
history. That is why the models in `KargerVariants.lean` report only
the cut value. Here we carry the history ourselves:
`rep : α → Finset α` sends each live vertex to the set of original
vertices merged into it. It starts at singletons, and when `e` is
contracted into `w` the fibre of `w` becomes the union of the two
endpoint fibres (`repOf`; unions are symmetric, so this is a genuine
function of the unordered edge). When the loop stops, the fibres of
the survivors are the sides of the cut. So every model returns the cut
and its value, not the value alone.

As everywhere in ARA, the algorithm is written once against
`RandMonad` and `MonadCost ℕ`, and read at `M = IO` (run it),
`M = PMF` (its law), and `M = TimeMT ℕ M'` (timed).

## Why sampling from a set is not trivial

A uniform element of a finite set is well-defined as a *distribution* —
`PMF.uniformOfFinset` exists, with no order and no choice, because
uniformity is precisely the distribution that does not depend on any
enumeration. It is not well-defined as a *program*. A `Finset` is a
quotient of lists by permutation, and a function out of a quotient must
be invariant under the relation; a program that draws cannot be — at
`M = IO`, drawing from `[a, b]` and from `[b, a]` are different
programs — only its output law is. So an executable draw must be given
a representative, and there are exactly three ways to get one: choice
(`Finset.toList` is noncomputable — the `IO` reading dies), a linear
order (`Finset.sort` — an assumption the min-cut problem does not
mention, sitting inside the sampler of every algorithm), or reading the
runtime representation through `unsafe`/`@[implemented_by]` (trusted
code invisible in the algorithm text). We take none of them: the
primitive is `randFin n`, and the edge collection is carried as a
`List` — the representative declared once, in the input, where everyone
can see it. The list also carries multiplicity, which `Finset` cannot,
and Karger's `2/n` step bound is false without it: contraction creates
parallel edges even from simple input, and the draw must be
proportional to multiplicity.

## The price of no fuel

With fuel, the `(n − 2) · m` cost bound holds for arbitrary inputs.
Without it the round count is derived, not declared: the vertex count
drops by one per step only under `WF` and freshness, so
`karger_cost_le` needs both. We chose the loop a reader would
write, and pay for it in the hypotheses of the cost bounds (the
fueled alternative survives as `contractAuxVia` in
`KargerVariants.lean`).

## Main results

* `karger_finds_min`: a single run returns an actual minimum cut
  with probability at least `2 / (n (n - 1))`, for every merge rule.
* `karger_isCut`: one-sided error, on every run: each reported
  side is a genuine cut of the input, of exactly the reported value,
  and that value never undershoots the minimum.
* `success_contractPick`: survival of the minimum cut through partial
  contraction, the kernel shared with Karger–Stein
  (`karger_success_prob` is its `s = 0` value-level corollary).
* `karger_cost_le`: expected cost at most `(n - 2) * m`, one tick
  per edge scanned.
* `karger_amplified`: the best of `k` runs succeeds with
  probability at least `1 − (1 − 2/(n(n−1)))^k`.
* `kargerOrder_*`, `kargerEnum_*`, `kargerFresh_*`: the
  three rename models, upgraded from value-level to cut-level.

## Pointers

The supervertex model, where `rep` would be the identity because a
vertex *is* its own fibre, is no longer a code path: `Variants.lean`
records the design discussion, and the supervertex section of
`ARA/Helpers/MultiGraph.lean` keeps the exhibit. `KargerVariants.lean`
holds the value-level results this file upgrades. `KargerStein.lean`
recurses on `contractPick` at target `ksTarget n`. The graph layer
stands in for `sorrachai/GraphLib` (see `ARA/Helpers/MultiGraph.lean`);
upstream contraction is a `Setoid` quotient in Weixuan Yuan's fork,
and `rep` is the executable fibre map of that quotient, so the
eventual adapter is mechanical.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-! ## Algorithm

One contraction step (`contractAt`), the fibre bookkeeping (`repOf`,
`updateRep`), the loop (`contractPick`), the readout (`Karger`). -/

/-- Contract the `i`-th listed edge into a vertex the pick
function chooses. -/
def contractAt (pick : MultiGraph α → Sym2 α → α)
    (g : MultiGraph α) (i : Fin g.edges.length) : MultiGraph α :=
  g.contractEdgeTo g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)])

/-- The contracted edge always becomes a loop. -/
private lemma map_self_isDiag (e : Sym2 α) (w : α) :
    (Sym2.map (redirectTo e w) e).IsDiag := by
  induction e with
  | _ u v => simp [redirectTo]

/-- `contractAt` strictly drops the edge count, the loop's
termination measure. -/
theorem length_edges_contractAt_lt (pick : MultiGraph α → Sym2 α → α)
    (g : MultiGraph α) (i : Fin g.edges.length) :
    (contractAt pick g i).edges.length < g.edges.length := by
  rw [contractAt, edges_contractEdgeTo]
  refine lt_of_lt_of_le (List.length_filter_lt_length_iff_exists.mpr
    ⟨_, List.mem_map_of_mem (List.getElem_mem _),
      by simpa using map_self_isDiag ..⟩)
    (by simp)

/-- Well-formedness survives `contractAt`. -/
theorem MultiGraph.WF.contractAt {g : MultiGraph α}
    (hwf : g.WF) (pick : MultiGraph α → Sym2 α → α) (i : Fin g.edges.length) :
    (contractAt pick g i).WF :=
  hwf.contractEdgeTo

/-- The fibre of the drawn edge: the union of its endpoints' fibres,
lifted through `Sym2` (symmetry is the well-definedness obligation). -/
def repOf (rep : α → Finset α) : Sym2 α → Finset α :=
  Sym2.lift ⟨fun u v => rep u ∪ rep v, fun _ _ => Finset.union_comm _ _⟩

/-- `repOf` on `s(u, v)` is `rep u ∪ rep v`. -/
@[simp] lemma repOf_mk (rep : α → Finset α) (u v : α) :
    repOf rep s(u, v) = rep u ∪ rep v := rfl

/-- The update of the report function after contracting `e` into `w`:
send every `x ≠ w` to `rep x`, and `w` to `repOf rep e`, i.e. to the union
of the two endpoint fibres. -/
def updateRep (rep : α → Finset α) (e : Sym2 α) (w : α) : α → Finset α :=
  fun x => if x = w then repOf rep e else rep x

/-- The merge target gets the merged fibre. -/
@[simp] lemma updateRep_self (rep : α → Finset α) (e : Sym2 α) (w : α) :
    updateRep rep e w w = repOf rep e := if_pos rfl

/-- Untouched vertices keep their fibre. -/
@[simp] lemma updateRep_of_ne {x w : α} (rep : α → Finset α) (e : Sym2 α)
    (h : x ≠ w) : updateRep rep e w x = rep x := if_neg h

/-- The contraction loop, carrying the report function along: draw a
uniform edge, contract it into the picked vertex, update the fibre of
the pick, while `t + 1 ≤ verts.card ∧ 0 < edges.length`. Karger runs
the target `t = 2`; Karger–Stein runs `t = ksTarget n`. It terminates
since the edge count drops strictly at each step. Ticks once per edge
scanned, like `contractAuxVia`. -/
def contractPick {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) (t : ℕ)
    (g : MultiGraph α) (rep : α → Finset α) :
    M (MultiGraph α × (α → Finset α)) :=
  -- keep contracting while an edge remains; stop at `t` vertices, at
  -- `t = 2` one step before the cut would disappear
  if h : t + 1 ≤ g.verts.card ∧ 0 < g.edges.length then do
    -- the round costs one tick per edge: contracting walks the whole
    -- list to redirect it and drop the loops
    MonadCost.tick g.edges.length
    -- a uniform position in the list is an edge drawn with probability
    -- proportional to its multiplicity; `h.2` keeps the index in range
    let i ← randIdx g.edges h.2
    -- contract the drawn edge into the picked vertex, and record the
    -- merge: the pick's fibre becomes the union of the endpoint previous
    -- fibres
    contractPick pick t (contractAt pick g i)
      (updateRep rep g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)]))
  else
    -- end state: `t` vertices remain, or the edges ran out
    pure (g, rep)
termination_by g.edges.length
decreasing_by exact length_edges_contractAt_lt pick g i

/-- Karger's algorithm with an abstract pick: contract random edges
until two vertices remain (or the edges run out), then report the
fibres of the survivors (the cut itself) together with the number
of surviving edges (its value). -/
def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) (g : MultiGraph α) :
    M (Finset (Finset α) × ℕ) := do
  let p ← contractPick pick 2 g (fun a => {a})
  pure (p.1.verts.image p.2, p.1.edges.length)

/-! ## Instances and demos

The three readings promised in the module docstring, on the demo
graphs of `KargerVariants.lean` (two triangles joined by a bridge,
minimum cut `1`). The outputs are random: sides and value vary from
run to run. -/

/-- The order model of `KargerVariants.lean`, now reporting the cut. -/
def KargerOrder {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    [LinearOrder α] (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
  Karger orderRule.pick g

/-- Enumeration model, now reporting the cut. -/
def KargerEnum {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (ℓ : α ↪ ℕ) (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
  Karger (enumRule ℓ).pick g

/-- Fresh-name model, now reporting the cut. -/
def KargerFresh {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph ℕ) : M (Finset (Finset ℕ) × ℕ) :=
  Karger freshRule.pick g

/-- The fresh-name model at `M = IO`: executable, untimed. -/
def KargerFresh_IO : MultiGraph ℕ → IO (Finset (Finset ℕ) × ℕ) :=
  KargerFresh

-- e.g. `({{0, 1, 2, 3}, {4, 5}}, 2)`: a genuine cut of value `2`;
-- this run missed the bridge
#eval KargerFresh_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) :=
  KargerFresh

/-- The fresh-name model timed: `TimeMT ℕ IO` counts the ticks. -/
def KargerFresh_IO_Timed :
    MultiGraph ℕ → TimeMT ℕ IO (Finset (Finset ℕ) × ℕ) :=
  KargerFresh

-- e.g. `{ ret := ({{0, 1}, {2, 3, 4, 5}}, 2), time := 20 }`: the same
-- output, plus the tick count
#eval (KargerFresh_IO_Timed kargerDemo).run

-- PMF timed version (noncomputable specification)
noncomputable example : MultiGraph ℕ → TimeMT ℕ PMF (Finset (Finset ℕ) × ℕ) :=
  KargerFresh

-- The other two picks run too: order on `ℕ` vertices…
def KargerOrder_IO : MultiGraph ℕ → IO (Finset (Finset ℕ) × ℕ) :=
  KargerOrder

-- e.g. `({{0, 1, 2}, {3, 4, 5}}, 1)`: this run found the bridge
#eval KargerOrder_IO kargerDemo

-- …and enumeration on the unordered `City` type. The `Repr` instance
-- lives here because only this file's output prints `City` values.
deriving instance Repr for City

def KargerEnum_IO : MultiGraph City → IO (Finset (Finset City) × ℕ) :=
  KargerEnum cityLabel

-- e.g. `({{zrh, gva, bsl}, {ber, lug, lau}}, 1)`: the sides are sets
-- of cities, no numbers anywhere
#eval KargerEnum_IO cityDemo

/-! ## Helper lemmas for the analysis

The two fresh-only step facts: a fresh contraction loses exactly one
vertex (`card_verts_contractAt`) and never drops the minimum-cut value
(`minCutValue_le_contractAt`). Note the signatures: `contractAt` takes
a bare pick, these take a `MergeRule`. -/

/-- Freshness makes the contraction lose exactly one vertex. -/
lemma card_verts_contractAt (R : MergeRule α) {g : MultiGraph α}
    (hwf : g.WF) (i : Fin g.edges.length) :
    (contractAt R.pick g i).verts.card + 1 = g.verts.card :=
  card_verts_contractVia R hwf i

/-- The minimum-cut value never drops under a fresh contraction. -/
lemma minCutValue_le_contractAt (R : MergeRule α) {g : MultiGraph α}
    (hwf : g.WF) (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (contractAt R.pick g i).minCutValue :=
  minCutValue_le_contractVia R hwf i h3

/-! ## The run invariant

`PickTracks` is what the loop maintains: the fibres of the live
vertices partition the original vertex set, and every cut of the
working graph flattens through `rep` to a cut of the original of the
same value. `init` and `step` show it holds at the start and survives
one fresh contraction; the bridges `isCut_rep` / `cutValue_rep` read
a genuine cut of the original off any live fibre at an end state;
`support_contractPick` packages everything a finished run guarantees,
on the whole support. -/

/-- The working graph `g` with representative map `rep` tracks `g₀`:
the fibres of the live vertices are pairwise-disjoint nonempty subsets
of `g₀.verts` covering all of it, and every cut of `g` flattens
through `rep` to a cut of `g₀` of the same value. -/
structure PickTracks (g₀ g : MultiGraph α) (rep : α → Finset α) : Prop where
  /-- Every fibre consists of original vertices. -/
  subset : ∀ x ∈ g.verts, rep x ⊆ g₀.verts
  /-- Every fibre is nonempty. -/
  nonempty : ∀ x ∈ g.verts, (rep x).Nonempty
  /-- The fibres of distinct live vertices are disjoint. -/
  disj : ∀ x ∈ g.verts, ∀ y ∈ g.verts, x ≠ y → Disjoint (rep x) (rep y)
  /-- Every original vertex sits in some live fibre. -/
  covers : ∀ a ∈ g₀.verts, ∃ x ∈ g.verts, a ∈ rep x
  /-- Cuts flatten with the same value. -/
  cut : ∀ 𝒮 ⊆ g.verts, g.cutValue 𝒮 = g₀.cutValue (𝒮.biUnion rep)

/-- The singleton assignment tracks the original graph. No `WF` needed. -/
lemma PickTracks.init (g : MultiGraph α) : PickTracks g g (fun a => {a}) where
  subset _ hx := Finset.singleton_subset_iff.mpr hx
  nonempty x _ := Finset.singleton_nonempty x
  disj _ _ _ _ hxy := Finset.disjoint_singleton.mpr hxy
  covers a ha := ⟨a, ha, Finset.mem_singleton_self a⟩
  cut 𝒮 _ := by rw [Finset.biUnion_singleton_eq_self]

/-- Tracking survives one contraction of a listed edge into a fresh
pick, with the fibre update. The pick may *be* an endpoint: the update
then overwrites that endpoint's fibre with the union, which is
correct; freshness only rules out collision with an untouched vertex. -/
lemma PickTracks.step {g₀ g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (ht : PickTracks g₀ g rep)
    {e : Sym2 α} (he : e ∈ g.edges)
    {w : α} (hfresh : w ∉ g.verts.filter (· ∉ e)) :
    PickTracks g₀ (g.contractEdgeTo e w) (updateRep rep e w) := by
  have hmem := hwf.incidence e he
  have hnd := hwf.loopless e he
  clear he
  revert hfresh hmem hnd
  induction e with
  | _ u v =>
    intro hfresh hmem hnd
    have hu := hmem u (Sym2.mem_mk_left u v)
    have hv := hmem v (Sym2.mem_mk_right u v)
    -- The freshness workhorse: every vertex surviving untouched
    -- differs from the pick.
    have hne : ∀ x ∈ g.verts, x ∉ s(u, v) → x ≠ w := by
      intro x hx hxe hxw
      exact hfresh (hxw ▸ Finset.mem_filter.mpr ⟨hx, hxe⟩)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [verts_contractEdgeTo] at hx
      rcases Finset.mem_insert.mp hx with rfl | hxf
      · rw [updateRep_self, repOf_mk]
        exact Finset.union_subset (ht.subset u hu) (ht.subset v hv)
      · obtain ⟨hxv, hxe⟩ := Finset.mem_filter.mp hxf
        rw [updateRep_of_ne rep _ (hne x hxv hxe)]
        exact ht.subset x hxv
    · intro x hx
      rw [verts_contractEdgeTo] at hx
      rcases Finset.mem_insert.mp hx with rfl | hxf
      · rw [updateRep_self, repOf_mk]
        exact (ht.nonempty u hu).mono Finset.subset_union_left
      · obtain ⟨hxv, hxe⟩ := Finset.mem_filter.mp hxf
        rw [updateRep_of_ne rep _ (hne x hxv hxe)]
        exact ht.nonempty x hxv
    · intro x hx y hy hxy
      rw [verts_contractEdgeTo] at hx hy
      rcases Finset.mem_insert.mp hx with rfl | hxf
      · rcases Finset.mem_insert.mp hy with rfl | hyf
        · exact absurd rfl hxy
        · obtain ⟨hyv, hye⟩ := Finset.mem_filter.mp hyf
          rw [updateRep_self, repOf_mk,
            updateRep_of_ne rep _ (hne y hyv hye),
            Finset.disjoint_union_left]
          exact ⟨ht.disj u hu y hyv fun h => hye (h ▸ Sym2.mem_mk_left u v),
            ht.disj v hv y hyv fun h => hye (h ▸ Sym2.mem_mk_right u v)⟩
      · obtain ⟨hxv, hxe⟩ := Finset.mem_filter.mp hxf
        rcases Finset.mem_insert.mp hy with rfl | hyf
        · rw [updateRep_of_ne rep _ (hne x hxv hxe), updateRep_self,
            repOf_mk, Finset.disjoint_union_right]
          exact ⟨ht.disj x hxv u hu fun h => hxe (h ▸ Sym2.mem_mk_left u v),
            ht.disj x hxv v hv fun h => hxe (h ▸ Sym2.mem_mk_right u v)⟩
        · obtain ⟨hyv, hye⟩ := Finset.mem_filter.mp hyf
          rw [updateRep_of_ne rep _ (hne x hxv hxe),
            updateRep_of_ne rep _ (hne y hyv hye)]
          exact ht.disj x hxv y hyv hxy
    · intro a ha
      obtain ⟨x, hx, hax⟩ := ht.covers a ha
      by_cases hxe : x ∈ s(u, v)
      · refine ⟨w, Finset.mem_insert_self .., ?_⟩
        rw [updateRep_self, repOf_mk]
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact Finset.mem_union_left _ hax
        · exact Finset.mem_union_right _ hax
      · refine ⟨x, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, hxe⟩), ?_⟩
        rw [updateRep_of_ne rep _ (hne x hx hxe)]
        exact hax
    · intro 𝒮' h𝒮'
      rw [cutValue_contractEdgeTo_of_pointwise
          (S := g.verts.filter (redirectTo s(u, v) w · ∈ 𝒮')) hwf
          (fun x hx => by simp [Finset.mem_filter, hx]),
        ht.cut _ (Finset.filter_subset _ _)]
      congr 1
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨hxv, hx𝒮'⟩, hax⟩
        by_cases hxe : x ∈ s(u, v)
        · rw [redirectTo, if_pos hxe] at hx𝒮'
          refine ⟨w, hx𝒮', ?_⟩
          rw [updateRep_self, repOf_mk]
          rcases Sym2.mem_iff.mp hxe with rfl | rfl
          · exact Finset.mem_union_left _ hax
          · exact Finset.mem_union_right _ hax
        · rw [redirectTo, if_neg hxe] at hx𝒮'
          exact ⟨x, hx𝒮',
            by rw [updateRep_of_ne rep _ (hne x hxv hxe)]; exact hax⟩
      · rintro ⟨y, hy𝒮', hay⟩
        have hyv' := h𝒮' hy𝒮'
        rw [verts_contractEdgeTo] at hyv'
        rcases Finset.mem_insert.mp hyv' with rfl | hyf
        · rw [updateRep_self, repOf_mk] at hay
          rcases Finset.mem_union.mp hay with ha' | ha'
          · exact ⟨u, ⟨hu, by
              rw [redirectTo, if_pos (Sym2.mem_mk_left u v)]; exact hy𝒮'⟩, ha'⟩
          · exact ⟨v, ⟨hv, by
              rw [redirectTo, if_pos (Sym2.mem_mk_right u v)]; exact hy𝒮'⟩, ha'⟩
        · obtain ⟨hyv, hye⟩ := Finset.mem_filter.mp hyf
          refine ⟨y, ⟨hyv, by rw [redirectTo, if_neg hye]; exact hy𝒮'⟩, ?_⟩
          rw [updateRep_of_ne rep _ (hne y hyv hye)] at hay
          exact hay

/-- Every live fibre is a genuine cut of the tracked graph. -/
lemma PickTracks.isCut_rep {g₀ g : MultiGraph α} {rep : α → Finset α}
    (ht : PickTracks g₀ g rep) (h2 : 2 ≤ g.verts.card)
    {x : α} (hx : x ∈ g.verts) : g₀.IsCut (rep x) := by
  refine ⟨ht.subset x hx, ht.nonempty x hx, ?_⟩
  obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne
    (show 1 < g.verts.card by omega) x
  obtain ⟨b, hb⟩ := ht.nonempty y hy
  exact ⟨b, ht.subset y hy hb,
    fun hbx => Finset.disjoint_left.mp (ht.disj y hy x hx hyx) hb hbx⟩

/-- The bridge: at an end state (two vertices remain, or no edges do)
every live fibre cuts the tracked graph with value exactly the number
of surviving edges. -/
lemma PickTracks.cutValue_rep {g₀ g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (ht : PickTracks g₀ g rep)
    (hend : g.verts.card = 2 ∨ g.edges = [])
    {x : α} (hx : x ∈ g.verts) : g₀.cutValue (rep x) = g.edges.length := by
  have h1 := ht.cut {x} (Finset.singleton_subset_iff.mpr hx)
  rw [Finset.singleton_biUnion] at h1
  rw [← h1]
  rcases hend with hcard | hnil
  · refine cutValue_of_card_two hwf hcard
      ⟨Finset.singleton_subset_iff.mpr hx, Finset.singleton_nonempty x, ?_⟩
    obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne
      (show 1 < g.verts.card by omega) x
    exact ⟨y, hy, by simp [hyx]⟩
  · simp [cutValue, hnil]

/-- The run invariant of the pick loop, for an arbitrary stopping
target `t` (Karger stops at `t = 2`; Karger–Stein at `t = ksTarget n`):
well-formedness, the card window, a genuine end state, monotonicity of
the edge count and of the minimum-cut value, and tracking. Fuel-free,
so no card arithmetic is threaded: freshness makes the card drop by
exactly one per step, which keeps `t ≤ card` across the guard. `2 ≤ t`
protects the minimum-cut value: a contraction at two vertices could
destroy the last cut. -/
theorem support_contractPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (R : MergeRule α) (g₀ : MultiGraph α) (t : ℕ) (ht2 : 2 ≤ t) :
    ∀ (g : MultiGraph α) (rep : α → Finset α),
      g.WF → t ≤ g.verts.card → PickTracks g₀ g rep →
      ∀ p ∈ 𝒟_{M}[contractPick R.pick t g rep].support,
        p.1.WF ∧ t ≤ p.1.verts.card ∧ p.1.verts.card ≤ g.verts.card ∧
          (p.1.verts.card = t ∨ p.1.edges = []) ∧
          p.1.edges.length ≤ g.edges.length ∧
          g.minCutValue ≤ p.1.minCutValue ∧
          PickTracks g₀ p.1 p.2 := by
  intro g rep
  induction g, rep using contractPick.induct (pick := R.pick) (t := t) with
  | case1 g rep h ih =>
    intro hwf hcard ht p hp
    rw [contractPick, dif_pos h] at hp
    toPMF_step at hp
    obtain ⟨i, -, hi⟩ := hp
    have hcard' := card_verts_contractAt R hwf i
    have ht' : PickTracks g₀ (contractAt R.pick g i)
        (updateRep rep g.edges[(i : ℕ)] (R.pick g g.edges[(i : ℕ)])) :=
      ht.step hwf (List.getElem_mem _) (R.fresh hwf (List.getElem_mem _))
    obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ :=
      ih i (hwf.contractAt R.pick i) (by omega) ht' p hi
    exact ⟨h1, h2', by omega, h4,
      le_trans h5 (length_edges_contractAt_lt R.pick g i).le,
      le_trans (minCutValue_le_contractAt R hwf i (by omega)) h6, h7⟩
  | case2 g rep h =>
    intro hwf hcard ht p hp
    rw [contractPick, dif_neg h] at hp
    toPMF_step at hp
    subst hp
    have hend : g.verts.card = t ∨ g.edges = [] := by
      rw [← List.length_eq_zero_iff]
      omega
    exact ⟨hwf, hcard, le_rfl, hend, le_rfl, le_rfl, ht⟩

/-! ## Survival of the minimum cut

The proof is Karger's: fix a minimum cut, count its crossing edges,
contract a non-crossing one. Only the per-step transport lemma
(`minCutValue_contractEdgeTo_of_notCrossing`) touches the contraction
model, and freshness feeds it. The loop being fuel-free, no fuel/card
equation is threaded: inside the guard the card is `k + s + 3` for
some `k`, and the guard-false leaves succeed with certainty — there
`s + 2 ≤ card` turns probability one into the stated bound. -/

/-- Survival of the minimum cut through the loop stopped at `s + 2`
vertices: the working graph still realizes the original minimum-cut
value with probability at least `(s+2)(s+1) / (n (n − 1))`. Karger is
the case `s = 0`; Karger–Stein recurses on `s + 2 = ksTarget n`, where
the bound is `≥ 1/2`. -/
theorem success_contractPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (R : MergeRule α) (s : ℕ) :
    ∀ (g : MultiGraph α) (rep : α → Finset α), g.WF →
      s + 2 ≤ g.verts.card →
      (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
          ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
        ℙ_{M}[contractPick R.pick (s + 2) g rep ∈
          {p | p.1.minCutValue = g.minCutValue}] := by
  intro g rep
  induction g, rep using contractPick.induct (pick := R.pick) (t := s + 2) with
  | case1 g rep h ih =>
    intro hwf h2
    obtain ⟨k, hk⟩ : ∃ k, g.verts.card = k + (s + 3) :=
      ⟨g.verts.card - (s + 3), by omega⟩
    -- Main case: pick a uniform edge, recurse.
    rw [contractPick, dif_pos h, toPMF_tick_bind, prob_toPMF_randIdx_bind]
    -- Fix a minimum cut `S`.
    obtain ⟨S, hS, hSval⟩ := exists_minCut g (by omega)
    -- The branch success probability as a function of the contracted edge.
    set F : Sym2 α → ℝ≥0∞ := fun e =>
      prob (inst.toPMF (contractPick R.pick (s + 2)
          (g.contractEdgeTo e (R.pick g e))
          (updateRep rep e (R.pick g e)) : M _))
        {p | p.1.minCutValue = g.minCutValue} with hF
    have hsum : (∑ i : Fin g.edges.length,
        prob (inst.toPMF (contractPick R.pick (s + 2) (contractAt R.pick g i)
            (updateRep rep g.edges[(i : ℕ)] (R.pick g g.edges[(i : ℕ)])) : M _))
          {p | p.1.minCutValue = g.minCutValue}) = (g.edges.map F).sum := by
      rw [← sum_univ_getElem g.edges F]
      rfl
    rw [hsum]
    -- Every non-crossing edge contributes at least the recursive bound.
    have hbranch : ∀ e ∈ g.edges,
        (if Crossing S e then 0 else
          (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
            (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞)) ≤ F e := by
      intro e he
      by_cases hcr : Crossing S e
      · simp [hcr]
      · rw [if_neg hcr, hF]
        obtain ⟨i, hilen, rfl⟩ := List.getElem_of_mem he
        have hcard' : (contractAt R.pick g ⟨i, hilen⟩).verts.card
            = k + (s + 2) := by
          have := card_verts_contractAt R hwf ⟨i, hilen⟩
          omega
        rw [← minCutValue_contractEdgeTo_of_notCrossing hwf
          (R.fresh hwf he) (hwf.incidence _ he) (hwf.loopless _ he)
          (by omega) hS hSval hcr]
        have hih := ih ⟨i, hilen⟩ (hwf.contractAt R.pick ⟨i, hilen⟩) (by omega)
        rw [hcard', show k + (s + 2) - 1 = k + s + 1 by omega,
          show k + (s + 2) = k + s + 2 by omega] at hih
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
    rw [hSval, hk, show k + (s + 3) - 1 = k + s + 2 by omega,
      show ((k + (s + 3)) * (k + s + 2) : ℕ) = ((k + s + 3) * (k + s + 2) : ℕ)
        by ring]
    -- Arithmetic: the counting bound closes the step.
    have hc_le : g.minCutValue ≤ g.edges.length :=
      minCutValue_le_length g (by omega)
    have hbound : g.minCutValue * (k + s + 3) ≤ 2 * g.edges.length := by
      have := card_mul_minCutValue_le g hwf (by omega)
      rw [hk] at this
      calc g.minCutValue * (k + s + 3)
          = (k + (s + 3)) * g.minCutValue := by ring
        _ ≤ 2 * g.edges.length := this
    exact step_bound (N := (s + 2) * (s + 1)) (k := k) (s := s) h.2 hc_le hbound
  | case2 g rep h =>
    intro hwf h2
    -- The guard failed: the graph is unchanged, success with probability `1`.
    rw [contractPick, dif_neg h, inst.toPMF_pure, pmf_pure_eq]
    refine le_trans (ENNReal.div_le_of_le_mul' ?_)
      (ge_of_eq (prob_pure_of_mem rfl))
    rw [mul_one]
    exact_mod_cast Nat.mul_le_mul (by omega : s + 2 ≤ g.verts.card)
      (by omega : s + 1 ≤ g.verts.card - 1)

/-! ## Karger's theorem

The *body* of `Karger` is everything after the singleton
initialisation: the loop at target `2`, then the readout.
`support_kargerBody` and `success_kargerBody` state what it
guarantees on any tracked pair; `Karger` consumes them on the
singleton fibres, Karger–Stein's leaves on their working
pairs. `karger_isCut` is the cut-level one-sided error, read off the
run invariant; `karger_success_prob` is the value-level survival
bound; `karger_finds_min` strengthens it to the textbook statement
along the support, not by re-induction. -/

/-- Everything a finished run of Karger's body guarantees on a
tracked pair, unconditionally: every reported side is a genuine cut
of the tracked graph of value exactly the reported number, and that
number undershoots neither minimum. Needs `fresh` (a `MergeRule`),
where the algorithm itself needed only `pick`. -/
theorem support_kargerBody
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    (R : MergeRule α) {g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (ht : PickTracks g₀ g rep) :
    ∀ o ∈ 𝒟_{M}[(contractPick R.pick 2 g rep >>= fun q =>
        pure (q.1.verts.image q.2, q.1.edges.length) :
          M (Finset (Finset α) × ℕ))].support,
      (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
        g₀.minCutValue ≤ o.2 ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  obtain ⟨q, hq, rfl⟩ := mem_support_toPMF_bind_pure.mp ho
  obtain ⟨hwf', h2', -, hend, -, hmin, ht'⟩ :=
    support_contractPick (M := M) R g₀ 2 le_rfl g rep hwf h2 ht q hq
  refine ⟨fun S hS => ?_, ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨ht'.isCut_rep h2' hx, ht'.cutValue_rep hwf' hend hx⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < q.1.verts.card)
    rw [← ht'.cutValue_rep hwf' hend hx]
    exact minCutValue_le (ht'.isCut_rep h2' hx)
  · exact le_trans hmin (minCutValue_le_length q.1 h2')

/-- Everything a single run guarantees, unconditionally: every reported
side is a genuine cut of `g` of value exactly the reported number, and
that number never undershoots the minimum. -/
theorem karger_isCut
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟_{M}[Karger R.pick g].support,
      (∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2) ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  unfold Karger at ho
  obtain ⟨hcut, hmin, -⟩ :=
    support_kargerBody R hwf h2 (PickTracks.init g) o ho
  exact ⟨hcut, hmin⟩

/-- The value-level survival bound for Karger's body on a tracked
pair: the reported number is the *current* minimum-cut value with
probability at least `2 / (n (n − 1))`. -/
theorem success_kargerBody
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    (R : MergeRule α) {g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (ht : PickTracks g₀ g rep) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[(contractPick R.pick 2 g rep >>= fun q =>
          pure (q.1.verts.image q.2, q.1.edges.length) :
            M (Finset (Finset α) × ℕ)) ∈ {o | o.2 = g.minCutValue}] := by
  have hmain : (2 : ℝ≥0∞) /
      ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[contractPick R.pick 2 g rep ∈
        {p | p.1.minCutValue = g.minCutValue}] := by
    simpa using success_contractPick (M := M) R (s := 0) g rep hwf (by omega)
  rw [bind_pure_comp, LawfulRandMonad.toPMF_map, pmf_map_eq, prob_map]
  refine le_trans hmain (prob_mono_of_support fun q hq hev => ?_)
  obtain ⟨hwf', h2', -, hend, -, -, -⟩ :=
    support_contractPick (M := M) R g₀ 2 le_rfl g rep hwf h2 ht q hq
  show q.1.edges.length = g.minCutValue
  rcases hend with hcard2 | hnil
  · exact (length_eq_minCutValue_of_card_two hwf' hcard2).trans hev
  · have hlen : q.1.edges.length = 0 := by rw [hnil]; rfl
    have hmin0 : q.1.minCutValue = 0 :=
      Nat.le_zero.mp (le_trans (minCutValue_le_length q.1 h2') (le_of_eq hlen))
    rw [hlen, ← hev, hmin0]

/-- A single run *reports the minimum-cut value* with probability at
least `2 / (n (n - 1))`, the value-level bound the induction proves;
`karger_finds_min` below is its cut-level (textbook) form. -/
theorem karger_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[Karger R.pick g ∈ {o | o.2 = g.minCutValue}] :=
  success_kargerBody R hwf h2 (PickTracks.init g)

/-- Karger's theorem, pick-abstract and cut-level. A single run
returns an actual minimum cut (every reported side is a genuine cut of
`g` of value exactly `minCutValue`) with probability at least
`2 / (n (n − 1))`. Obtained from the value-level bound by
strengthening the event along the run's support invariant
(`karger_isCut`), not by re-induction. -/
theorem karger_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[Karger R.pick g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] := by
  refine le_trans (karger_success_prob R g hwf h2)
    (prob_mono_of_support fun o ho hval => ?_)
  obtain ⟨hall, -⟩ := karger_isCut R g hwf h2 o ho
  exact fun S hS => ⟨(hall S hS).1, (hall S hS).2.trans hval⟩

/-! ## Complexity

Each contraction round ticks `m'`, the current number of edges: the
contraction pass relabels and filters the whole edge list. Since
contraction never adds edges, every round costs at most `m` and the
loop stopped at `t` runs at most `n − t` rounds, giving expected cost
at most `(n − t) m`; Karger reads it at `t = 2`. The round count is
derived, not declared — the fuel-free trade of the module docstring —
so the bounds here need `WF` and freshness. -/

/-- Expected cost of the pick loop stopped at `t` vertices: at most
`(n − t) m`. -/
lemma expected_cost_contractPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (R : MergeRule α) (t : ℕ) :
    ∀ (g : MultiGraph α) (rep : α → Finset α), g.WF →
      𝔼_{M}[cost (contractPick R.pick t g rep :
          TimeMT ℕ M (MultiGraph α × (α → Finset α)))] ≤
        ((g.verts.card - t : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  intro g rep
  induction g, rep using contractPick.induct (pick := R.pick) (t := t) with
  | case1 g rep h ih =>
    intro hwf
    rw [contractPick, dif_pos h, MonadCost.tick_timeMT,
      expected_cost_toPMF_tick_bind, expected_cost_uniform_step]
    -- Each branch starts from one fewer vertex and at most `m` edges,
    -- so the uniform average of the branch costs is at most
    -- `(n - (t + 1)) m`.
    have hbranch : ∀ i : Fin g.edges.length,
        𝔼_{M}[cost (contractPick R.pick t (contractAt R.pick g i)
            (updateRep rep g.edges[(i : ℕ)] (R.pick g g.edges[(i : ℕ)])) :
          TimeMT ℕ M (MultiGraph α × (α → Finset α)))] ≤
        ((g.verts.card - (t + 1) : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
      intro i
      have hcard := card_verts_contractAt R hwf i
      exact le_trans (ih i (hwf.contractAt R.pick i))
        (mul_le_mul' (Nat.cast_le.mpr (by omega))
          (Nat.cast_le.mpr (length_edges_contractAt_lt R.pick g i).le))
    refine le_trans (add_le_add le_rfl
      (uniform_avg_le_of_forall hbranch h.2.ne')) ?_
    rw [show ((g.verts.card - t : ℕ) : ℝ≥0∞)
        = ((g.verts.card - (t + 1) : ℕ) : ℝ≥0∞) + 1 by
      exact_mod_cast (by omega : g.verts.card - t = g.verts.card - (t + 1) + 1)]
    rw [add_mul, one_mul, add_comm]
  | case2 g rep h =>
    intro _
    rw [contractPick, dif_neg h, expected_cost_toPMF_pure]
    exact bot_le

/-- Expected complexity of Karger's algorithm with an abstract pick.
With one tick per edge scanned during a contraction pass, a run on a
well-formed graph with `n` vertices and `m` edges costs at most
`(n - 2) * m` in expectation, the fuel-free counterpart of
`kargerVia_cost_le`. -/
theorem karger_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost Karger R.pick g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  unfold Karger
  rw [expected_cost_toPMF_bind_pure]
  exact expected_cost_contractPick R 2 g _ hwf

/-- Finiteness of the expected cost, a free corollary of the
`(n - 2) m` bound. -/
lemma expected_cost_karger_ne_top
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost Karger R.pick g] ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le R g hwf)

/-- Real-valued corollary: the expected cost is at most `(n - 2) * m`. -/
theorem karger_cost_le_real
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) :
    𝔼ℝ_{M}[cost Karger R.pick g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ) * (g.edges.length : ℝ) := by
  have := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le (M := M) R g hwf)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
  exact this

/-! ## Amplification: repetition finds the minimum cut

A single run succeeds with probability only `Ω(1/n²)`, but the
algorithm is one-sided (the reported value never undershoots), so
keeping the best output over independent runs succeeds as soon as any
single run does. The generic `amplify` combinator turns this into a
theorem. -/

/-- Amplified `Karger`. Run the algorithm `k` times and keep the
output of smallest reported value: the result reports the minimum-cut
value with probability at least `1 − (1 − 2/(n(n−1)))^k`, so
`O(n² log n)` repetitions find a minimum cut with high probability.
Selecting by the reported value (`argmin Prod.snd`) costs nothing:
the run already computed it. -/
theorem karger_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card)
    (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify (argmin Prod.snd) k (Karger R.pick g)
          ∈ {o | o.2 = g.minCutValue}] :=
  amplify_argmin_success
    (fun o ho => (karger_isCut R g hwf h2 o ho).2)
    (karger_success_prob R g hwf h2) k

/-- Amplified cost: `k + 1` runs cost at most `k + 1` times the
single-run bound `(n − 2) m`. -/
theorem karger_amplified_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (R : MergeRule α) (g : MultiGraph α) (hwf : g.WF) (k : ℕ) :
    𝔼_{M}[cost amplify (argmin Prod.snd) (k + 1) (Karger R.pick g)] ≤
      (k + 1 : ℝ≥0∞) *
        (((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
  rw [expected_cost_amplify]
  exact mul_le_mul' le_rfl (karger_cost_le R g hwf)

/-! ## The rename models, upgraded to cut-level

The payoff of the abstraction. Each rename model of
`KargerVariants.lean` — order, enumeration, fresh names — inherits
the cut-level theorems by instantiating `R`; each proof is one line.
Compare the value-level shadow (`kargerVia_success_prob`),
which could state only the value. -/

/-- The order model finds an actual minimum cut — the statement its
value-level shadow (`kargerVia_success_prob`) could not make. -/
theorem kargerOrder_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [LinearOrder α]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerOrder g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] :=
  karger_finds_min orderRule g hwf h2

/-- Expected cost at most `(n - 2) * m`, one tick per edge scanned. -/
theorem kargerOrder_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] [LinearOrder α]
    (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost KargerOrder g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  karger_cost_le orderRule g hwf

/-- Keeping the output of smallest value over `k` runs succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerOrder_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] [LinearOrder α]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify (argmin Prod.snd) k (KargerOrder g)
          ∈ {o | o.2 = g.minCutValue}] :=
  karger_amplified orderRule g hwf h2 k

/-- The enumeration model finds an actual minimum cut, with a bound
that does not depend on `ℓ`, though the statement must mention it. -/
theorem kargerEnum_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerEnum ℓ g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] :=
  karger_finds_min (enumRule ℓ) g hwf h2

/-- Expected cost at most `(n - 2) * m`, one tick per edge scanned. -/
theorem kargerEnum_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost KargerEnum ℓ g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  karger_cost_le (enumRule ℓ) g hwf

/-- Keeping the output of smallest value over `k` runs succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerEnum_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify (argmin Prod.snd) k (KargerEnum ℓ g)
          ∈ {o | o.2 = g.minCutValue}] :=
  karger_amplified (enumRule ℓ) g hwf h2 k

/-- The fresh-name model finds an actual minimum cut. -/
theorem kargerFresh_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph ℕ) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerFresh g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] :=
  karger_finds_min freshRule g hwf h2

/-- Expected cost at most `(n - 2) * m`, one tick per edge scanned. -/
theorem kargerFresh_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph ℕ) (hwf : g.WF) :
    𝔼_{M}[cost KargerFresh g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  karger_cost_le freshRule g hwf

/-- Keeping the output of smallest value over `k` runs succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerFresh_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph ℕ) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify (argmin Prod.snd) k (KargerFresh g)
          ∈ {o | o.2 = g.minCutValue}] :=
  karger_amplified freshRule g hwf h2 k

end ARA
