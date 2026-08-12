/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Correctness.Amplify
import ARA.Helpers.MultiGraph

/-!
# Karger algorithm

As everywhere in ARA, the algorithm is written once against
`RandMonad` and `MonadCost ℕ`, and read at `M = IO` (run it),
`M = PMF` (its law), and `M = TimeMT ℕ M'` (timed).

## Note:

A question arises from the graph representation, more precisely from
the implementation of the edge collection, which is mathematically a
set:

- GraphLib stores labeled edges in a `Set`;
- our `MultiGraph` carries a `List (Sym2 α)` instead.

Why? First because Karger needs multiplicity and a list carries it: a
`List (Sym2 α)` seems a simple way to record it. Second, even if
you find a way to record multiplicity with a `Finset`, you must (because
Karger is a randomized algorithm) draw a random edge, and drawing
uniformly from a `Finset` is hard the moment the draw must execute
(`M=IO`). Indeed:

A uniform element of a finite set is well-defined as a distribution:
`PMF.uniformOfFinset` exists, with no order and no choice, because
uniformity is exactly the distribution that does not depend on how the
set is enumerated. Great.

However, it is not well-defined as a program. A `Finset` is a quotient
of lists by permutation, and a function out of a quotient must be invariant
under the relation. A program that draws from `{a, b}` cannot be: at `M = IO`,
drawing from `[a, b]` and drawing from `[b, a]` are _different_
programs. Only the output law of the draw is permutation-invariant,
which is why the object exists at `M = PMF` and cannot exist
polymorphically in `M`.

Said differently: a program can only point at an address, so
sampling needs an ID on the elements, an arbitrary identifier that
breaks the symmetry of `Finset`.

Here, we thought about three ways around this:

* Convert the finset to a list, then draw: `Finset.toList` is
  `Quotient.out`, noncomputable, so the `IO` reading dies;

* Use a linear order: `Finset.sort` is computable, but now `[LinearOrder α]`
  is a (weird) assumption the min-cut problem never mentions;

* Read the runtime representative. At runtime the quotient (the `Finset`)
  does not exist: what sits in memory is literally a list, in whatever
  order the program built it, and the `unsafe` function `Quot.unquot`
  reads it. It is quarantined as `unsafe` because it distinguishes equal
  things: `{1, 2} = {2, 1}` as Finsets, yet it may return `[1, 2]` for
  one and `[2, 1]` for the other, and a function separating equal inputs
  proves `False`. To get around this we can write `@[implemented_by]`,
  which declares an `opaque` logical constant and tells the compiler to
  run the unsafe function in its place. The type checker reasons about
  one function, the compiled program runs another, and nothing checks
  that they agree. Every theorem would then be about the thing that
  does not run. And unlike the `tick`s, which someone can audits by
  reading the algorithm, this trust is invisible in the text: you would
  have to open the instance to know it is there.

We took none of them and stayed with our primitive, `randFin n` with
the derived `randIdx`, for which a list seems a reasonable carrier: the
ID of the elements is declared once, in the input, rather than conjured
at every draw. Whether that is the best answer we do not know; it is
the one that let all four readings survive.


## Main results

For `n` the number of vertices and `m` the number of edges (with
multiplicity), we have:

* `karger_finds_min`: a single run returns an actual minimum cut
  with probability at least `2 / (n (n - 1))`, for every pick
  satisfying `Fresh`.
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
The concrete picks (order, labelling, fresh names) and the
value-level analysis under a bundled `MergeRule` live in
`DesignDiscussion/`; this file depends only on `Infrastructure` and
`Helpers`.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-! ## Algorithm -/

/-
In a contraction the two endpoints of the drawn edge leave and one
new vertex `w` (that must be of the same type) enters. Someone has to
produce such `w`. This is taken care of by abstracting over a function
`pick : MultiGraph α → Sym2 α → α`.
-/

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

/-- `contractAt` strictly drops the edge count. -/
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

/-- Freshness of a pick function: the merged vertex collides with no
untouched vertex. -/
def Fresh (pick : MultiGraph α → Sym2 α → α) : Prop :=
  ∀ ⦃g : MultiGraph α⦄ ⦃e : Sym2 α⦄, g.WF → e ∈ g.edges →
    pick g e ∉ g.verts.filter (· ∉ e)

/-
In order to report a cut in Karger algorithm, we update at each
step a set that will become the cut at the end. Informally, this
is done by updating a function `rep : α → Finset α`. At the end we
want to have an updated `rep : α → Finset α` that should send each
live vertex to the set of original vertices merged into it. It starts at
singletons, and when `e` is contracted into `w` the fibre of `w`
becomes the union of the two endpoint fibres. When the loop stops,
the fibres of the survivors are the sides of the cut.
-/

/-- The fibre of the drawn edge: the union of its endpoints' fibres,
lifted through `Sym2`. -/
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
the pick, while `t + 1 ≤ verts.card ∧ 0 < edges.length`. `t` is abstracted
for future needs: Karger runs with `t = 2` but for example
Karger–Stein runs `t = ksTarget n`. It terminates since the edge count
drops strictly at each step. Ticks once per scanned edge. -/
def contractPick {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) (t : ℕ)
    (g : MultiGraph α) (rep : α → Finset α) :
    M (MultiGraph α × (α → Finset α)) :=
  -- keep contracting while an edge remains; stop at `t` vertices, at
  -- `t = 2` one step before the cut would disappear
  if h : t + 1 ≤ g.verts.card ∧ 0 < g.edges.length then do
    -- costs one tick per edge: contracting walks the whole
    -- list to redirect it and drop the loops
    MonadCost.tick g.edges.length
    -- a uniform position in the list is an edge drawn with probability
    -- proportional to its multiplicity
    let i ← randIdx g.edges h.2
    -- contract the drawn edge into the picked vertex, and record the
    -- merge (by updating the report function): the pick's fibre
    -- becomes the union of the endpoint previous fibres
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
    -- t = 2 and the report function is a => {a}
  let p ← contractPick pick 2 g (fun a => {a})
  pure (p.1.verts.image p.2, p.1.edges.length)

/-! ## Instances and demos

Any `pick : MultiGraph α → Sym2 α → α` runs the algorithm, but in order
to guarantee correctness of the output (a cut, with its value) we need
it to choose a vertex that no untouched vertex already occupies, i.e.
to satisfy the `Fresh` definition. One can still run the algorithm
without that assumption, which is why it is the hypothesis of every
theorem below and of none of the definitions above.

A discussion of the possible picks (order, labelling, fresh names,
union), and of what each one seems to cost, lives in
`DesignDiscussion/KargerVariants.lean`. -/

/-- A demo pick on `ℕ`: merge into one past the largest live vertex.
It is fresh, the new name exceeding every vertex present. -/
def demoPick : MultiGraph ℕ → Sym2 ℕ → ℕ := fun g _ => g.verts.sup id + 1

/-- `demoPick` is fresh: its value exceeds every live vertex, so it
collides with none of them, untouched or not. -/
lemma demoPick_is_Fresh : Fresh demoPick := by
  intro g e _ _ h
  -- the pick landed on a live vertex, so it is bounded by the sup
  have := Finset.le_sup (f := id) (Finset.mem_filter.mp h).1
  simp only [id_eq, demoPick] at this
  omega

/-- Two triangles joined by one bridge. The minimum cut is the bridge
`s(2, 3)`, of value `1`; every other cut has value at least `2`.

```
       *0                      *5
      /  \                    /  \
     /    \                  /    \
   *1 ---- *2 ------------ *3 ---- *4
                 bridge
```
Outputs below are random: the sides and the value vary from run to
run, and a run finds the bridge only sometimes. -/
def demoGraph : MultiGraph ℕ where
  verts := {0, 1, 2, 3, 4, 5}
  edges := [s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3), s(2, 3)]

-- IO reading (executable, untimed); e.g. `({{0, 1, 2}, {3, 4, 5}}, 1)`
#eval (Karger demoPick demoGraph : IO (Finset (Finset ℕ) × ℕ))

-- PMF reading (noncomputable specification)
noncomputable example : PMF (Finset (Finset ℕ) × ℕ) :=
  Karger demoPick demoGraph

-- timed IO reading; e.g. `{ ret := ({{0, 1}, {2, 3, 4, 5}}, 2), time := 20 }`
#eval (Karger demoPick demoGraph : TimeMT ℕ IO _).run

-- timed PMF reading: the joint law of (output, cost)
noncomputable example : TimeMT ℕ PMF (Finset (Finset ℕ) × ℕ) :=
  Karger demoPick demoGraph

/-! ## Helper lemmas for the analysis

The two fresh-only step facts: a fresh contraction loses exactly one
vertex (`card_verts_contractAt`) and never drops the minimum-cut value
(`minCutValue_le_contractAt`). Note the signatures: `contractAt` takes
a bare pick, these two take `Fresh pick`.

Then two counting facts, about lists and arithmetic. Both are the
plumbing of `success_contractPick`, the survival induction, and both
are `private` for that reason. `sum_map_ite_zero` sums what the edges
contribute when the crossing ones contribute nothing, and `step_bound`
turns that sum into the bound one vertex up. -/

/-- Freshness makes the contraction lose exactly one vertex. -/
lemma card_verts_contractAt {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) {g : MultiGraph α}
    (hwf : g.WF) (i : Fin g.edges.length) :
    (contractAt pick g i).verts.card + 1 = g.verts.card :=
  card_verts_contractEdgeTo (hfresh hwf (List.getElem_mem _))
    (hwf.incidence _ (List.getElem_mem _)) (hwf.loopless _ (List.getElem_mem _))

/-- The minimum-cut value never drops under a fresh contraction. -/
lemma minCutValue_le_contractAt {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) {g : MultiGraph α}
    (hwf : g.WF) (i : Fin g.edges.length) (h3 : 3 ≤ g.verts.card) :
    g.minCutValue ≤ (contractAt pick g i).minCutValue :=
  minCutValue_le_contractEdgeTo hwf (hfresh hwf (List.getElem_mem _))
    (hwf.incidence _ (List.getElem_mem _)) (hwf.loopless _ (List.getElem_mem _))
    h3

/-- Each element contributes `q`, except those satisfying `p`, which
contribute nothing. The total is then `(length − #p) · q`.

We use it in `success_contractPick`, while proving that the minimum cut
survives the loop. There a minimum cut `S` is fixed, and every edge of
the current graph is given a lower bound on its branch probability:
contracting an edge that crosses `S` destroys `S`, so those branches
get the bound `0`, while contracting an edge that misses `S` keeps `S`
minimum, so those get the induction hypothesis, one vertex down.
Summing that list is what this lemma does, taking for `p` the property
of crossing `S`. The count `#p` is then the number of crossing edges,
which is the value `c` of the cut, so each of the `m − c` edges that
miss `S` earns the recursive bound `q` and the total is `(m − c) · q`.

Proved by induction on the list.

Mathlib seems to have no equivalent (checked with `exact?`).
-/
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

/-- The arithmetic of the induction step. The names come from
`success_contractPick`, its only caller: the loop stops at `s + 2`
vertices, and `k` counts how far the current graph still is from that
target, so it has `n = k + s + 3` vertices and one contraction takes
it to `k + s + 2`. Read `m` as its edge count, `c` as its minimum-cut
value, and `hbound` as the handshake bound `n · c ≤ 2m` at that `n`.

A uniform draw then misses the fixed minimum cut with probability
`(m − c)/m`, and multiplying that by the bound at `k + s + 2` vertices
has to give the bound at `k + s + 3`, which is exactly the inequality
below. The numerator `N` is `(s + 2)(s + 1)`, carried unchanged by the
induction, so it is left abstract here. Proved by clearing denominators
and closing in `ℕ`. -/
private lemma step_bound {m c k s N : ℕ} (hm : 0 < m) (hc : c ≤ m)
    (hbound : c * (k + s + 3) ≤ 2 * m) :
    ((N : ℕ) : ℝ≥0∞) / (((k + s + 3) * (k + s + 2) : ℕ) : ℝ≥0∞) ≤
      ((m : ℕ) : ℝ≥0∞)⁻¹ *
        (((m - c : ℕ) : ℝ≥0∞) *
          (((N : ℕ) : ℝ≥0∞) / (((k + s + 2) * (k + s + 1) : ℕ) : ℝ≥0∞))) := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + c := ⟨m - c, by omega⟩
  rw [Nat.add_sub_cancel]
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
  nlinarith [Nat.mul_le_mul_left (N * (k + s + 2)) hkey]

/-! ## The run invariant

`PickTracks` is what the loop maintains: the fibres of the live
vertices partition the original vertex set, and every cut of the
working graph flattens through `rep` to a cut of the original of the
same value. `init` and `step` show it holds at the start and survives
one fresh contraction; the bridges `isCut_rep` / `cutValue_rep` read
a genuine cut of the original off any live fibre at an end state;
`support_contractPick` packages what a finished run guarantees, on the
whole support. The invariant does not mention the loop, so we hope any
algorithm contracting listed edges into fresh picks can start it with
`init` and carry it with `step`; that was at least enough for
Karger–Stein. In the statements `𝒟_{M}[e]` is
the law of `e` at `M`, i.e. `LawfulRandMonad.toPMF (e : M _)`, and
its `support` is the set of possible outputs. -/

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
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g₀ : MultiGraph α) (t : ℕ) (ht2 : 2 ≤ t) :
    ∀ (g : MultiGraph α) (rep : α → Finset α),
      g.WF → t ≤ g.verts.card → PickTracks g₀ g rep →
      ∀ p ∈ 𝒟_{M}[contractPick pick t g rep].support,
        p.1.WF ∧ t ≤ p.1.verts.card ∧ p.1.verts.card ≤ g.verts.card ∧
          (p.1.verts.card = t ∨ p.1.edges = []) ∧
          p.1.edges.length ≤ g.edges.length ∧
          g.minCutValue ≤ p.1.minCutValue ∧
          PickTracks g₀ p.1 p.2 := by
  intro g rep
  induction g, rep using contractPick.induct (pick := pick) (t := t) with
  | case1 g rep h ih =>
    intro hwf hcard ht p hp
    rw [contractPick, dif_pos h] at hp
    -- `toPMF_step` (`ARA.Infrastructure.Correctness.Correctness`)
    -- pushes `toPMF` through the branch via the `toPMF_simp` set
    toPMF_step at hp
    obtain ⟨i, -, hi⟩ := hp
    have hcard' := card_verts_contractAt hfresh hwf i
    have ht' : PickTracks g₀ (contractAt pick g i)
        (updateRep rep g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)])) :=
      ht.step hwf (List.getElem_mem _) (hfresh hwf (List.getElem_mem _))
    obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ :=
      ih i (hwf.contractAt pick i) (by omega) ht' p hi
    exact ⟨h1, h2', by omega, h4,
      le_trans h5 (length_edges_contractAt_lt pick g i).le,
      le_trans (minCutValue_le_contractAt hfresh hwf i (by omega)) h6, h7⟩
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

The proof follows Karger's: fix a minimum cut, count its crossing
edges, contract a non-crossing one. As far as we can tell only the
per-step transport lemma (`minCutValue_contractEdgeTo_of_notCrossing`)
touches the contraction model, and freshness feeds it. The loop being fuel-free, no fuel/card
equation is threaded: inside the guard the card is `k + s + 3` for
some `k`, and the guard-false leaves succeed with certainty — there
`s + 2 ≤ card` turns probability one into the stated bound.
`ℙ_{M}[e ∈ S]` is the probability under the law `𝒟_{M}[e]` that the
output lands in `S` (`ARA.Infrastructure.Randomness.Prob`). -/

/-- Survival of the minimum cut through the loop stopped at `s + 2`
vertices: the working graph still realizes the original minimum-cut
value with probability at least `(s+2)(s+1) / (n (n − 1))`. Karger is
the case `s = 0`; Karger–Stein recurses on `s + 2 = ksTarget n`, where
the bound is `≥ 1/2`. -/
theorem success_contractPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (s : ℕ) :
    ∀ (g : MultiGraph α) (rep : α → Finset α), g.WF →
      s + 2 ≤ g.verts.card →
      (((s + 2) * (s + 1) : ℕ) : ℝ≥0∞) /
          ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
        ℙ_{M}[contractPick pick (s + 2) g rep ∈
          {p | p.1.minCutValue = g.minCutValue}] := by
  intro g rep
  induction g, rep using contractPick.induct (pick := pick) (t := s + 2) with
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
      prob (inst.toPMF (contractPick pick (s + 2)
          (g.contractEdgeTo e (pick g e))
          (updateRep rep e (pick g e)) : M _))
        {p | p.1.minCutValue = g.minCutValue} with hF
    have hsum : (∑ i : Fin g.edges.length,
        prob (inst.toPMF (contractPick pick (s + 2) (contractAt pick g i)
            (updateRep rep g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)])) : M _))
          {p | p.1.minCutValue = g.minCutValue}) = (g.edges.map F).sum := by
      rw [← Fin.sum_univ_fun_getElem g.edges F]
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
        have hcard' : (contractAt pick g ⟨i, hilen⟩).verts.card
            = k + (s + 2) := by
          have := card_verts_contractAt hfresh hwf ⟨i, hilen⟩
          omega
        rw [← minCutValue_contractEdgeTo_of_notCrossing hwf
          (hfresh hwf he) (hwf.incidence _ he) (hwf.loopless _ he)
          (by omega) hS hSval hcr]
        have hih := ih ⟨i, hilen⟩ (hwf.contractAt pick ⟨i, hilen⟩) (by omega)
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
number undershoots neither minimum. Needs `Fresh pick`,
where the algorithm itself needed only `pick`. -/
theorem support_kargerBody
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) {g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (ht : PickTracks g₀ g rep) :
    ∀ o ∈ 𝒟_{M}[(contractPick pick 2 g rep >>= fun q =>
        pure (q.1.verts.image q.2, q.1.edges.length) :
          M (Finset (Finset α) × ℕ))].support,
      (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
        g₀.minCutValue ≤ o.2 ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  obtain ⟨q, hq, rfl⟩ := mem_support_toPMF_bind_pure.mp ho
  obtain ⟨hwf', h2', -, hend, -, hmin, ht'⟩ :=
    support_contractPick (M := M) hfresh g₀ 2 le_rfl g rep hwf h2 ht q hq
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
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟_{M}[Karger pick g].support,
      (∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2) ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  unfold Karger at ho
  obtain ⟨hcut, hmin, -⟩ :=
    support_kargerBody hfresh hwf h2 (PickTracks.init g) o ho
  exact ⟨hcut, hmin⟩

/-- The value-level survival bound for Karger's body on a tracked
pair: the reported number is the *current* minimum-cut value with
probability at least `2 / (n (n − 1))`. -/
theorem success_kargerBody
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) {g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (ht : PickTracks g₀ g rep) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[(contractPick pick 2 g rep >>= fun q =>
          pure (q.1.verts.image q.2, q.1.edges.length) :
            M (Finset (Finset α) × ℕ)) ∈ {o | o.2 = g.minCutValue}] := by
  have hmain : (2 : ℝ≥0∞) /
      ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[contractPick pick 2 g rep ∈
        {p | p.1.minCutValue = g.minCutValue}] := by
    simpa using success_contractPick (M := M) hfresh (s := 0) g rep hwf (by omega)
  rw [bind_pure_comp, LawfulRandMonad.toPMF_map, pmf_map_eq, prob_map]
  refine le_trans hmain (prob_mono_of_support fun q hq hev => ?_)
  obtain ⟨hwf', h2', -, hend, -, -, -⟩ :=
    support_contractPick (M := M) hfresh g₀ 2 le_rfl g rep hwf h2 ht q hq
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
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[Karger pick g ∈ {o | o.2 = g.minCutValue}] :=
  success_kargerBody hfresh hwf h2 (PickTracks.init g)

/-- Karger's theorem, pick-abstract and cut-level. A single run
returns an actual minimum cut (every reported side is a genuine cut of
`g` of value exactly `minCutValue`) with probability at least
`2 / (n (n − 1))`. Obtained from the value-level bound by
strengthening the event along the run's support invariant
(`karger_isCut`), not by re-induction. -/
theorem karger_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[Karger pick g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] := by
  refine le_trans (karger_success_prob hfresh g hwf h2)
    (prob_mono_of_support fun o ho hval => ?_)
  obtain ⟨hall, -⟩ := karger_isCut hfresh g hwf h2 o ho
  exact fun S hS => ⟨(hall S hS).1, (hall S hS).2.trans hval⟩

/-! ## Complexity

Each contraction round ticks `m'`, the current number of edges: the
contraction pass relabels and filters the whole edge list. Since
contraction never adds edges, every round costs at most `m` and the
loop stopped at `t` runs at most `n − t` rounds, giving expected cost
at most `(n − t) m`; Karger reads it at `t = 2`. The round count is
derived, not declared — the fuel-free trade of the module docstring —
so the bounds here need `WF` and freshness. `𝔼_{M}[cost e]` is the
expected tick count of `e` read at `TimeMT ℕ M`
(`ARA.Infrastructure.Complexity.ExpectedCost`). Tick placement is
trusted: the theorems bound the declared ticks, and matching them to
the work a pass does is a reading of the code, not a theorem. -/

/-- Expected cost of the pick loop stopped at `t` vertices: at most
`(n − t) m`. -/
lemma expected_cost_contractPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (t : ℕ) :
    ∀ (g : MultiGraph α) (rep : α → Finset α), g.WF →
      𝔼_{M}[cost (contractPick pick t g rep :
          TimeMT ℕ M (MultiGraph α × (α → Finset α)))] ≤
        ((g.verts.card - t : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  intro g rep
  induction g, rep using contractPick.induct (pick := pick) (t := t) with
  | case1 g rep h ih =>
    intro hwf
    rw [contractPick, dif_pos h, MonadCost.tick_timeMT,
      expected_cost_toPMF_tick_bind, expected_cost_uniform_step]
    -- Each branch starts from one fewer vertex and at most `m` edges,
    -- so the uniform average of the branch costs is at most
    -- `(n - (t + 1)) m`.
    have hbranch : ∀ i : Fin g.edges.length,
        𝔼_{M}[cost (contractPick pick t (contractAt pick g i)
            (updateRep rep g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)])) :
          TimeMT ℕ M (MultiGraph α × (α → Finset α)))] ≤
        ((g.verts.card - (t + 1) : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
      intro i
      have hcard := card_verts_contractAt hfresh hwf i
      exact le_trans (ih i (hwf.contractAt pick i))
        (mul_le_mul' (Nat.cast_le.mpr (by omega))
          (Nat.cast_le.mpr (length_edges_contractAt_lt pick g i).le))
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
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost Karger pick g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  unfold Karger
  rw [expected_cost_toPMF_bind_pure]
  exact expected_cost_contractPick hfresh 2 g _ hwf

/-- Finiteness of the expected cost, a free corollary of the
`(n - 2) m` bound. -/
lemma expected_cost_karger_ne_top
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost Karger pick g] ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le hfresh g hwf)

/-- Real-valued corollary: the expected cost is at most `(n - 2) * m`. -/
theorem karger_cost_le_real
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) :
    𝔼ℝ_{M}[cost Karger pick g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ) * (g.edges.length : ℝ) := by
  have := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
    (karger_cost_le (M := M) hfresh g hwf)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
  exact this

/-! ## Amplification: repetition finds the minimum cut

A single run succeeds with probability only `Ω(1/n²)`, but the
algorithm is one-sided (the reported value never undershoots), so
keeping the best output over independent runs succeeds as soon as any
single run does. The generic `amplify` combinator and its selector
`argmin` (`ARA.Infrastructure.Correctness.Amplify`) turn this into a
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
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card)
    (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify (argmin Prod.snd) k (Karger pick g)
          ∈ {o | o.2 = g.minCutValue}] :=
  amplify_argmin_success
    (fun o ho => (karger_isCut hfresh g hwf h2 o ho).2)
    (karger_success_prob hfresh g hwf h2) k

/-- Amplified cost: `k + 1` runs cost at most `k + 1` times the
single-run bound `(n − 2) m`. -/
theorem karger_amplified_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) (k : ℕ) :
    𝔼_{M}[cost amplify (argmin Prod.snd) (k + 1) (Karger pick g)] ≤
      (k + 1 : ℝ≥0∞) *
        (((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
  rw [expected_cost_amplify]
  exact mul_le_mul' le_rfl (karger_cost_le hfresh g hwf)
end ARA
