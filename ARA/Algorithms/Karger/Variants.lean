import ARA.Algorithms.Karger.Karger
import ARA.Algorithms.Karger.KargerEnum
import Mathlib.Data.Sym.Sym2.Order

/-
# The contraction problem for Karger's algorithm:

in a contraction, two endpoints leave, one vertex w enters, every edge
is redirected through the merge, the loops die and parallel edges stay.

We have one problem (or multiple ones?): we need to produce the new vertex w.

Three things:

-it must not collide with a vertex that is still there untouched, otherwise
the step loses two vertices instead of one;

-it must be a symmetric function of u and v, since the edge is unordered
(`Sym2 α`) otherwise "contract this edge" is not a function at all;

-it must exist.
-/

/-
# Recall that:

An edge is an unordered pair. In Mathlib that is `Sym2 α`, the quotient of
`α × α` by the swap (`Mathlib/Data/Sym/Sym2.lean`, inside `namespace Sym2`):

    inductive Rel (α : Type u) : α × α → α × α → Prop
      | refl (x y : α) : Rel _ (x, y) (x, y)
      | swap (x y : α) : Rel _ (x, y) (y, x)

    abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)

    protected abbrev Sym2.mk {α : Type*} (a b : α) : Sym2 α := Quot.mk (Sym2.Rel α) (a, b)

    notation3 "s(" x ", " y ")" => Sym2.mk x y

So `s(u, v)` and `s(v, u)` are the same term: orientation is not irrelevant here,
it is inexpressible. The price of that is the universal property that a function
out of `Sym2 α` has to be handed over as a symmetric function of two arguments.

    def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β)

    def map (f : α → β) : Sym2 α → Sym2 β :=
      Quot.map (Prod.map f f) (by intro _ _ h; cases h <;> constructor)

    def IsDiag : Sym2 α → Prop :=
      lift ⟨Eq, fun _ _ => propext eq_comm⟩

A graph is then a vertex set and an edge list, one entry per parallel copy
(`ARA/Helpers/MultiGraph.lean`):

    structure MultiGraph (α : Type) where
      verts : Finset α
      edges : List (Sym2 α)

    structure WF (g : MultiGraph α) : Prop where
      incidence : ∀ e ∈ g.edges, ∀ v ∈ e, v ∈ g.verts
      loopless  : ∀ e ∈ g.edges, ¬ e.IsDiag

Note that:

multiplicity is carried by repetition in the list and not by a weight, which is
what makes "draw a uniformly random edge" nothing more than
`randFin edges.length`: an edge comes up with probability proportional to its
multiplicity, for free, and the whole thing stays executable.

`WF` is the property that we assume of an input and must re-establish after every
contraction: endpoints are vertices, and no edge is a loop.
-/

/-
# TEMPLATE

## of contraction:

    def redirectTo (e : Sym2 β) (w : β) (x : β) : β :=
      if x ∈ e then w else x

a-b then a and b go to w and the rest is untouched

    def contractEdgeTo (g : MultiGraph β) (e : Sym2 β) (w : β) (h : w ∉ g.verts \ e) : MultiGraph β where
      verts := insert w (g.verts.filter (· ∉ e))
      edges := (g.edges.map (Sym2.map (redirectTo e w))).filter fun e' => !e'.IsDiag

That is the whole of contraction: `verts` says the two endpoints leave and w
enters, `edges` says every edge is redirected through the merge and the loops
this creates are dropped.

problem: what happens when w is in the graph already.

So with this definition of contraction. how do we find the
new vertex `w`?

so a solution is to take a function `pick` that takes the graph and the edge and returns a
new vertex `w` that is not in the graph (with the deleted endpoints) and is symmetric in
the edge endpoints.

-- contracts the graph along its i-th edge with the new vertex chosen by `pick`.
    def contractAt (pick : MultiGraph β → Sym2 β → β)
        (g : MultiGraph β) (i : Fin g.edges.length) : MultiGraph β :=
        e = g.edges[(i : ℕ)]
      g.contractEdgeTo e (pick g e)

-- second version for another source of randomness on finset (not list index)
-- contracts the graph along its i-th edge with the new vertex chosen by `pick`.
    def contractAtsecond (pick : MultiGraph β → Sym2 β → β)
        (g : MultiGraph β) (e : Sym2 β) (h : e ∈ g.edges) : MultiGraph β :=
      g.contractEdgeTo e (pick g e)

-- Karger algorithm (without cut reporting)
    def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
        (pick : MultiGraph β → Sym2 β → β) (g : MultiGraph β) : M (Finset β × ℕ) :=

      if h : 3 ≤ g.verts.card ∧ 0 < g.edges.length then do
        MonadCost.tick g.edges.length
        let i ← randIdx g.edges h.2
        Karger pick (contractAt pick g i)

      else:
        pure (g.verts, g.edges.length)

    termination_by g.edges.length
    decreasing_by exact length_edges_contractAt_lt pick g i

-- the `3 ≤` stops one step early to report a cut.
-- Here Karger returns the two surviving vertices and the number of edges between them,
-- which is the value of the cut.


A second version can carry a map `rep` (for report) sending every vertex
to the set of original vertices merged into it, and update it at each step.

-- report function
    def repOf (rep : β → Finset α) : Sym2 β → Finset α :=
      Sym2.lift ⟨fun u v => rep u ∪ rep v, fun _ _ => Finset.union_comm _ _⟩

 a basic rep function could be β → Finset β that a ↦ {a}

 Multigraph Finset β

-- Karger algorithm (with cut reporting)
    def KargerCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
        (pick : MultiGraph β → Sym2 β → β) (g : MultiGraph β) (rep : β → Finset α) :
        M (Finset (Finset α) × ℕ) :=

      if h : 3 ≤ g.verts.card ∧ 0 < g.edges.length then do
        MonadCost.tick g.edges.length
        let i ← randIdx g.edges h.2
        KargerCut pick (contractAt pick g i)
          (fun x => if x = pick g g.edges[(i : ℕ)]
                    then repOf rep g.edges[(i : ℕ)] else rep x)

      else
        pure (g.verts.image rep, g.edges.length)

    termination_by g.edges.length
    decreasing_by exact length_edges_contractAt_lt pick g i

if I take rep to be the simple function as above then

initially rep is simply a ↦ {a} and by doig a contraciton on g along the edge e = {u, v} with picked vertices w
then we update rep to send all vertices `a` that is not w one are going to stay mapped to {a}
and w is going to be mapped to the union of the two endpoints of e. w ↦ {u, v}

-- Here KargerCut returns the two surviving vertices and the number of edges between them,
-- which is the value of the cut, and also the two sets of original vertices merged into
-- them, thanks to the report function which is the cut itself.

-/

/-
# multiple options for pick:

* We take an injective labelling of the vertices `ℓ : α ↪ ℕ` as an input, once,
  and merge every drawn edge into its endpoint of smaller label.
  The vertex type needs nothing beyond `DecidableEq`, which is only there to
  run the redirection (`x ∈ e`) and the `Finset` operations on the vertex set.

  The merged vertex is always one of the two endpoints, so we never
  need a new element of α, and all the choosing happens in ℕ through `ℓ`.

  the pick function is

      def enumPick (ℓ : α ↪ ℕ) : Sym2 α → α :=
        Sym2.lift ⟨fun u v => if ℓ u ≤ ℓ v then u else v, symmetry proof⟩

      def KargerEnum (ℓ : α ↪ ℕ) (g : MultiGraph α) : M (Finset α × ℕ) :=
        Karger (fun _ e => enumPick ℓ e) g

  Problems:

  -the labelling goes in every statement: the theorems are
  about `KargerEnum ℓ g` although neither the answer nor the bounds
  depend on `ℓ`;

  -the merged vertex is one of the two endpoints, so it forgets what it
  erased: we can (in Karger) report the value of the cut, but not the cut if
  we want it.

  Note: for KargerCut this works.

      def KargerEnumCut (ℓ : α ↪ ℕ) (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
        KargerCut (fun _ e => enumPick ℓ e) g (fun a => {a})

      #eval KargerEnumCut ℓ kargerDemo   -- ({{1, 2, 3, 0, 4}, {5}}, 2)

* We ask the vertex type for a linear order and merge into `min u v`.

  the pick function is

      def orderPick : MultiGraph α → Sym2 α → α := fun _ e => e.inf

      def KargerOrder [LinearOrder α] (g : MultiGraph α) : M (Finset α × ℕ) :=
        Karger orderPick g

  here: `inf` is commutative outright.

  Problems:

  -`[LinearOrder α]` stands in every statement and says nothing about the
  problem: a minimum cut does not care that the vertices are comparable;

  -same forgetting as above, the merged vertex being again an endpoint: the
  value of the cut, not the cut.

  Note: for KargerCut this works:

      def KargerOrderCut [LinearOrder α] (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
        KargerCut orderPick g (fun a => {a})

      #eval KargerOrderCut kargerDemo    -- ({{4, 2, 5, 3}, {0, 1}}, 2)

* We take a genuinely new name `w ∉ verts` and glue everything to it.

  for example on ℕ the pick function is

      def freshPick : MultiGraph ℕ → Sym2 ℕ → ℕ := fun g _ => g.verts.sup id + 1

      def KargerFresh (g : MultiGraph ℕ) : M (Finset ℕ × ℕ) :=
        Karger freshPick g

  Problems:

  -the name has to come from somewhere. For an arbitrary α that means
  `Infinite α` plus choice, which is noncomputable: we lose the `IO` reading,
  and with it one of the four instantiations of the same text;

  -for a finite α, if the graph uses all of
  them, then we need to choose one of the endpoints.

  -forgets what it erases, so after n-2 steps the two survivors
  are two meaningless names: the value of the cut, not the cut.

  Note: for KargerCut this works

      def KargerFreshCut (g : MultiGraph ℕ) : M (Finset (Finset ℕ) × ℕ) :=
        KargerCut freshPick g (fun a => {a})

      #eval KargerFreshCut kargerDemo    -- ({{1, 2, 3, 4, 5}, {0}}, 2)

* We take the union `w = u ∪ v`. Vertices are sets of original vertices, each one starts
  as its own singleton, and merging is union. `∪` is commutative so symmetric, computable,
  and `w` remembers exactly which original vertices are inside it, so the two
  survivors are the two sides of the cut, and we get also a the cut!

  the pick function is

      def unionPick : MultiGraph (Finset α) → Sym2 (Finset α) → Finset α :=
        fun _ e => unionOf e

      def KargerUnion (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
        Karger unionPick g.super

  Problems:

  -the working vertex type is `Finset α` and not α (so can be strange for the brain),
  paid once on entry with

  -one invariant travels with the run: the supervertices stay pairwise disjoint.
  It is what makes the union automatically a new vertex, and it is also exactly
  the statement that the surviving sets form a partition of V, so it is the
  reason the answer is a cut, not overhead.

  Note: we can bypass KargerCut this way.

      #eval KargerUnionCut kargerDemo    -- ({{0, 1}, {2, 3, 4, 5}}, 2)

  because `repOf id` is `unionOf`.
-/

namespace ARA.Variants

open MultiGraph
open Cslib.Algorithms.Lean

variable {β : Type} [DecidableEq β] {α : Type} [DecidableEq α]

private lemma map_self_isDiag (e : Sym2 β) (w : β) :
    (Sym2.map (redirectTo e w) e).IsDiag := by
  induction e with
  | _ u v =>
    have h1 : redirectTo s(u, v) w u = w := by simp [redirectTo]
    have h2 : redirectTo s(u, v) w v = w := by simp [redirectTo]
    rw [Sym2.map_mk, h1, h2, Sym2.mk_isDiag_iff]

def contractAt (pick : MultiGraph β → Sym2 β → β)
    (g : MultiGraph β) (i : Fin g.edges.length) : MultiGraph β :=
  g.contractEdgeTo g.edges[(i : ℕ)] (pick g g.edges[(i : ℕ)])

theorem length_edges_contractAt_lt (pick : MultiGraph β → Sym2 β → β)
    (g : MultiGraph β) (i : Fin g.edges.length) :
    (contractAt pick g i).edges.length < g.edges.length := by
  rw [contractAt, edges_contractEdgeTo]
  set e := g.edges[(i : ℕ)] with he
  set w := pick g e with hw
  have hlen : (g.edges.map (Sym2.map (redirectTo e w))).length = g.edges.length := by simp
  refine lt_of_lt_of_le ?_ (le_of_eq hlen)
  refine List.length_filter_lt_length_iff_exists.mpr
    ⟨Sym2.map (redirectTo e w) e, List.mem_map_of_mem (List.getElem_mem _), ?_⟩
  simpa using map_self_isDiag e w

def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph β → Sym2 β → β) (g : MultiGraph β) : M (Finset β × ℕ) :=
  if h : 3 ≤ g.verts.card ∧ 0 < g.edges.length then do
    MonadCost.tick g.edges.length
    let i ← randIdx g.edges h.2
    Karger pick (contractAt pick g i)
  else
    pure (g.verts, g.edges.length)
termination_by g.edges.length
decreasing_by exact length_edges_contractAt_lt pick g i

def repOf (rep : β → Finset α) : Sym2 β → Finset α :=
  Sym2.lift ⟨fun u v => rep u ∪ rep v, fun _ _ => Finset.union_comm _ _⟩

def KargerCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph β → Sym2 β → β) (g : MultiGraph β) (rep : β → Finset α) :
    M (Finset (Finset α) × ℕ) :=
  if h : 3 ≤ g.verts.card ∧ 0 < g.edges.length then do
    MonadCost.tick g.edges.length
    let i ← randIdx g.edges h.2
    KargerCut pick (contractAt pick g i)
      (fun x => if x = pick g g.edges[(i : ℕ)]
                then repOf rep g.edges[(i : ℕ)] else rep x)
  else
    pure (g.verts.image rep, g.edges.length)
termination_by g.edges.length
decreasing_by exact length_edges_contractAt_lt pick g i

def unionPick : MultiGraph (Finset α) → Sym2 (Finset α) → Finset α :=
  fun _ e => unionOf e

def orderPick [LinearOrder β] : MultiGraph β → Sym2 β → β := fun _ e => e.inf

def picklist


def freshPick : MultiGraph ℕ → Sym2 ℕ → ℕ := fun g _ => g.verts.sup id + 1

def KargerUnion {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) := Karger unionPick g.super

def KargerOrder {M} [Monad M] [RandMonad M] [MonadCost ℕ M] [LinearOrder α]
    (g : MultiGraph α) : M (Finset α × ℕ) := Karger orderPick g

def KargerEnum {M} [Monad M] [RandMonad M] [MonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) : M (Finset α × ℕ) := Karger (fun _ e => enumPick ℓ e) g

def KargerFresh {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph ℕ) : M (Finset ℕ × ℕ) := Karger freshPick g

def KargerUnionCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) := KargerCut unionPick g.super id

def KargerOrderCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M] [LinearOrder α]
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
  KargerCut orderPick g (fun a => {a})

def KargerEnumCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
  KargerCut (fun _ e => enumPick ℓ e) g (fun a => {a})

def KargerFreshCut {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph ℕ) : M (Finset (Finset ℕ) × ℕ) :=
  KargerCut freshPick g (fun a => {a})

def idLabel : ℕ ↪ ℕ := ⟨id, fun _ _ h => h⟩

#eval (KargerUnion kargerDemo : IO (Finset (Finset ℕ) × ℕ))
#eval (KargerOrder kargerDemo : IO (Finset ℕ × ℕ))
#eval (KargerEnum idLabel kargerDemo : IO (Finset ℕ × ℕ))
#eval (KargerFresh kargerDemo : IO (Finset ℕ × ℕ))

#eval (KargerUnionCut kargerDemo : IO (Finset (Finset ℕ) × ℕ))
#eval (KargerOrderCut kargerDemo : IO (Finset (Finset ℕ) × ℕ))
#eval (KargerEnumCut idLabel kargerDemo : IO (Finset (Finset ℕ) × ℕ))
#eval (KargerFreshCut kargerDemo : IO (Finset (Finset ℕ) × ℕ))

#eval (show TimeMT ℕ IO (Finset (Finset ℕ) × ℕ) from KargerUnion kargerDemo).run

noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) := KargerUnion
noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) := KargerOrderCut

end ARA.Variants
