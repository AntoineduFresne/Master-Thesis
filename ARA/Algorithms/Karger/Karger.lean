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
supervertices remain; the surviving parallel edges form a cut of the
original graph, and it is a global minimum cut with probability at
least `2 / (n (n - 1))`.

## Graph model

The algorithm operates on an executable multigraph `MultiGraph α`:
a `Finset` of vertices plus a `List` of edges, parallel edges
repeated (one list entry per copy). Sampling an edge uniformly from
the list therefore picks an edge with probability proportional to its
multiplicity, so no weighted-choice primitive is needed.

The graph is **undirected**, and this is enforced by the types rather
than argued after the fact: an edge is a `Sym2 α`, so `s(u, v)` and
`s(v, u)` are literally the same term and no orientation exists to be
invariant under. `Crossing` is built with `Sym2.lift`, whose
well-definedness obligation *is* the symmetry proof — a
direction-sensitive crossing predicate cannot be written down. This
matters: the `2 / (n (n - 1))` bound is false for digraphs, where a
set can have no outgoing edge while every edge is incident on it, so
the "a random edge crosses the cut with probability `≤ 2/n`" step
fails.

`Sym2 α` is also the endpoint type used by GraphLib — `Edge.endpoints`
in `GraphLib/Graph/Basic.lean` on `main`, and `abbrev Edge := Sym2` in
Weixuan Yuan's `UndirectedGraphs/SimpleGraphs.lean` — so the graph
notion here is the one we intend to import once the toolchains align.

The cut/contraction theory itself is ported (not imported: those
branches are on older toolchains, and `main` has no cut theory yet).

Three deliberate adaptations:

* GraphLib's `contract` deduplicates parallel edges to stay inside
  simple graphs; here parallel edges are kept, since Karger's
  success-probability analysis is valid on multigraphs. GraphLib
  distinguishes parallel edges with an `Edge.edgeLabel`; we repeat the
  edge in a `List`, so `List (Sym2 α)` is GraphLib's
  `Set (Edge α (Fin m))` with the list position as the label.
* GraphLib's `Set`-based graphs are noncomputable; `MultiGraph` is
  executable, so the same definition runs under `IO` and is analyzed
  under `PMF`, and drawing a uniform edge *with multiplicity* is just
  `randFin edges.length`.
* GraphLib contracts by quotienting the vertex type with a `Setoid`
  (Weixuan's `Contractions.lean`), which changes the vertex type at
  every round; we merge one endpoint into the other so the type is
  preserved and the contraction loop is a plain recursion. That choice
  of survivor is fixed by `[LinearOrder α]`, needed only for the
  executable layer (`MultiGraph.contract'` onwards).

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


/-! ## Algorithm -/

open MultiGraph

-- The executable contraction loop fixes the surviving endpoint by the
-- linear order (see `MultiGraph.contract'`), so everything below needs
-- `[LinearOrder α]`. The cut theory above needs only `[DecidableEq α]`.
variable [LinearOrder α]

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

/-- The contraction loop **tracking the merge map**. `rep x` is the
supervertex that the original vertex `x` has been merged into; the
fibres of `rep` over the final vertex set are exactly the
supervertices, so they are what the algorithm reports.

This is `contractAux` with bookkeeping attached: `contractAuxT_fst`
says erasing the bookkeeping recovers `contractAux` exactly, so the
entire probability analysis is shared rather than redone. -/
def contractAuxT {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → MultiGraph α → (α → α) → M (MultiGraph α × (α → α))
  | 0, g, rep => pure (g, rep)
  | k + 1, g, rep =>
    if h : 0 < g.edges.length then do
      MonadCost.tick g.edges.length
      let i ← (haveI : NeZero g.edges.length := ⟨h.ne'⟩
        RandMonad.randFin g.edges.length)
      contractAuxT k (g.contract i)
        (redirect (g.edges[(i : ℕ)]).inf (g.edges[(i : ℕ)]).sup ∘ rep)
    else
      pure (g, rep)

/-- Erasing the bookkeeping recovers the untracked loop. -/
lemma contractAuxT_fst {M} [Monad M] [LawfulMonad M] [RandMonad M]
    [MonadCost ℕ M] :
    ∀ (k : ℕ) (g : MultiGraph α) (r : α → α),
      (Prod.fst <$> contractAuxT k g r : M (MultiGraph α)) = contractAux k g := by
  intro k
  induction k with
  | zero => intro g r; simp [contractAuxT, contractAux]
  | succ k ih =>
    intro g r
    by_cases h : 0 < g.edges.length
    · simp only [contractAuxT, contractAux, dif_pos h, map_bind, ih]
    · simp [contractAuxT, contractAux, dif_neg h]


/-- **Karger's algorithm.** Contract uniformly random edges until two
supervertices remain, then return the **cut** they induce: the set of
original vertices merged into one of the two surviving supervertices.
This is the textbook statement — the algorithm finds a cut, and
`cutValue` of it is the value reported by `valueRun`. -/
def Karger {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M (Finset α × ℕ) := do
  let p ← contractAuxT (g.verts.card - 2) g id
  pure (cutOf g p.2, p.1.edges.length)

/-- The value-only run: the number of surviving edges, with the cut
bookkeeping erased. This is the form the analysis inducts over;
`karger_value_eq` identifies it with the second component of `Karger`,
and `contractAuxT_fst` is what lets every bound proved here transfer. -/
private def valueRun {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M ℕ := do
  let g' ← contractAux (g.verts.card - 2) g
  pure g'.edges.length

-- ----------------------------------------
-- Different instances of "randomness"
-- ----------------------------------------

-- IO version (executable, untimed)
def Karger_IO : MultiGraph ℕ → IO (Finset ℕ × ℕ) := Karger

/-- Demo graph: two triangles joined by a single bridge — the global
minimum cut is `1` (the bridge). -/
def kargerDemo : MultiGraph ℕ where
  verts := {0, 1, 2, 3, 4, 5}
  edges := [s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3), s(2, 3)]

#eval Karger_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF (Finset ℕ × ℕ) := Karger

-- ----------------------------------------
-- Monad transformer version (timed)
-- ----------------------------------------

-- IO timed version (executable)
def Karger_IO_Timed : MultiGraph ℕ → TimeMT ℕ IO (Finset ℕ × ℕ) := Karger

#eval (Karger_IO_Timed kargerDemo).run

-- PMF timed version (noncomputable specification)
noncomputable example : MultiGraph ℕ → TimeMT ℕ PMF (Finset ℕ × ℕ) := Karger

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

/-- The arithmetic core of valueRun's induction step: if the current
graph has `m > 0` edges and `k + 3` vertices, and the fixed minimum cut
has `c ≤ m` crossing edges with `c * (k + 3) ≤ 2 * m` (the counting
bound), then picking a non-crossing edge and succeeding afterwards with
probability `2 / ((k+2)(k+1))` beats `2 / ((k+3)(k+2))`. -/
private lemma valueRun_step_bound {m c k : ℕ} (hm : 0 < m) (hc : c ≤ m)
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

/-! ## Correctness: valueRun never undershoots

The output of `valueRun` is always the value of *some* cut of the input
graph, hence at least the minimum-cut value. Together with the success
probability below, this makes `valueRun` a one-sided Monte Carlo
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
every value `valueRun` can output is at least the true minimum-cut value:
the algorithm never undershoots. -/
private theorem valueRun_correct
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ c ∈ 𝒟[valueRun g | M].support,
      g.minCutValue ≤ c := by
  intro c hc
  unfold valueRun at hc
  obtain ⟨g', hg', rfl⟩ := mem_support_toPMF_bind_pure.mp hc
  exact support_contractAux (g.verts.card - 2) g hwf (by omega) g' hg'

/-! ## The cut that Karger returns

`valueRun` bounds a *number*; the theorems below promote it to the
*cut* that `Karger` actually outputs. Everything rests on one bridge
(`cutValue_cutOf`): the cut a run returns has exactly the value that
run reports. The probability statements then transfer verbatim. -/

/-- The tracking invariant survives the whole contraction loop. -/
private lemma support_contractAuxT
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α} (hwf₀ : g₀.WF) :
    ∀ (k : ℕ) (g : MultiGraph α) (r : α → α), g.WF → g.verts.card = k + 2 →
      Tracks g₀ g r →
      ∀ p ∈ (inst.toPMF (contractAuxT k g r : M (MultiGraph α × (α → α)))).support,
        p.1.WF ∧ 2 ≤ p.1.verts.card ∧ (p.1.verts.card = 2 ∨ p.1.edges = []) ∧
          Tracks g₀ p.1 p.2 := by
  intro k
  induction k with
  | zero =>
    intro g r hwf hcard ht p hp
    rw [contractAuxT.eq_1, inst.toPMF_pure, pmf_pure_eq] at hp
    obtain rfl : p = (g, r) := by simpa [PMF.support_pure] using hp
    show g.WF ∧ 2 ≤ g.verts.card ∧ (g.verts.card = 2 ∨ g.edges = []) ∧
      Tracks g₀ g r
    exact ⟨hwf, by omega, Or.inl hcard, ht⟩
  | succ k ih =>
    intro g r hwf hcard ht p hp
    by_cases hm : 0 < g.edges.length
    · rw [contractAuxT.eq_2, dif_pos hm] at hp
      simp only [toPMF_simp, inst.toPMF_randFin] at hp
      obtain ⟨i, -, hi⟩ := (PMF.mem_support_bind_iff _ _ _).mp hp
      have hu : (g.edges[(i : ℕ)]).inf ∈ g.verts :=
        hwf.incidence _ (List.getElem_mem _) _ (sym2_inf_mem _)
      have hne : (g.edges[(i : ℕ)]).inf ≠ (g.edges[(i : ℕ)]).sup :=
        sym2_inf_ne_sup (hwf.loopless _ (List.getElem_mem _))
      exact ih (g.contract i) _ (hwf.contract i)
        (by have := card_verts_contract hwf i; omega)
        (ht.contractEdge hwf₀ hwf hu hne) p hi
    · rw [contractAuxT.eq_2, dif_neg hm, inst.toPMF_pure, pmf_pure_eq] at hp
      obtain rfl : p = (g, r) := by simpa [PMF.support_pure] using hp
      show g.WF ∧ 2 ≤ g.verts.card ∧ (g.verts.card = 2 ∨ g.edges = []) ∧
        Tracks g₀ g r
      exact ⟨hwf, by omega, Or.inr (List.eq_nil_of_length_eq_zero (by omega)), ht⟩

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
      set F : Sym2 α → ℝ≥0∞ := fun e =>
        inst.toPMF
          ((contractAux k (g.contract' e) >>=
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
          have hu := hwf.incidence e he _ (sym2_inf_mem e)
          have hv := hwf.incidence e he _ (sym2_sup_mem e)
          have hene := sym2_inf_ne_sup (hwf.loopless e he)
          have hwf' := hwf.contractEdge hu hene
          have hcard' : (g.contract' e).verts.card = k + 2 := by
            show (g.contractEdge e.inf e.sup).verts.card = k + 2
            have := card_verts_contractEdge (u := e.inf) g hv
            omega
          have hmc : (g.contract' e).minCutValue = g.minCutValue :=
            minCutValue_contractEdge_of_notCrossing hwf hu hv hene (by omega)
              hS hSval (by rwa [sym2_mk_inf_sup])
          have := ih (g.contract' e) hwf' hcard'
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
      have := valueRun_step_bound hm hc_le hbound
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

/-- **Success probability of valueRun's algorithm.** Over any
`LawfulRandMonad`, a single run outputs the exact minimum-cut value
with probability at least `2 / (n (n - 1))`, where `n = g.verts.card`.
Consequently `O(n² log n)` independent repetitions find a minimum cut
with high probability. -/
private theorem valueRun_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[valueRun g = g.minCutValue | M] := by
  have hmain := success_contractAux (M := M) (g.verts.card - 2) g hwf (by omega)
  have harith : (g.verts.card - 2 + 2) * (g.verts.card - 2 + 1) =
      g.verts.card * (g.verts.card - 1) := by
    rw [show g.verts.card - 2 + 2 = g.verts.card by omega,
      show g.verts.card - 2 + 1 = g.verts.card - 1 by omega]
  rw [harith] at hmain
  exact hmain

/-! ### Karger returns a minimum cut

The two theorems the textbook states. Both are obtained from the
`valueRun` analysis by *transport*, not by re-induction: `Karger`
and `valueRun` are two read-outs of the same run
(`contractAuxT`), and `cutValue_cutOf` says they agree on its
support, so `prob_map_congr_of_support` moves the bound across. -/

private lemma karger_eq_map {M} [Monad M] [LawfulMonad M] [RandMonad M]
    [MonadCost ℕ M] (g : MultiGraph α) :
    (Karger g : M (Finset α × ℕ))
      = (fun p => (cutOf g p.2, p.1.edges.length)) <$>
          contractAuxT (g.verts.card - 2) g id := by
  rw [map_eq_bind_pure_comp]
  rfl

private lemma valueRun_eq_map {M} [Monad M] [LawfulMonad M] [RandMonad M]
    [MonadCost ℕ M] (g : MultiGraph α) :
    (valueRun g : M ℕ)
      = (fun p => p.1.edges.length) <$> contractAuxT (g.verts.card - 2) g id := by
  calc (valueRun g : M ℕ)
      = contractAux (g.verts.card - 2) g >>= fun g' => pure g'.edges.length := rfl
    _ = (Prod.fst <$> contractAuxT (g.verts.card - 2) g id) >>=
          fun g' => pure g'.edges.length := by rw [contractAuxT_fst]
    _ = (fun p => p.1.edges.length) <$>
          contractAuxT (g.verts.card - 2) g id := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

/-- Everything a single run guarantees, unconditionally: the first
component is a genuine cut of `g`, the second is its value, and that
value never undershoots the minimum. -/
theorem karger_isCut
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟[Karger g | M].support,
      g.IsCut o.1 ∧ g.cutValue o.1 = o.2 ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  unfold Karger at ho
  obtain ⟨p, hp, rfl⟩ := mem_support_toPMF_bind_pure.mp ho
  obtain ⟨hwf', h2', hend, ht⟩ :=
    support_contractAuxT hwf (g.verts.card - 2) g id hwf (by omega)
      (Tracks.refl g hwf) p hp
  have hne : g.verts.Nonempty := Finset.card_pos.mp (by omega)
  have hcut := isCut_cutOf ht h2' hne
  have hval := cutValue_cutOf hwf' ht hend hne
  exact ⟨hcut, hval, hval ▸ minCutValue_le hcut⟩

/-- **Karger's theorem.** A single run returns an actual *minimum cut*
with probability at least `2 / (n (n - 1))`. -/
theorem karger_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[Karger g ∈ {o | o.2 = g.minCutValue} | M] := by
  rw [karger_eq_map]
  rw [prob_map_congr_of_support (t := ({g.minCutValue} : Set ℕ))
    (h := fun p => p.1.edges.length) _ ?_]
  · rw [← valueRun_eq_map, prob_singleton]
    exact valueRun_success_prob g hwf h2
  · intro p hp
    rw [Set.mem_setOf_eq, Set.mem_singleton_iff]

/-- **Amplified Karger.** Run the algorithm `k` times and keep the
cut of smallest value: the result is an actual minimum cut with
probability at least `1 − (1 − 2/(n(n−1)))^k`, so `O(n² log n)`
repetitions find one with high probability. Selecting by the reported
value (`argmin Prod.snd`) costs nothing — the run already computed it. -/
theorem karger_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ[amplify (argmin Prod.snd) k (Karger g)
          ∈ {o | o.2 = g.minCutValue} | M] :=
  amplify_argmin_success
    (fun o ho => (karger_isCut g hwf h2 o ho).2.2)
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

/-- The tracked loop costs exactly what the untracked one costs:
bookkeeping is pure post-processing (`expected_cost_toPMF_map`). -/
private lemma expected_cost_contractAuxT
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (k : ℕ) (g : MultiGraph α) (r : α → α) :
    𝔼_runtime[(contractAuxT k g r : TimeMT ℕ M (MultiGraph α × (α → α)))] ≤
      (k : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) := by
  rw [← expected_cost_toPMF_map Prod.fst
    (contractAuxT k g r : TimeMT ℕ M (MultiGraph α × (α → α)))]
  rw [show (Prod.fst <$> (contractAuxT k g r : TimeMT ℕ M _)) =
      (contractAux k g : TimeMT ℕ M (MultiGraph α)) from contractAuxT_fst k g r]
  exact expected_cost_contractAux k g

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
  exact expected_cost_contractAuxT _ g _

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
      (k + 1 : ℝ≥0∞) * (((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞)) := by
  rw [expected_cost_amplify]
  exact mul_le_mul' le_rfl (karger_cost_le g)

end ARA
