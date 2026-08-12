/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Algorithms.Karger.Karger

/-!
# The Karger–Stein recursive contraction algorithm

A single contraction run succeeds with probability only `Θ(1/n²)`, but
the *early* contractions are nearly safe and only the late ones are
risky. Karger–Stein contracts down to `ksTarget n ≈ n/√2` vertices, which
preserves the minimum cut with probability `≥ 1/2` by the
*definition* of `ksTarget`, and spends the repetition budget on the
risky small graphs by recursing twice and keeping the better output.

## Main results

For `n` the number of vertices, `m` the number of edges (with
multiplicity) and `d = ksDepth n` the recursion depth, we have:

* `kargerStein_finds_min`: a run returns an actual minimum cut
  with probability at least `1 / (ksDepth n + 3)`, where `ksDepth n`
  is the recursion depth (`≈ 2·log₂ n`; the `⌈log⌉` depth bound is
  `KargerStein.md` §6, the resulting success bound its §4 corollary).
* `kargerStein_isCut`: one-sided error: every output is a partition
  into genuine cuts of the reported value, never undershooting.
* `kargerStein_cost_le`: expected cost at most `(2^(d+2) − 2)·n·m` in
  the edge-list cost model (the interim bound of `KargerStein.md` §5;
  the level-sum `7n²m` refinement is future work).

## Architecture

The recursion operates directly on the working pairs of `Karger.lean`,
a graph and its fibre map: contraction preserves the vertex type, so
no lifting is ever needed. It consumes Karger's shared
kernel: `contractPick` (the loop, at target `ksTarget n`),
`success_contractPick` (survival of the minimum cut through partial
contraction) and `support_contractPick` (the run invariant), together
with the `amplify` layer for the best-of-two composition. The
recursion is fueled by `ksDepth`, so termination is structural; the
analysis shows the fuel is exactly sufficient. The merge rule is
abstract: as in `Karger.lean`, `pick` defines and `fresh` proves.
-/

namespace ARA

open Cslib.Algorithms.Lean
open List
open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-! ## The contraction target and the recursion depth -/

private lemma ksTarget_exists (n : ℕ) :
    ∃ t, 2 ≤ t ∧ n * (n - 1) ≤ 2 * (t * (t - 1)) :=
  ⟨max n 2, le_max_right .., by
    calc n * (n - 1) ≤ max n 2 * (max n 2 - 1) :=
          Nat.mul_le_mul (le_max_left ..) (by omega)
      _ ≤ 2 * (max n 2 * (max n 2 - 1)) := Nat.le_mul_of_pos_left _ (by omega)⟩

/-- The contraction target: the least `t ≥ 2` at which the survival
probability `t(t−1)/(n(n−1))` of a fixed minimum cut reaches `1/2`,
classically `⌈1 + n/√2⌉`, characterized integrally (no `√2`). -/
def ksTarget (n : ℕ) : ℕ := Nat.find (ksTarget_exists n)

lemma ksTarget_two_le (n : ℕ) : 2 ≤ ksTarget n :=
  (Nat.find_spec (ksTarget_exists n)).1

/-- The defining inequality: contracting to `ksTarget n` vertices
keeps the survival probability at least `1/2`. -/
lemma ksTarget_bound (n : ℕ) :
    n * (n - 1) ≤ 2 * (ksTarget n * (ksTarget n - 1)) :=
  (Nat.find_spec (ksTarget_exists n)).2

/-- The target genuinely shrinks the graph, exactly from `n = 4` on,
which delimits the recursion's base case. -/
lemma ksTarget_lt {n : ℕ} (h4 : 4 ≤ n) : ksTarget n < n := by
  have hle : ksTarget n ≤ n - 1 := by
    refine Nat.find_le ⟨by omega, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega]
    nlinarith
  omega

/-- The recursion depth: `0` for the base case `n ≤ 3`, else one more
than the depth at the contraction target. -/
def ksDepth : ℕ → ℕ
  | n =>
    if h : 4 ≤ n then
      1 + ksDepth (ksTarget n)
    else 0
  termination_by n => n
  decreasing_by exact ksTarget_lt h

lemma ksDepth_of_ge {n : ℕ} (h4 : 4 ≤ n) :
    ksDepth n = 1 + ksDepth (ksTarget n) := by
  rw [ksDepth]
  exact dif_pos h4

lemma ksDepth_of_lt {n : ℕ} (h4 : ¬ 4 ≤ n) : ksDepth n = 0 := by
  rw [ksDepth]
  exact dif_neg h4

/-! ## Algorithm -/

/-- One fueled round of Karger–Stein: on `≤ 3` vertices (or on
exhausted fuel) contract fully and report the fibres of the two
survivors with the surviving edge count; otherwise, twice and
independently, contract down to `ksTarget n` vertices and recurse,
keeping the output with the smaller reported value. -/
def kargerSteinAux {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) :
    ℕ → MultiGraph α × (α → Finset α) → M (Finset (Finset α) × ℕ)
  | 0, p => do
      let q ← contractPick pick 2 p.1 p.2
      pure (q.1.verts.image q.2, q.1.edges.length)
  | fuel + 1, p =>
      if 4 ≤ p.1.verts.card then
        amplify (argmin Prod.snd) 2
          (contractPick pick (ksTarget p.1.verts.card) p.1 p.2 >>=
            fun q => kargerSteinAux pick fuel q)
      else do
        let q ← contractPick pick 2 p.1 p.2
        pure (q.1.verts.image q.2, q.1.edges.length)

/-- The Karger–Stein algorithm: recursive contraction with fuel
`ksDepth n` (exactly the recursion depth), on singleton fibres. -/
def KargerStein {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) (g : MultiGraph α) :
    M (Finset (Finset α) × ℕ) :=
  kargerSteinAux pick (ksDepth g.verts.card) (g, fun a => {a})

/-- Karger–Stein at `M = IO`: executable, on `ℕ` vertices with the
demo pick. -/
def KargerStein_IO : MultiGraph ℕ → IO (Finset (Finset ℕ) × ℕ) :=
  KargerStein demoPick

#eval KargerStein_IO demoGraph

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) :=
  KargerStein demoPick

/-! ## The leaf: a full contraction run

Both the base case and the small-graph case run Karger's body on the
working pair; `support_kargerBody` and `success_kargerBody` state its
guarantees. -/

/-- The leaf bound on at most three vertices, in the `1/(0 + 3)` form
both base cases of the success induction need. -/
private lemma success_ksLeaf_small
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) {g : MultiGraph α} {rep : α → Finset α}
    (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (h3 : g.verts.card ≤ 3)
    (ht : PickTracks g₀ g rep) :
    ((1 : ℕ) : ℝ≥0∞) / ((0 + 3 : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[(contractPick pick 2 g rep >>= fun q =>
          pure (q.1.verts.image q.2, q.1.edges.length) :
            M (Finset (Finset α) × ℕ)) ∈ {o | o.2 = g.minCutValue}] := by
  refine le_trans ?_ (success_kargerBody hfresh hwf h2 ht)
  have h6 : g.verts.card * (g.verts.card - 1) ≤ 6 := by
    rcases (by omega : g.verts.card = 2 ∨ g.verts.card = 3) with h | h <;>
      simp [h]
  exact_mod_cast ennreal_div_le_div_nat (a := 1) (b := 0 + 3) (c := 2)
    (d := g.verts.card * (g.verts.card - 1)) (by norm_num)
    (Nat.mul_pos (by omega) (by omega)) (by simpa using h6)

/-- `argmin` keeps one of its two arguments, so it never leaves an
invariant set: the closure obligation of every `amplify` call here. -/
private lemma argmin_mem {β γ : Type} [LinearOrder γ] (f : β → γ)
    {V : Set β} : ∀ a ∈ V, ∀ b ∈ V, argmin f a b ∈ V := by
  intro a ha b hb
  unfold argmin
  split_ifs
  exacts [ha, hb]

/-! ## Degenerate graphs: no edges left -/

private lemma contractPick_edgeless {M} [Monad M] [RandMonad M]
    [MonadCost ℕ M] (pick : MultiGraph α → Sym2 α → α) (t : ℕ)
    {g : MultiGraph α} (hnil : g.edges = []) (rep : α → Finset α) :
    (contractPick pick t g rep : M (MultiGraph α × (α → Finset α))) =
      pure (g, rep) := by
  rw [contractPick, dif_neg (by simp [hnil])]

private lemma support_kargerSteinAux_edgeless
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (pick : MultiGraph α → Sym2 α → α) :
    ∀ fuel (p : MultiGraph α × (α → Finset α)), p.1.edges = [] →
      ∀ o ∈ 𝒟_{M}[kargerSteinAux pick fuel p].support,
        o = (p.1.verts.image p.2, 0) := by
  intro fuel p
  induction fuel, p using kargerSteinAux.induct with
  | case1 p =>
    intro hnil o ho
    rw [kargerSteinAux.eq_1, contractPick_edgeless pick 2 hnil p.2,
      pure_bind] at ho
    toPMF_step at ho
    rw [ho, hnil]
    rfl
  | case2 fuel p h4 ih =>
    intro hnil o ho
    rw [kargerSteinAux.eq_2, if_pos h4,
      contractPick_edgeless pick (ksTarget p.1.verts.card) hnil p.2,
      pure_bind] at ho
    exact support_amplify_subset (V := {o | o = (p.1.verts.image p.2, 0)})
      (ih p hnil) (argmin_mem Prod.snd) 2 ho
  | case3 fuel p h4 =>
    intro hnil o ho
    rw [kargerSteinAux.eq_2, if_neg h4, contractPick_edgeless pick 2 hnil p.2,
      pure_bind] at ho
    toPMF_step at ho
    rw [ho, hnil]
    rfl

/-! ## The run invariant -/

/-- One-sided error: every output of a Karger–Stein run is a partition
of the tracked graph into genuine cuts of the reported value, and the
reported value never undershoots either minimum. -/
private lemma support_kargerSteinAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) :
    ∀ fuel (p : MultiGraph α × (α → Finset α)), p.1.WF →
      2 ≤ p.1.verts.card → PickTracks g₀ p.1 p.2 →
      ∀ o ∈ 𝒟_{M}[kargerSteinAux pick fuel p].support,
        (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
          g₀.minCutValue ≤ o.2 ∧ p.1.minCutValue ≤ o.2 := by
  intro fuel p
  induction fuel, p using kargerSteinAux.induct with
  | case1 p =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_1] at ho
    exact support_kargerBody hfresh hwf h2 ht o ho
  | case2 fuel p h4 ih =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_2, if_pos h4] at ho
    refine support_amplify_subset
      (V := {o | (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
        g₀.minCutValue ≤ o.2 ∧ p.1.minCutValue ≤ o.2}) ?_ ?_ 2 ho
    · intro o' ho'
      obtain ⟨q, hq, ho''⟩ := mem_support_toPMF_bind.mp ho'
      obtain ⟨hwf'', hcard'', -, -, -, hmin'', ht''⟩ :=
        support_contractPick (M := M) hfresh g₀ (ksTarget p.1.verts.card)
          (ksTarget_two_le _) p.1 p.2 hwf (ksTarget_lt h4).le ht q hq
      obtain ⟨hcut, hle₀, hle'⟩ := ih q hwf''
        (le_trans (ksTarget_two_le _) hcard'') ht'' o' ho''
      exact ⟨hcut, hle₀, le_trans hmin'' hle'⟩
    · exact argmin_mem Prod.snd
  | case3 fuel p h4 =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_2, if_neg h4] at ho
    exact support_kargerBody hfresh hwf h2 ht o ho

/-! ## Success probability -/

/-- First ℕ-fraction fact of the recurrence: a product of two casts
of ℕ-fractions is the cast of the product fraction. -/
private lemma ennreal_natCast_div_mul_div (a b c d : ℕ) (hb : b ≠ 0) :
    ((a : ℝ≥0∞) / b) * ((c : ℝ≥0∞) / d) =
      ((a * c : ℕ) : ℝ≥0∞) / ((b * d : ℕ) : ℝ≥0∞) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast hb))
      (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-- `1 − 1/c = (c−1)/c` over the ℕ-casts. -/
private lemma ennreal_one_sub_inv_natCast {c : ℕ} (hc : 0 < c) :
    1 - ((1 : ℕ) : ℝ≥0∞) / ((c : ℕ) : ℝ≥0∞) =
      ((c - 1 : ℕ) : ℝ≥0∞) / ((c : ℕ) : ℝ≥0∞) := by
  rw [ENNReal.natCast_sub, Nat.cast_one,
    ENNReal.sub_div (fun _ _ => by exact_mod_cast hc.ne'),
    ENNReal.div_self (by exact_mod_cast hc.ne') (ENNReal.natCast_ne_top _)]

/-- Success of a fueled run: with fuel at least the recursion
depth, a run reports the current minimum-cut value with probability at
least `1/(ksDepth n + 3)`. -/
private theorem success_kargerSteinAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) :
    ∀ fuel (p : MultiGraph α × (α → Finset α)), p.1.WF →
      2 ≤ p.1.verts.card → PickTracks g₀ p.1 p.2 →
      ksDepth p.1.verts.card ≤ fuel →
      ((1 : ℕ) : ℝ≥0∞) / ((ksDepth p.1.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
        ℙ_{M}[kargerSteinAux pick fuel p ∈
          {o | o.2 = p.1.minCutValue}] := by
  intro fuel p
  induction fuel, p using kargerSteinAux.induct with
  | case1 p =>
    intro hwf h2 ht hdepth
    have hd0 : ksDepth p.1.verts.card = 0 := Nat.le_zero.mp hdepth
    have h3 : p.1.verts.card ≤ 3 := by
      by_contra hc
      rw [ksDepth_of_ge (by omega)] at hd0
      omega
    rw [kargerSteinAux.eq_1, hd0]
    exact success_ksLeaf_small hfresh hwf h2 h3 ht
  | case2 fuel p h4 ih =>
    intro hwf h2 ht hdepth
    rw [kargerSteinAux.eq_2, if_pos h4]
    have ht2 := ksTarget_two_le p.1.verts.card
    have htlt := ksTarget_lt h4
    have hdd : ksDepth p.1.verts.card =
        1 + ksDepth (ksTarget p.1.verts.card) :=
      ksDepth_of_ge h4
    have hdt : ksDepth (ksTarget p.1.verts.card) ≤ fuel := by omega
    -- Survival to `t = ksTarget n` vertices happens with probability
    -- at least `1/2`, by the definition of the target.
    have hsurv := success_contractPick (M := M) hfresh
      (s := ksTarget p.1.verts.card - 2) p.1 p.2 hwf (by omega)
    rw [show ksTarget p.1.verts.card - 2 + 2 = ksTarget p.1.verts.card by omega,
      show ksTarget p.1.verts.card - 2 + 1 = ksTarget p.1.verts.card - 1 by
        omega] at hsurv
    have h1 : (1 : ℝ≥0∞) / 2 ≤
        prob (inst.toPMF (contractPick pick
            (ksTarget p.1.verts.card) p.1 p.2 : M _))
          {q | q.1.minCutValue = p.1.minCutValue} := by
      refine le_trans ?_ hsurv
      exact_mod_cast ennreal_div_le_div_nat (a := 1) (b := 2)
        (c := ksTarget p.1.verts.card * (ksTarget p.1.verts.card - 1))
        (d := p.1.verts.card * (p.1.verts.card - 1)) (by norm_num)
        (Nat.mul_pos (by omega) (by omega))
        (by have := ksTarget_bound p.1.verts.card; nlinarith)
    -- Each branch: survive, then recurse.
    have hp : (1 : ℝ≥0∞) / 2 *
        (((1 : ℕ) : ℝ≥0∞) /
          ((ksDepth (ksTarget p.1.verts.card) + 3 : ℕ) : ℝ≥0∞)) ≤
        ℙ_{M}[(contractPick pick (ksTarget p.1.verts.card) p.1 p.2 >>=
            fun q => kargerSteinAux pick fuel q : M _) ∈
          {o | o.2 = p.1.minCutValue}] := by
      refine le_prob_toPMF_bind h1 ?_
      intro q hqgood hqsupp
      obtain ⟨hwf'', hcard2'', -, hcase, -, -, ht''⟩ :=
        support_contractPick (M := M) hfresh g₀ (ksTarget p.1.verts.card)
          (ksTarget_two_le _) p.1 p.2 hwf (ksTarget_lt h4).le ht q hqsupp
      have hqmin : q.1.minCutValue = p.1.minCutValue := hqgood
      rcases hcase with hct | hnil
      · have hrec := ih q hwf'' (by omega) ht''
          (by rw [hct]; exact hdt)
        rw [hqmin, hct] at hrec
        exact hrec
      · -- Stalled on an edgeless graph: deterministic success.
        have h2' : 2 ≤ q.1.verts.card := le_trans ht2 hcard2''
        have hmin0 : q.1.minCutValue = 0 :=
          Nat.le_zero.mp (le_trans (minCutValue_le_length q.1 h2')
            (by simp [hnil]))
        have hsub := support_kargerSteinAux_edgeless (M := M) pick fuel q hnil
        refine le_trans ?_
          (prob_mono_of_support
            (p := inst.toPMF (kargerSteinAux pick fuel q : M _))
            (s := Set.univ) fun o ho _ => ?_)
        · rw [prob_univ]
          rw [ENNReal.div_le_iff
            (by exact_mod_cast (by omega :
              (ksDepth (ksTarget p.1.verts.card) + 3 : ℕ) ≠ 0))
            (ENNReal.natCast_ne_top _), one_mul]
          exact_mod_cast (by omega :
            (1 : ℕ) ≤ ksDepth (ksTarget p.1.verts.card) + 3)
        · rw [hsub o ho]
          show (0 : ℕ) = p.1.minCutValue
          rw [← hqmin, hmin0]
    -- One-sidedness of the branch, for the amplify composition.
    have hsupp : ∀ o ∈ 𝒟_{M}[(contractPick pick
          (ksTarget p.1.verts.card) p.1 p.2 >>=
          fun q => kargerSteinAux pick fuel q : M _)].support,
        p.1.minCutValue ≤ o.2 := by
      intro o ho
      obtain ⟨q, hq, ho'⟩ := mem_support_toPMF_bind.mp ho
      obtain ⟨hwf'', hcard'', -, -, -, hmin'', ht''⟩ :=
        support_contractPick (M := M) hfresh g₀ (ksTarget p.1.verts.card)
          (ksTarget_two_le _) p.1 p.2 hwf (ksTarget_lt h4).le ht q hq
      obtain ⟨-, -, hle'⟩ := support_kargerSteinAux hfresh fuel q hwf''
        (le_trans ht2 hcard'') ht'' o ho'
      exact le_trans hmin'' hle'
    have hamp := amplify_argmin_success (f := Prod.snd)
      (c := p.1.minCutValue) hsupp hp 2
    refine le_trans ?_ hamp
    -- The recurrence arithmetic: `1/(c+1) ≤ 1 − (1 − 1/(2c))²`
    -- with `c := ksDepth t + 3`.
    rw [hdd]
    obtain ⟨c', hc'⟩ : ∃ c', ksDepth (ksTarget p.1.verts.card) + 3 = c' + 3 :=
      ⟨ksDepth (ksTarget p.1.verts.card), rfl⟩
    rw [hc',
      show (1 + ksDepth (ksTarget p.1.verts.card) + 3 : ℕ) = c' + 3 + 1 by
        omega]
    have hp₀ : (1 : ℝ≥0∞) / 2 *
        (((1 : ℕ) : ℝ≥0∞) / ((c' + 3 : ℕ) : ℝ≥0∞)) =
        ((1 : ℕ) : ℝ≥0∞) / ((2 * (c' + 3) : ℕ) : ℝ≥0∞) := by
      have h := ennreal_natCast_div_mul_div 1 2 1 (c' + 3) (by norm_num)
      rw [show (1 * 1 : ℕ) = 1 by norm_num] at h
      exact_mod_cast h
    rw [hp₀,
      ennreal_one_sub_inv_natCast (by omega : 0 < 2 * (c' + 3)), sq,
      ennreal_natCast_div_mul_div _ _ _ _ (by omega)]
    refine ENNReal.le_sub_of_add_le_right
      ((ENNReal.div_lt_top (ENNReal.natCast_ne_top _)
        (by exact_mod_cast (by positivity :
          (2 * (c' + 3) * (2 * (c' + 3)) : ℕ) ≠ 0))).ne) ?_
    calc ((1 : ℕ) : ℝ≥0∞) / ((c' + 3 + 1 : ℕ) : ℝ≥0∞) +
          (((2 * (c' + 3) - 1) * (2 * (c' + 3) - 1) : ℕ) : ℝ≥0∞) /
            ((2 * (c' + 3) * (2 * (c' + 3)) : ℕ) : ℝ≥0∞)
        ≤ ((1 : ℕ) : ℝ≥0∞) / ((c' + 3 + 1 : ℕ) : ℝ≥0∞) +
          ((c' + 3 : ℕ) : ℝ≥0∞) / ((c' + 3 + 1 : ℕ) : ℝ≥0∞) := by
          refine add_le_add le_rfl (ennreal_div_le_div_nat
            (Nat.mul_pos (by omega) (by omega)) (by omega) ?_)
          rw [show 2 * (c' + 3) - 1 = 2 * c' + 5 by omega]
          nlinarith
      _ = 1 := by
          rw [ENNReal.div_add_div_same,
            show ((1 : ℕ) : ℝ≥0∞) + ((c' + 3 : ℕ) : ℝ≥0∞) =
              ((c' + 3 + 1 : ℕ) : ℝ≥0∞) by push_cast; ring]
          exact ENNReal.div_self (by exact_mod_cast (by omega :
            (c' + 3 + 1 : ℕ) ≠ 0)) (ENNReal.natCast_ne_top _)
  | case3 fuel p h4 =>
    intro hwf h2 ht _
    rw [kargerSteinAux.eq_2, if_neg h4, ksDepth_of_lt h4]
    exact success_ksLeaf_small hfresh hwf h2 (by omega) ht

/-! ## Main theorems -/

/-- One-sided error. Every output of Karger–Stein is a partition
of `g` into genuine cuts of the reported value, and the reported value
never undershoots the minimum. -/
theorem kargerStein_isCut
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟_{M}[KargerStein pick g].support,
      (∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2) ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  obtain ⟨hcut, hle, -⟩ := support_kargerSteinAux (M := M) hfresh
    (ksDepth g.verts.card) (g, fun a => {a}) hwf h2 (PickTracks.init g) o ho
  exact ⟨hcut, hle⟩

/-- Karger–Stein reports the minimum-cut value with probability at
least `1/(ksDepth n + 3)`, and with `ksDepth n ≈ 2 log₂ n` this is an
exponential improvement over a single run's `2/(n(n−1))`. -/
theorem kargerStein_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    ((1 : ℕ) : ℝ≥0∞) / ((ksDepth g.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerStein pick g ∈ {o | o.2 = g.minCutValue}] := by
  exact success_kargerSteinAux (M := M) hfresh (ksDepth g.verts.card)
    (g, fun a => {a}) hwf h2 (PickTracks.init g) le_rfl

/-- The Karger–Stein theorem. A single run returns an actual
minimum cut (every reported side is a genuine cut of value
exactly `minCutValue`) with probability at least
`1/(ksDepth n + 3)`. -/
theorem kargerStein_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF)
    (h2 : 2 ≤ g.verts.card) :
    ((1 : ℕ) : ℝ≥0∞) / ((ksDepth g.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerStein pick g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue}] := by
  refine le_trans (kargerStein_success_prob hfresh g hwf h2)
    (prob_mono_of_support fun o ho hval => ?_)
  obtain ⟨hall, -⟩ := kargerStein_isCut hfresh g hwf h2 o ho
  exact fun S hS => ⟨(hall S hS).1, (hall S hS).2.trans hval⟩

/-! ## Complexity

The interim bound of `KargerStein.md` §5: each of the `≤ 2^(fuel+1)`
tree nodes runs a contraction pass of at most `n` rounds costing at
most `m` each (edge counts and vertex counts never increase down a
path, which is where well-formedness and freshness enter, as in the
fuel-free Karger bound). The level-sum refinement to `7 n² m` is
future work. -/

private lemma cost_kargerSteinAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {g₀ : MultiGraph α} {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) :
    ∀ fuel (p : MultiGraph α × (α → Finset α)), p.1.WF →
      PickTracks g₀ p.1 p.2 →
      𝔼_{M}[cost (kargerSteinAux pick fuel p :
          TimeMT ℕ M (Finset (Finset α) × ℕ))] ≤
        ((2 ^ (fuel + 2) - 2 : ℕ) : ℝ≥0∞) *
          ((p.1.verts.card * p.1.edges.length : ℕ) : ℝ≥0∞) := by
  intro fuel p
  induction fuel, p using kargerSteinAux.induct with
  | case1 p =>
    intro hwf _
    rw [kargerSteinAux.eq_1, expected_cost_toPMF_bind_pure]
    refine le_trans (expected_cost_contractPick hfresh 2 p.1 p.2 hwf) ?_
    have hnat : (p.1.verts.card - 2) * p.1.edges.length ≤
        (2 ^ (0 + 2) - 2) * (p.1.verts.card * p.1.edges.length) := by
      calc (p.1.verts.card - 2) * p.1.edges.length
          ≤ p.1.verts.card * p.1.edges.length :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 ^ (0 + 2) - 2) * (p.1.verts.card * p.1.edges.length) :=
            Nat.le_mul_of_pos_left _ (by norm_num)
    exact_mod_cast hnat
  | case2 fuel p h4 ih =>
    intro hwf ht
    have h2 : (2 : ℕ) ≤ 2 ^ (fuel + 2) := Nat.le_self_pow (by omega) 2
    rw [kargerSteinAux.eq_2, if_pos h4, show (2 : ℕ) = 1 + 1 from by norm_num,
      expected_cost_amplify]
    have hbr : 𝔼[cost (contractPick pick
          (ksTarget p.1.verts.card) p.1 p.2 >>=
          fun q => kargerSteinAux pick fuel q :
            TimeMT ℕ M (Finset (Finset α) × ℕ))] ≤
        ((2 ^ (fuel + 2) - 1 : ℕ) : ℝ≥0∞) *
          ((p.1.verts.card * p.1.edges.length : ℕ) : ℝ≥0∞) := by
      refine le_trans (expected_cost_toPMF_bind_le
        (c := ((2 ^ (fuel + 2) - 2 : ℕ) : ℝ≥0∞) *
          ((p.1.verts.card * p.1.edges.length : ℕ) : ℝ≥0∞)) ?_) ?_
      · intro tm htm
        have hret := mem_support_timedPMF (inst := inst) htm
        obtain ⟨hwf'', -, hcardle'', -, hlen'', -, ht''⟩ :=
          support_contractPick (M := TimeMT ℕ M) hfresh g₀
            (ksTarget p.1.verts.card) (ksTarget_two_le _) p.1 p.2 hwf
            (ksTarget_lt h4).le ht tm.ret hret
        refine le_trans (ih tm.ret hwf'' ht'') ?_
        exact mul_le_mul' le_rfl
          (by exact_mod_cast Nat.mul_le_mul hcardle'' hlen'')
      · refine le_trans (add_le_add
          (expected_cost_contractPick hfresh (ksTarget p.1.verts.card) p.1 p.2 hwf)
          le_rfl) ?_
        have hnat : (p.1.verts.card - ksTarget p.1.verts.card) *
            p.1.edges.length +
            (2 ^ (fuel + 2) - 2) * (p.1.verts.card * p.1.edges.length) ≤
            (2 ^ (fuel + 2) - 1) * (p.1.verts.card * p.1.edges.length) := by
          have h1 : (p.1.verts.card - ksTarget p.1.verts.card) *
              p.1.edges.length ≤ p.1.verts.card * p.1.edges.length :=
            Nat.mul_le_mul_right _ (by omega)
          rw [show (2 ^ (fuel + 2) - 1) = (2 ^ (fuel + 2) - 2) + 1 by omega,
            Nat.add_mul, one_mul, Nat.add_comm
              ((p.1.verts.card - ksTarget p.1.verts.card) * p.1.edges.length)]
          exact Nat.add_le_add_left h1 _
        exact_mod_cast hnat
    refine le_trans (mul_le_mul' le_rfl hbr) ?_
    have hpow : (2 : ℕ) ^ (fuel + 1 + 2) = 2 ^ (fuel + 2) * 2 := by
      rw [pow_succ]
    have hnat : 2 * ((2 ^ (fuel + 2) - 1) *
        (p.1.verts.card * p.1.edges.length)) ≤
        (2 ^ (fuel + 1 + 2) - 2) * (p.1.verts.card * p.1.edges.length) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    calc (((1 : ℕ) : ℝ≥0∞) + 1) * (((2 ^ (fuel + 2) - 1 : ℕ) : ℝ≥0∞) *
          ((p.1.verts.card * p.1.edges.length : ℕ) : ℝ≥0∞))
        = ((2 * ((2 ^ (fuel + 2) - 1) *
            (p.1.verts.card * p.1.edges.length)) : ℕ) : ℝ≥0∞) := by
          push_cast
          ring
      _ ≤ ((2 ^ (fuel + 1 + 2) - 2 : ℕ) : ℝ≥0∞) *
            ((p.1.verts.card * p.1.edges.length : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hnat
  | case3 fuel p h4 =>
    intro hwf _
    rw [kargerSteinAux.eq_2, if_neg h4, expected_cost_toPMF_bind_pure]
    refine le_trans (expected_cost_contractPick hfresh 2 p.1 p.2 hwf) ?_
    have hpos : 0 < 2 ^ (fuel + 1 + 2) - 2 := by
      have : (4 : ℕ) ≤ 2 ^ (fuel + 1 + 2) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (fuel + 1 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hnat : (p.1.verts.card - 2) * p.1.edges.length ≤
        (2 ^ (fuel + 1 + 2) - 2) * (p.1.verts.card * p.1.edges.length) := by
      calc (p.1.verts.card - 2) * p.1.edges.length
          ≤ p.1.verts.card * p.1.edges.length :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 ^ (fuel + 1 + 2) - 2) * (p.1.verts.card * p.1.edges.length) :=
            Nat.le_mul_of_pos_left _ hpos
    exact_mod_cast hnat

/-- Expected cost of Karger–Stein (interim bound, edge-list model):
at most `(2^(d+2) − 2)·n·m` where `d = ksDepth n`. Needs `WF` and
freshness, like the fuel-free Karger cost bound: the recursion's cost
is controlled by the run invariant. -/
theorem kargerStein_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {pick : MultiGraph α → Sym2 α → α}
    (hfresh : Fresh pick) (g : MultiGraph α) (hwf : g.WF) :
    𝔼_{M}[cost KargerStein pick g] ≤
      ((2 ^ (ksDepth g.verts.card + 2) - 2 : ℕ) : ℝ≥0∞) *
        ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞) := by
  unfold KargerStein
  exact cost_kargerSteinAux (g₀ := g) hfresh (ksDepth g.verts.card)
    (g, fun a => {a}) hwf (PickTracks.init g)

end ARA
