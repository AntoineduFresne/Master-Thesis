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
risky. Karger–Stein contracts down to `ksTarget n ≈ n/√2` supervertices
— which preserves the minimum cut with probability `≥ 1/2`, by the
*definition* of `ksTarget` — and spends the repetition budget on the
risky small graphs by recursing twice and keeping the better answer.

## Main results

* `kargerStein_finds_min` — a run returns an actual **minimum cut**
  with probability at least `1 / (ksDepth n + 3)`, where `ksDepth n`
  is the recursion depth (`≈ 2·log₂ n`; the `⌈log⌉` form of the bound
  is stated in `KargerStein.md` §6).
* `kargerStein_isCut` — one-sided error: every output is a partition
  into genuine cuts of the reported value, never undershooting.
* `kargerStein_cost_le` — expected cost at most `(2^(d+2) − 2)·n·m` in
  the edge-list cost model (the interim bound of `KargerStein.md` §5;
  the level-sum `7n²m` refinement is future work).

## Architecture

The recursion operates directly on the supervertex graphs of
`ARA.Helpers.MultiGraph` — contraction preserves the vertex type, so
no re-lifting is ever needed — and consumes Karger's shared kernel:
`contractAux` (the loop), `success_contractAux` (survival of the
minimum cut through partial contraction) and `support_contractAux`
(the run invariant), together with the `amplify` layer for the
best-of-two composition. The recursion is fueled by `ksDepth`, so
termination is structural; the analysis shows the fuel is exactly
sufficient.
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
probability `t(t−1)/(n(n−1))` of a fixed minimum cut reaches `1/2` —
classically `⌈1 + n/√2⌉`, characterized integrally (no `√2`). -/
def ksTarget (n : ℕ) : ℕ := Nat.find (ksTarget_exists n)

lemma ksTarget_two_le (n : ℕ) : 2 ≤ ksTarget n :=
  (Nat.find_spec (ksTarget_exists n)).1

/-- The defining inequality: contracting to `ksTarget n` supervertices
keeps the survival probability at least `1/2`. -/
lemma ksTarget_bound (n : ℕ) :
    n * (n - 1) ≤ 2 * (ksTarget n * (ksTarget n - 1)) :=
  (Nat.find_spec (ksTarget_exists n)).2

/-- The target genuinely shrinks the graph — exactly from `n = 4` on,
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

/-- One fueled round of Karger–Stein: on `≤ 3` supervertices (or on
exhausted fuel) contract fully and report; otherwise, twice and
independently, contract down to `ksTarget n` supervertices and
recurse, keeping the output with the smaller reported value. -/
def kargerSteinAux {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    ℕ → MultiGraph (Finset α) → M (Finset (Finset α) × ℕ)
  | 0, g => do
      let h ← contractAux (g.verts.card - 2) g
      pure (h.verts, h.edges.length)
  | fuel + 1, g =>
      if 4 ≤ g.verts.card then
        amplify (argmin Prod.snd) 2
          (contractAux (g.verts.card - ksTarget g.verts.card) g >>=
            fun h => kargerSteinAux fuel h)
      else do
        let h ← contractAux (g.verts.card - 2) g
        pure (h.verts, h.edges.length)

/-- **The Karger–Stein algorithm**: recursive contraction with fuel
`ksDepth n` (exactly the recursion depth), on the supervertex lift. -/
def KargerStein {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (g : MultiGraph α) : M (Finset (Finset α) × ℕ) :=
  kargerSteinAux (ksDepth g.verts.card) g.super

-- IO version (executable)
def KargerStein_IO : MultiGraph ℕ → IO (Finset (Finset ℕ) × ℕ) := KargerStein

#eval KargerStein_IO kargerDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph ℕ → PMF (Finset (Finset ℕ) × ℕ) := KargerStein

/-! ## The leaf: a full contraction run

Both the base case and the small-graph case run Karger's body; its
guarantees restate Karger's, one supervertex level down. -/

private lemma support_ksLeaf
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {g : MultiGraph (Finset α)} (hwf : g.WF) (h2 : 2 ≤ g.verts.card)
    (ht : Tracks g₀ g) :
    ∀ o ∈ 𝒟[(contractAux (g.verts.card - 2) g >>= fun h =>
        pure (h.verts, h.edges.length) : M (Finset (Finset α) × ℕ))].support,
      (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
        g₀.minCutValue ≤ o.2 ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  obtain ⟨h, hh, rfl⟩ := mem_support_toPMF_bind_pure.mp ho
  obtain ⟨hwf', h2', -, hend, -, hmin, ht'⟩ :=
    support_contractAux (M := M) 2 le_rfl (g.verts.card - 2) g hwf
      (by omega) ht h hh
  refine ⟨fun S hS => ⟨ht'.isCut_mem h2' hS, ht'.cutValue_mem hwf' hend hS⟩,
    ?_, ?_⟩
  · obtain ⟨S, hS⟩ := Finset.card_pos.mp (by omega : 0 < h.verts.card)
    rw [← ht'.cutValue_mem hwf' hend hS]
    exact minCutValue_le (ht'.isCut_mem h2' hS)
  · exact le_trans hmin (minCutValue_le_length h h2')

private lemma success_ksLeaf
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α}
    {g : MultiGraph (Finset α)} (hwf : g.WF) (h2 : 2 ≤ g.verts.card)
    (ht : Tracks g₀ g) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ[(contractAux (g.verts.card - 2) g >>= fun h =>
          pure (h.verts, h.edges.length) : M (Finset (Finset α) × ℕ))
        ∈ {o | o.2 = g.minCutValue}] := by
  have hmain := success_contractAux (M := M) (s := 0) (g.verts.card - 2) g
    hwf ht.disj (by omega)
  rw [show ((0 + 2) * (0 + 1) : ℕ) = 2 by norm_num,
    show g.verts.card - 2 + 0 + 2 = g.verts.card by omega,
    show g.verts.card - 2 + 0 + 1 = g.verts.card - 1 by omega] at hmain
  rw [show (contractAux (g.verts.card - 2) g >>= fun h =>
        pure (h.verts, h.edges.length) : M (Finset (Finset α) × ℕ)) =
      (fun h => (h.verts, h.edges.length)) <$>
        contractAux (g.verts.card - 2) g from by
    rw [map_eq_bind_pure_comp]; rfl]
  rw [LawfulRandMonad.toPMF_map, pmf_map_eq, prob_map]
  refine le_trans (by exact_mod_cast hmain)
    (prob_mono_of_support fun h hh hev => ?_)
  obtain ⟨hwf', h2', -, hend, -, -, -⟩ :=
    support_contractAux (M := M) 2 le_rfl (g.verts.card - 2) g hwf
      (by omega) ht h hh
  show h.edges.length = g.minCutValue
  rcases hend with hcard2 | hnil
  · exact (length_eq_minCutValue_of_card_two hwf' hcard2).trans hev
  · have hlen : h.edges.length = 0 := by rw [hnil]; rfl
    have hmin0 : h.minCutValue = 0 :=
      Nat.le_zero.mp (le_trans (minCutValue_le_length h h2') (le_of_eq hlen))
    rw [hlen, ← hev, hmin0]

/-! ## Degenerate graphs: no edges left -/

private lemma contractAux_edgeless {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    {g : MultiGraph (Finset α)} (hnil : g.edges = []) :
    ∀ k, (contractAux k g : M (MultiGraph (Finset α))) = pure g
  | 0 => rfl
  | k + 1 => by
      rw [contractAux.eq_2, dif_neg (by simp [hnil])]

private lemma support_kargerSteinAux_edgeless
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] :
    ∀ fuel (g : MultiGraph (Finset α)), g.edges = [] →
      ∀ o ∈ 𝒟[kargerSteinAux fuel g | M].support, o = (g.verts, 0) := by
  intro fuel g
  induction fuel, g using kargerSteinAux.induct with
  | case1 g =>
    intro hnil o ho
    rw [kargerSteinAux.eq_1, contractAux_edgeless hnil, pure_bind] at ho
    toPMF_step at ho
    rw [ho, hnil]
    rfl
  | case2 fuel g h4 ih =>
    intro hnil o ho
    rw [kargerSteinAux.eq_2, if_pos h4, contractAux_edgeless hnil,
      pure_bind] at ho
    exact support_amplify_subset (V := {o | o = (g.verts, 0)}) (ih g hnil)
      (fun a ha b hb => by
        unfold argmin
        split_ifs
        exacts [ha, hb]) 2 ho
  | case3 fuel g h4 =>
    intro hnil o ho
    rw [kargerSteinAux.eq_2, if_neg h4, contractAux_edgeless hnil,
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
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α} :
    ∀ fuel (g : MultiGraph (Finset α)), g.WF → 2 ≤ g.verts.card →
      Tracks g₀ g →
      ∀ o ∈ 𝒟[kargerSteinAux fuel g | M].support,
        (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
          g₀.minCutValue ≤ o.2 ∧ g.minCutValue ≤ o.2 := by
  intro fuel g
  induction fuel, g using kargerSteinAux.induct with
  | case1 g =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_1] at ho
    exact support_ksLeaf hwf h2 ht o ho
  | case2 fuel g h4 ih =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_2] at ho
    · rw [if_pos h4] at ho
      refine support_amplify_subset
        (V := {o | (∀ S ∈ o.1, g₀.IsCut S ∧ g₀.cutValue S = o.2) ∧
          g₀.minCutValue ≤ o.2 ∧ g.minCutValue ≤ o.2}) ?_ ?_ 2 ho
      · intro o' ho'
        obtain ⟨g', hg', ho''⟩ := mem_support_toPMF_bind.mp ho'
        obtain ⟨hwf'', hcard'', -, -, -, hmin'', ht''⟩ :=
          support_contractAux (M := M) (ksTarget g.verts.card)
            (ksTarget_two_le _) (g.verts.card - ksTarget g.verts.card) g hwf
            (by have := ksTarget_lt h4; omega) ht g' hg'
        obtain ⟨hcut, hle₀, hle'⟩ := ih g' hwf''
          (le_trans (ksTarget_two_le _) hcard'') ht'' o' ho''
        exact ⟨hcut, hle₀, le_trans hmin'' hle'⟩
      · intro a ha b hb
        unfold argmin
        split_ifs
        exacts [ha, hb]
  | case3 fuel g h4 =>
    intro hwf h2 ht o ho
    rw [kargerSteinAux.eq_2, if_neg h4] at ho
    exact support_ksLeaf hwf h2 ht o ho

/-! ## Success probability -/

/-- The two ℕ-fraction facts of the recurrence, packaged: a product of
two casts of ℕ-fractions is the cast of the product fraction. -/
private lemma ennreal_natCast_div_mul_div (a b c d : ℕ)
    (hb : b ≠ 0) (_hd : d ≠ 0) :
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
  have hsum : ((c - 1 : ℕ) : ℝ≥0∞) / ((c : ℕ) : ℝ≥0∞) +
      ((1 : ℕ) : ℝ≥0∞) / ((c : ℕ) : ℝ≥0∞) = 1 := by
    rw [ENNReal.div_add_div_same,
      show ((c - 1 : ℕ) : ℝ≥0∞) + ((1 : ℕ) : ℝ≥0∞) = ((c : ℕ) : ℝ≥0∞) by
        rw [← Nat.cast_add]; congr 1; omega]
    exact ENNReal.div_self (by exact_mod_cast hc.ne') (ENNReal.natCast_ne_top _)
  exact (ENNReal.eq_sub_of_add_eq
    ((ENNReal.div_lt_top (by simp) (by exact_mod_cast hc.ne')).ne) hsum).symm

/-- **Success of a fueled run**: with fuel at least the recursion
depth, a run reports the current minimum-cut value with probability at
least `1/(ksDepth n + 3)`. -/
private theorem success_kargerSteinAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] {g₀ : MultiGraph α} :
    ∀ fuel (g : MultiGraph (Finset α)), g.WF → Tracks g₀ g →
      2 ≤ g.verts.card → ksDepth g.verts.card ≤ fuel →
      ((1 : ℕ) : ℝ≥0∞) / ((ksDepth g.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
        ℙ[kargerSteinAux fuel g ∈ {o | o.2 = g.minCutValue} | M] := by
  intro fuel g
  induction fuel, g using kargerSteinAux.induct with
  | case1 g =>
    intro hwf ht h2 hdepth
    have hd0 : ksDepth g.verts.card = 0 := Nat.le_zero.mp hdepth
    have h3 : g.verts.card ≤ 3 := by
      by_contra hc
      rw [ksDepth_of_ge (by omega)] at hd0
      omega
    rw [kargerSteinAux.eq_1, hd0]
    refine le_trans ?_ (success_ksLeaf hwf h2 ht)
    have h6 : g.verts.card * (g.verts.card - 1) ≤ 6 := by
      rcases (by omega : g.verts.card = 2 ∨ g.verts.card = 3) with h | h <;> simp [h]
    exact_mod_cast ennreal_div_le_div_nat (a := 1) (b := 0 + 3) (c := 2)
      (d := g.verts.card * (g.verts.card - 1)) (by norm_num)
      (Nat.mul_pos (by omega) (by omega)) (by simpa using h6)
  | case2 fuel g h4 ih =>
    intro hwf ht h2 hdepth
    rw [kargerSteinAux.eq_2]
    · rw [if_pos h4]
      have ht2 := ksTarget_two_le g.verts.card
      have htlt := ksTarget_lt h4
      have hdd : ksDepth g.verts.card = 1 + ksDepth (ksTarget g.verts.card) :=
        ksDepth_of_ge h4
      have hdt : ksDepth (ksTarget g.verts.card) ≤ fuel := by omega
      -- Survival to `t = ksTarget n` supervertices happens with
      -- probability at least `1/2`, by the definition of the target.
      have hsurv := success_contractAux (M := M) (s := ksTarget g.verts.card - 2)
        (g.verts.card - ksTarget g.verts.card) g hwf ht.disj (by omega)
      rw [show ksTarget g.verts.card - 2 + 2 = ksTarget g.verts.card by omega,
        show ksTarget g.verts.card - 2 + 1 = ksTarget g.verts.card - 1 by omega,
        show g.verts.card - ksTarget g.verts.card +
            (ksTarget g.verts.card - 2) + 2 = g.verts.card by omega,
        show g.verts.card - ksTarget g.verts.card +
            (ksTarget g.verts.card - 2) + 1 = g.verts.card - 1 by omega] at hsurv
      have h1 : (1 : ℝ≥0∞) / 2 ≤
          prob (inst.toPMF (contractAux
              (g.verts.card - ksTarget g.verts.card) g : M _))
            {h | h.minCutValue = g.minCutValue} := by
        refine le_trans ?_ hsurv
        exact_mod_cast ennreal_div_le_div_nat (a := 1) (b := 2)
          (c := ksTarget g.verts.card * (ksTarget g.verts.card - 1))
          (d := g.verts.card * (g.verts.card - 1)) (by norm_num)
          (Nat.mul_pos (by omega) (by omega))
          (by have := ksTarget_bound g.verts.card; nlinarith)
      -- Each branch: survive, then recurse.
      have hp : (1 : ℝ≥0∞) / 2 *
          (((1 : ℕ) : ℝ≥0∞) /
            ((ksDepth (ksTarget g.verts.card) + 3 : ℕ) : ℝ≥0∞)) ≤
          ℙ[(contractAux (g.verts.card - ksTarget g.verts.card) g >>=
              kargerSteinAux fuel : M _) ∈ {o | o.2 = g.minCutValue}] := by
        refine le_prob_toPMF_bind h1 ?_
        intro g' hg'good hg'supp
        obtain ⟨hwf'', hcard2'', -, hcase, -, -, ht''⟩ :=
          support_contractAux (M := M) (ksTarget g.verts.card) ht2
            (g.verts.card - ksTarget g.verts.card) g hwf (by omega) ht g' hg'supp
        have hg'min : g'.minCutValue = g.minCutValue := hg'good
        rcases hcase with hct | hnil
        · have hrec := ih g' hwf'' ht'' (by omega)
            (by rw [hct]; exact hdt)
          rw [hg'min, hct] at hrec
          exact hrec
        · -- Stalled on an edgeless graph: deterministic success.
          have h2' : 2 ≤ g'.verts.card := le_trans ht2 hcard2''
          have hmin0 : g'.minCutValue = 0 :=
            Nat.le_zero.mp (le_trans (minCutValue_le_length g' h2')
              (by simp [hnil]))
          have hsub := support_kargerSteinAux_edgeless (M := M) fuel g' hnil
          refine le_trans ?_
            (prob_mono_of_support
              (p := inst.toPMF (kargerSteinAux fuel g' : M _))
              (s := Set.univ) fun o ho _ => ?_)
          · rw [prob_univ]
            rw [ENNReal.div_le_iff
              (by exact_mod_cast (by omega :
                (ksDepth (ksTarget g.verts.card) + 3 : ℕ) ≠ 0))
              (ENNReal.natCast_ne_top _), one_mul]
            exact_mod_cast (by omega :
              (1 : ℕ) ≤ ksDepth (ksTarget g.verts.card) + 3)
          · rw [hsub o ho]
            show (0 : ℕ) = g.minCutValue
            rw [← hg'min, hmin0]
      -- One-sidedness of the branch, for the amplify composition.
      have hsupp : ∀ o ∈ 𝒟[(contractAux
            (g.verts.card - ksTarget g.verts.card) g >>=
            kargerSteinAux fuel : M _)].support,
          g.minCutValue ≤ o.2 := by
        intro o ho
        obtain ⟨g', hg', ho'⟩ := mem_support_toPMF_bind.mp ho
        obtain ⟨hwf'', hcard'', -, -, -, hmin'', ht''⟩ :=
          support_contractAux (M := M) (ksTarget g.verts.card) ht2
            (g.verts.card - ksTarget g.verts.card) g hwf (by omega) ht g' hg'
        obtain ⟨-, -, hle'⟩ := support_kargerSteinAux fuel g' hwf''
          (le_trans ht2 hcard'') ht'' o ho'
        exact le_trans hmin'' hle'
      have hamp := amplify_argmin_success (f := Prod.snd)
        (c := g.minCutValue) hsupp hp 2
      refine le_trans ?_ hamp
      -- The recurrence arithmetic: `1/(c+1) ≤ 1 − (1 − 1/(2c))²`
      -- with `c := ksDepth t + 3`.
      rw [hdd]
      obtain ⟨c', hc'⟩ : ∃ c', ksDepth (ksTarget g.verts.card) + 3 = c' + 3 :=
        ⟨ksDepth (ksTarget g.verts.card), rfl⟩
      rw [hc',
        show (1 + ksDepth (ksTarget g.verts.card) + 3 : ℕ) = c' + 3 + 1 by
          omega]
      have hp₀ : (1 : ℝ≥0∞) / 2 *
          (((1 : ℕ) : ℝ≥0∞) / ((c' + 3 : ℕ) : ℝ≥0∞)) =
          ((1 : ℕ) : ℝ≥0∞) / ((2 * (c' + 3) : ℕ) : ℝ≥0∞) := by
        have h := ennreal_natCast_div_mul_div 1 2 1 (c' + 3)
          (by norm_num) (by omega)
        rw [show (1 * 1 : ℕ) = 1 by norm_num] at h
        exact_mod_cast h
      rw [hp₀,
        ennreal_one_sub_inv_natCast (by omega : 0 < 2 * (c' + 3)), sq,
        ennreal_natCast_div_mul_div _ _ _ _ (by omega) (by omega)]
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
  | case3 fuel g h4 =>
    intro hwf ht h2 _
    rw [kargerSteinAux.eq_2]
    · rw [if_neg h4]
      have hd0 : ksDepth g.verts.card = 0 := ksDepth_of_lt h4
      rw [hd0]
      have h3 : g.verts.card ≤ 3 := by omega
      refine le_trans ?_ (success_ksLeaf hwf h2 ht)
      have h6 : g.verts.card * (g.verts.card - 1) ≤ 6 := by
        rcases (by omega : g.verts.card = 2 ∨ g.verts.card = 3) with h | h <;> simp [h]
      exact_mod_cast ennreal_div_le_div_nat (a := 1) (b := 0 + 3) (c := 2)
        (d := g.verts.card * (g.verts.card - 1)) (by norm_num)
        (Nat.mul_pos (by omega) (by omega)) (by simpa using h6)

/-! ## Main theorems -/

/-- **One-sided error.** Every output of Karger–Stein is a partition
of `g` into genuine cuts of the reported value, and the reported value
never undershoots the minimum. -/
theorem kargerStein_isCut
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ o ∈ 𝒟[KargerStein g | M].support,
      (∀ S ∈ o.1, g.IsCut S ∧ g.cutValue S = o.2) ∧ g.minCutValue ≤ o.2 := by
  intro o ho
  obtain ⟨hcut, hle, -⟩ := support_kargerSteinAux (M := M)
    (ksDepth g.verts.card) g.super hwf.super
    (by rw [card_verts_super]; omega) (Tracks.super g) o ho
  exact ⟨hcut, hle⟩

/-- Karger–Stein reports the minimum-cut value with probability at
least `1/(ksDepth n + 3)` — with `ksDepth n ≈ 2 log₂ n`, an
exponential improvement over a single run's `2/(n(n−1))`. -/
theorem kargerStein_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ((1 : ℕ) : ℝ≥0∞) / ((ksDepth g.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
      ℙ[KargerStein g ∈ {o | o.2 = g.minCutValue} | M] := by
  have hmain := success_kargerSteinAux (M := M) (ksDepth g.verts.card) g.super
    hwf.super (Tracks.super g) (by rw [card_verts_super]; omega)
    (le_of_eq (congrArg ksDepth (card_verts_super g)))
  rw [minCutValue_super h2, card_verts_super] at hmain
  exact hmain

/-- **The Karger–Stein theorem.** A single run returns an actual
**minimum cut** — every reported side is a genuine cut of value
exactly `minCutValue` — with probability at least
`1/(ksDepth n + 3)`. -/
theorem kargerStein_finds_min
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ((1 : ℕ) : ℝ≥0∞) / ((ksDepth g.verts.card + 3 : ℕ) : ℝ≥0∞) ≤
      ℙ[KargerStein g ∈ {o | ∀ S ∈ o.1,
          g.IsCut S ∧ g.cutValue S = g.minCutValue} | M] := by
  refine le_trans (kargerStein_success_prob g hwf h2)
    (prob_mono_of_support fun o ho hval => ?_)
  obtain ⟨hall, -⟩ := kargerStein_isCut g hwf h2 o ho
  exact fun S hS => ⟨(hall S hS).1, (hall S hS).2.trans hval⟩

/-! ## Complexity

The interim bound of `KargerStein.md` §5: each of the `≤ 2^(fuel+1)`
tree nodes runs a contraction pass of at most `n` rounds costing at
most `m` each (edge counts and vertex counts never increase down a
path — this is where well-formedness enters, unlike Karger's bound).
The level-sum refinement to `7 n² m` is future work. -/

private lemma cost_kargerSteinAux
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {g₀ : MultiGraph α} :
    ∀ fuel (g : MultiGraph (Finset α)), g.WF → Tracks g₀ g →
      𝔼_runtime[(kargerSteinAux fuel g : TimeMT ℕ M (Finset (Finset α) × ℕ))] ≤
        ((2 ^ (fuel + 2) - 2 : ℕ) : ℝ≥0∞) *
          ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞) := by
  intro fuel g
  induction fuel, g using kargerSteinAux.induct with
  | case1 g =>
    intro hwf ht
    rw [kargerSteinAux.eq_1, expected_cost_toPMF_bind_pure]
    refine le_trans (expected_cost_contractAux _ g) ?_
    have hnat : (g.verts.card - 2) * g.edges.length ≤
        (2 ^ (0 + 2) - 2) * (g.verts.card * g.edges.length) := by
      calc (g.verts.card - 2) * g.edges.length
          ≤ g.verts.card * g.edges.length :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 ^ (0 + 2) - 2) * (g.verts.card * g.edges.length) :=
            Nat.le_mul_of_pos_left _ (by norm_num)
    exact_mod_cast hnat
  | case2 fuel g h4 ih =>
    intro hwf ht
    rw [kargerSteinAux.eq_2]
    · rw [if_pos h4, show (2 : ℕ) = 1 + 1 from by norm_num,
        expected_cost_amplify]
      have hbr : 𝔼_runtime[(contractAux
            (g.verts.card - ksTarget g.verts.card) g >>=
            kargerSteinAux fuel : TimeMT ℕ M (Finset (Finset α) × ℕ))] ≤
          ((2 ^ (fuel + 2) - 1 : ℕ) : ℝ≥0∞) *
            ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞) := by
        refine le_trans (expected_cost_toPMF_bind_le
          (c := ((2 ^ (fuel + 2) - 2 : ℕ) : ℝ≥0∞) *
            ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞)) ?_) ?_
        · intro tm htm
          have hret := mem_support_timedPMF (inst := inst) htm
          obtain ⟨hwf'', -, hcardle'', -, hlen'', -, ht''⟩ :=
            support_contractAux (M := TimeMT ℕ M) (ksTarget g.verts.card)
              (ksTarget_two_le _) (g.verts.card - ksTarget g.verts.card) g hwf
              (by have := ksTarget_lt h4; omega) ht tm.ret hret
          refine le_trans (ih tm.ret hwf'' ht'') ?_
          exact mul_le_mul' le_rfl
            (by exact_mod_cast Nat.mul_le_mul hcardle'' hlen'')
        · refine le_trans (add_le_add (expected_cost_contractAux _ g) le_rfl) ?_
          have hnat : (g.verts.card - ksTarget g.verts.card) * g.edges.length +
              (2 ^ (fuel + 2) - 2) * (g.verts.card * g.edges.length) ≤
              (2 ^ (fuel + 2) - 1) * (g.verts.card * g.edges.length) := by
            have h1 : (g.verts.card - ksTarget g.verts.card) * g.edges.length ≤
                g.verts.card * g.edges.length :=
              Nat.mul_le_mul_right _ (by omega)
            have h2 : (2 : ℕ) ≤ 2 ^ (fuel + 2) := by
              calc (2 : ℕ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (fuel + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            rw [show (2 ^ (fuel + 2) - 1) = (2 ^ (fuel + 2) - 2) + 1 by omega,
              Nat.add_mul, one_mul, Nat.add_comm
                ((g.verts.card - ksTarget g.verts.card) * g.edges.length)]
            exact Nat.add_le_add_left h1 _
          exact_mod_cast hnat
      refine le_trans (mul_le_mul' le_rfl hbr) ?_
      have hpow : (2 : ℕ) ^ (fuel + 1 + 2) = 2 ^ (fuel + 2) * 2 := by
        rw [pow_succ]
      have h2 : (2 : ℕ) ≤ 2 ^ (fuel + 2) := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (fuel + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hnat : 2 * ((2 ^ (fuel + 2) - 1) *
          (g.verts.card * g.edges.length)) ≤
          (2 ^ (fuel + 1 + 2) - 2) * (g.verts.card * g.edges.length) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      calc (((1 : ℕ) : ℝ≥0∞) + 1) * (((2 ^ (fuel + 2) - 1 : ℕ) : ℝ≥0∞) *
            ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞))
          = ((2 * ((2 ^ (fuel + 2) - 1) *
              (g.verts.card * g.edges.length)) : ℕ) : ℝ≥0∞) := by
            push_cast
            ring
        _ ≤ ((2 ^ (fuel + 1 + 2) - 2 : ℕ) : ℝ≥0∞) *
              ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hnat
  | case3 fuel g h4 =>
    intro _ _
    rw [kargerSteinAux.eq_2]
    · rw [if_neg h4, expected_cost_toPMF_bind_pure]
      refine le_trans (expected_cost_contractAux _ g) ?_
      have hpos : 0 < 2 ^ (fuel + 1 + 2) - 2 := by
        have : (4 : ℕ) ≤ 2 ^ (fuel + 1 + 2) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (fuel + 1 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hnat : (g.verts.card - 2) * g.edges.length ≤
          (2 ^ (fuel + 1 + 2) - 2) * (g.verts.card * g.edges.length) := by
        calc (g.verts.card - 2) * g.edges.length
            ≤ g.verts.card * g.edges.length :=
              Nat.mul_le_mul_right _ (by omega)
          _ ≤ (2 ^ (fuel + 1 + 2) - 2) * (g.verts.card * g.edges.length) :=
              Nat.le_mul_of_pos_left _ hpos
      exact_mod_cast hnat

/-- **Expected cost of Karger–Stein** (interim bound, edge-list model):
at most `(2^(d+2) − 2)·n·m` where `d = ksDepth n`. Needs `g.WF` —
unlike Karger's bound — because the recursion's cost is controlled by
the run invariant. -/
theorem kargerStein_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (g : MultiGraph α) (hwf : g.WF) :
    𝔼_runtime[KargerStein g | M] ≤
      ((2 ^ (ksDepth g.verts.card + 2) - 2 : ℕ) : ℝ≥0∞) *
        ((g.verts.card * g.edges.length : ℕ) : ℝ≥0∞) := by
  unfold KargerStein
  refine le_trans (cost_kargerSteinAux (g₀ := g) _ g.super hwf.super
    (Tracks.super g)) ?_
  rw [card_verts_super, length_edges_super]

end ARA
