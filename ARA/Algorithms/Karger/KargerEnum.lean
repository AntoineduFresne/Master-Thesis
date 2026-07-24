/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import ARA.Algorithms.Karger.KargerVariants

/-!
# Karger, enumeration model: the order is data, fixed at the start

Instead of demanding structure on the vertex type, take an injective
**labeling** `ℓ : α ↪ ℕ` as an input, once, and merge every drawn edge
into its endpoint of smaller label. The vertex type needs nothing
beyond `DecidableEq` — the demo below runs on an *unordered* type of
city names.

Two prices, both visible below:

* the labeling threads through **every statement** — the theorems are
  about `KargerEnum ℓ g` although neither the answer nor the bounds
  depend on `ℓ`;
* the merge is well-defined on the *unordered* edge only because `ℓ`
  is injective — a tie would make "the smaller-labeled endpoint"
  ill-defined (`enumPick`'s `Sym2.lift` obligation is exactly this).

This model also connects to edge orientation: a labeling orients every
edge (small label → large label), which is why treating the edges as
unordered was sound all along — cut values are orientation-invariant.
As with every rename model, the output is the cut *value* only.
-/

namespace ARA

open scoped ENNReal
open MultiGraph

variable {α : Type} [DecidableEq α]

/-- The endpoint of smaller label — well-defined on the unordered edge
*because* the labeling is injective: a tie forces the endpoints to be
equal. -/
def enumPick (ℓ : α ↪ ℕ) : Sym2 α → α :=
  Sym2.lift ⟨fun u v => if ℓ u ≤ ℓ v then u else v, fun u v => by
    show (if ℓ u ≤ ℓ v then u else v) = if ℓ v ≤ ℓ u then v else u
    rcases lt_trichotomy (ℓ u) (ℓ v) with h | h | h
    · rw [if_pos h.le, if_neg (not_le.mpr h)]
    · cases ℓ.injective h
      simp
    · rw [if_neg (not_le.mpr h), if_pos h.le]⟩

omit [DecidableEq α] in
/-- The pick is always one of the two endpoints. -/
lemma enumPick_mem (ℓ : α ↪ ℕ) (e : Sym2 α) : enumPick ℓ e ∈ e := by
  induction e with
  | _ u v =>
    show (if ℓ u ≤ ℓ v then u else v) ∈ s(u, v)
    split_ifs
    · exact Sym2.mem_mk_left u v
    · exact Sym2.mem_mk_right u v

/-- **The enumeration rule**: merge into the endpoint of smaller
label. Freshness is trivial — the pick is an endpoint. -/
def enumRule (ℓ : α ↪ ℕ) : MergeRule α where
  pick _ e := enumPick ℓ e
  fresh _ _ h := (Finset.mem_filter.mp h).2 (enumPick_mem _ _)

/-- Karger's algorithm under an upfront labeling. -/
def KargerEnum {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (ℓ : α ↪ ℕ) (g : MultiGraph α) : M ℕ :=
  KargerVia (enumRule ℓ) g

/-! ### Demo on an unordered vertex type

Six cities, no `LinearOrder` anywhere — the labeling is data. Same
shape as `kargerDemo`: two triangles joined by one bridge, minimum
cut `1`. -/

inductive City | zrh | gva | bsl | ber | lug | lau
  deriving DecidableEq

open City in
/-- An explicit injective labeling — data handed to the algorithm. -/
def cityLabel : City ↪ ℕ :=
  ⟨fun c => match c with
    | zrh => 0 | gva => 1 | bsl => 2 | ber => 3 | lug => 4 | lau => 5,
   fun a b h => by cases a <;> cases b <;> simp_all⟩

open City in
def cityDemo : MultiGraph City where
  verts := {zrh, gva, bsl, ber, lug, lau}
  edges := [s(zrh, gva), s(gva, bsl), s(bsl, zrh),
            s(ber, lug), s(lug, lau), s(lau, ber), s(bsl, ber)]

-- IO version (executable)
def KargerEnum_IO : MultiGraph City → IO ℕ := KargerEnum cityLabel

#eval KargerEnum_IO cityDemo

-- PMF version (noncomputable specification)
noncomputable example : MultiGraph City → PMF ℕ := KargerEnum cityLabel

/-- One-sided error: the reported value never undershoots the
minimum-cut value. (Note `ℓ` in the statement.) -/
theorem kargerEnum_value_ge
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    ∀ n ∈ 𝒟_{M}[KargerEnum ℓ g].support, g.minCutValue ≤ n :=
  kargerVia_value_ge (enumRule ℓ) g hwf h2

/-- A single run reports the minimum-cut value with probability at
least `2 / (n (n - 1))` — a bound that does not depend on `ℓ`, though
the statement must mention it. -/
theorem kargerEnum_success_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) :
    (2 : ℝ≥0∞) / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞) ≤
      ℙ_{M}[KargerEnum ℓ g ∈ {n | n = g.minCutValue}] :=
  kargerVia_success_prob (enumRule ℓ) g hwf h2

/-- Keeping the smallest of `k` reported values succeeds with
probability at least `1 − (1 − 2/(n(n−1)))^k`. -/
theorem kargerEnum_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) (hwf : g.WF) (h2 : 2 ≤ g.verts.card) (k : ℕ) :
    1 - (1 - 2 / ((g.verts.card * (g.verts.card - 1) : ℕ) : ℝ≥0∞)) ^ k ≤
      ℙ_{M}[amplify min k (KargerEnum ℓ g) = g.minCutValue] :=
  kargerVia_amplified (enumRule ℓ) g hwf h2 k

/-- Expected cost at most `(n - 2) * m` — one tick per edge scanned. -/
theorem kargerEnum_cost_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] (ℓ : α ↪ ℕ)
    (g : MultiGraph α) :
    𝔼_{M}[cost KargerEnum ℓ g] ≤
      ((g.verts.card - 2 : ℕ) : ℝ≥0∞) * (g.edges.length : ℝ≥0∞) :=
  kargerVia_cost_le (enumRule ℓ) g

end ARA
