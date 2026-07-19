/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.TailBounds
import ARA.Infrastructure.Correctness

/-!
# Amplification

Success amplification for Monte-Carlo algorithms: `amplify best k m`
runs `m` `k` times independently and combines the answers with `best`.
If a single run succeeds with probability at least `p`, and `best`
keeps a success when it sees one, the amplified run succeeds with
probability at least

```
1 − (1 − p) ^ k
```

so the failure probability decays geometrically in the number of runs
— the "repeat and keep the best" argument, proved once, inherited by
every Monte-Carlo algorithm (`karger_amplified` is the first client).

The hypotheses are phrased on an *invariant* set `V` containing the
support of one run — typically supplied by the algorithm's one-sided
correctness theorem ("every output is at least the minimum cut"):

* `hclosed` — `best` does not leave `V`;
* `hkeep` — on `V`, `best` returns a success as soon as either
  argument is one.

## Main declarations

* `amplify` — `k` independent runs combined with `best`
* `prob_singleton`, `prob_compl_eq_one_sub`, `prob_bind`, … —
  event-probability API extending `prob` from
  `ARA.Infrastructure.TailBounds`
* `support_amplify_subset` — one-sided correctness survives
  amplification
* `prob_amplify_compl_le` — the failure product `q ^ k`
* `amplify_success` — the amplification theorem `1 − (1 − p) ^ k`
* `amplify_min_success` / `amplify_max_success` — the ready-made form
  for one-sided algorithms on a linear order: the hypotheses are
  exactly the support and success theorems such an algorithm already
  provides
* `expected_cost_amplify` — `k + 1` runs cost `k + 1` times one run

Statements are phrased with the `ℙ[m ∈ S]` / `ℙ[m = v]` notation from
`ARA.Infrastructure.TailBounds`.
-/

namespace ARA

open Cslib.Algorithms.Lean
open scoped ENNReal

/-! ## The combinator -/

/-- `amplify best k m` — run `m` `k` times independently and combine
the answers with `best`. `k = 0` degenerates to a single run: a
probabilistic computation cannot produce "no output". -/
def amplify {M} [Monad M] {β : Type} (best : β → β → β) : ℕ → M β → M β
  | 0, m => m
  | 1, m => m
  | k + 2, m => do
      let a ← m
      let b ← amplify best (k + 1) m
      return best a b

@[simp] lemma amplify_zero {M} [Monad M] {β : Type} (best : β → β → β)
    (m : M β) : amplify best 0 m = m := rfl

@[simp] lemma amplify_one {M} [Monad M] {β : Type} (best : β → β → β)
    (m : M β) : amplify best 1 m = m := rfl

/-- Unfolding equation for the inductive step, stated in the
`k + 1 + 1` shape that `induction`/`cases` produce. -/
lemma amplify_succ_succ {M} [Monad M] {β : Type} (best : β → β → β)
    (k : ℕ) (m : M β) :
    amplify best (k + 1 + 1) m =
      m >>= fun a => amplify best (k + 1) m >>= fun b => pure (best a b) :=
  rfl

/-!
## Event-probability API

`prob` (from `ARA.Infrastructure.TailBounds`) with the lemmas an
amplification argument needs: singletons, complements, `bind`, `pure`.
-/

/-- The probability of a singleton event is the point probability. -/
@[simp] lemma prob_singleton {α : Type*} (p : PMF α) (a : α) :
    prob p {a} = p a := by
  unfold prob
  refine (tsum_eq_single a fun b hb => ?_).trans (Set.indicator_of_mem rfl ⇑p)
  exact Set.indicator_of_notMem (fun h : b ∈ ({a} : Set α) => hb h) ⇑p

/-- An event and its complement split the total mass. -/
lemma prob_add_compl {α : Type*} (p : PMF α) (s : Set α) :
    prob p s + prob p sᶜ = 1 := by
  unfold prob
  rw [← ENNReal.tsum_add,
    show ∑' a, (s.indicator (⇑p) a + sᶜ.indicator (⇑p) a) = ∑' a, p a from
      tsum_congr fun a => by
        by_cases h : a ∈ s
        · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h),
            add_zero]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h),
            zero_add]]
  exact p.tsum_coe

/-- Success probability via the failure probability. -/
lemma prob_eq_one_sub_compl {α : Type*} (p : PMF α) (s : Set α) :
    prob p s = 1 - prob p sᶜ :=
  ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one p sᶜ))
    (prob_add_compl p s)

/-- Failure probability via the success probability. -/
lemma prob_compl_eq_one_sub {α : Type*} (p : PMF α) (s : Set α) :
    prob p sᶜ = 1 - prob p s :=
  ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one p s))
    (by rw [add_comm]; exact prob_add_compl p s)

/-- Total probability through a `bind`. -/
lemma prob_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (s : Set β) :
    prob (p.bind f) s = ∑' a, p a * prob (f a) s := by
  unfold prob
  rw [show ∑' b, s.indicator (⇑(p.bind f)) b =
      ∑' b, ∑' a, p a * s.indicator (⇑(f a)) b from
    tsum_congr fun b => by
      by_cases hb : b ∈ s
      · rw [Set.indicator_of_mem hb, PMF.bind_apply]
        exact tsum_congr fun a => by rw [Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb]
        symm
        simp only [Set.indicator_of_notMem hb, mul_zero, tsum_zero],
    ENNReal.tsum_comm]
  exact tsum_congr fun a => ENNReal.tsum_mul_left

/-- A point mass assigns probability `1` to any event containing it. -/
lemma prob_pure_of_mem {α : Type*} {a : α} {s : Set α} (h : a ∈ s) :
    prob (PMF.pure a) s = 1 := by
  unfold prob
  rw [tsum_eq_single a fun b hb => ?_, Set.indicator_of_mem h,
    PMF.pure_apply, if_pos rfl]
  by_cases hb' : b ∈ s
  · rw [Set.indicator_of_mem hb', PMF.pure_apply, if_neg hb]
  · exact Set.indicator_of_notMem hb' _

/-- A point mass assigns probability `0` to any event avoiding it. -/
lemma prob_pure_of_notMem {α : Type*} {a : α} {s : Set α} (h : a ∉ s) :
    prob (PMF.pure a) s = 0 := by
  unfold prob
  rw [ENNReal.tsum_eq_zero]
  intro b
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb, PMF.pure_apply,
      if_neg (fun hba : b = a => h (hba ▸ hb))]
  · exact Set.indicator_of_notMem hb _

/-! ## The failure product -/

/-- **Two-run failure bound.** If (on the supports) a failure of the
combined answer `best a b` forces both runs to have failed, the failure
probability of the combined run is at most the product of the
individual failure probabilities. -/
lemma prob_bind_best_le {α β γ : Type*} (p : PMF α) (r : PMF β)
    (best : α → β → γ) {A : Set α} {B : Set β} {F : Set γ}
    (h : ∀ a ∈ p.support, ∀ b ∈ r.support, best a b ∈ F → a ∈ A ∧ b ∈ B) :
    prob (p.bind fun a => r.bind fun b => PMF.pure (best a b)) F ≤
      prob p A * prob r B := by
  rw [prob_bind]
  have hpt : ∀ a, p a * prob (r.bind fun b => PMF.pure (best a b)) F ≤
      A.indicator (⇑p) a * prob r B := by
    intro a
    by_cases ha : a ∈ p.support
    · rw [prob_bind]
      by_cases hA : a ∈ A
      · rw [Set.indicator_of_mem hA]
        refine mul_le_mul' le_rfl ?_
        show _ ≤ ∑' b, B.indicator (⇑r) b
        refine ENNReal.tsum_le_tsum fun b => ?_
        by_cases hb : b ∈ r.support
        · by_cases hB : b ∈ B
          · rw [Set.indicator_of_mem hB]
            exact le_trans (mul_le_mul' le_rfl (prob_le_one _ _))
              (le_of_eq (mul_one _))
          · rw [Set.indicator_of_notMem hB,
              prob_pure_of_notMem fun hF => hB (h a ha b hb hF).2, mul_zero]
        · rw [(PMF.apply_eq_zero_iff r b).mpr hb, zero_mul]
          exact zero_le
      · rw [Set.indicator_of_notMem hA, zero_mul,
          show (∑' b, r b * prob (PMF.pure (best a b)) F) = 0 from
            ENNReal.tsum_eq_zero.mpr fun b => by
              by_cases hb : b ∈ r.support
              · rw [prob_pure_of_notMem fun hF => hA (h a ha b hb hF).1, mul_zero]
              · rw [(PMF.apply_eq_zero_iff r b).mpr hb, zero_mul],
          mul_zero]
    · rw [(PMF.apply_eq_zero_iff p a).mpr ha, zero_mul]
      exact zero_le
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right]
  rfl

/-- One-sided correctness survives amplification: if every single-run
output lies in `V` and `best` does not leave `V`, every amplified
output lies in `V`. -/
lemma support_amplify_subset
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {V : Set β}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V) (k : ℕ) :
    (𝒟[amplify best k m]).support ⊆ V := by
  induction k with
  | zero => exact hsupp
  | succ k ih =>
    cases k with
    | zero => exact hsupp
    | succ k =>
      intro c hc
      rw [amplify_succ_succ, inst.toPMF_bind, pmf_bind_eq] at hc
      obtain ⟨a, ha, hc'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hc
      obtain ⟨b, hb, rfl⟩ := mem_support_toPMF_bind_pure.mp hc'
      exact hclosed a (hsupp ha) b (ih hb)

/-- **Failure product.** All `k` runs must fail for the amplified run
to fail, so the failure probability is at most the `k`-th power of the
single-run failure probability. -/
theorem prob_amplify_compl_le
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {S V : Set β}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V)
    (hkeep : ∀ a ∈ V, ∀ b ∈ V, a ∈ S ∨ b ∈ S → best a b ∈ S) (k : ℕ) :
    ℙ[amplify best k m ∈ Sᶜ] ≤ ℙ[m ∈ Sᶜ] ^ k := by
  induction k with
  | zero => rw [pow_zero]; exact prob_le_one _ _
  | succ k ih =>
    cases k with
    | zero => rw [zero_add, pow_one, amplify_one]
    | succ k =>
      rw [amplify_succ_succ]
      simp only [inst.toPMF_bind, inst.toPMF_pure, pmf_bind_eq, pmf_pure_eq]
      refine le_trans (prob_bind_best_le (𝒟[m]) (𝒟[amplify best (k + 1) m]) best
        (A := Sᶜ) (B := Sᶜ) (F := Sᶜ)
        fun a ha b hb hab =>
          ⟨fun haS => hab (hkeep a (hsupp ha) b
              (support_amplify_subset hsupp hclosed (k + 1) hb) (Or.inl haS)),
           fun hbS => hab (hkeep a (hsupp ha) b
              (support_amplify_subset hsupp hclosed (k + 1) hb) (Or.inr hbS))⟩)
        ?_
      exact le_trans (mul_le_mul' le_rfl ih) (le_of_eq (by ring))

/-- **The amplification theorem.** If one run of `m` succeeds — lands
in `S` — with probability at least `p`, then `k` independent runs
combined with a success-keeping `best` succeed with probability at
least `1 − (1 − p) ^ k`. -/
theorem amplify_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    {best : β → β → β} {m : M β} {S V : Set β} {p : ℝ≥0∞}
    (hsupp : (𝒟[m]).support ⊆ V)
    (hclosed : ∀ a ∈ V, ∀ b ∈ V, best a b ∈ V)
    (hkeep : ∀ a ∈ V, ∀ b ∈ V, a ∈ S ∨ b ∈ S → best a b ∈ S)
    (hp : p ≤ ℙ[m ∈ S]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify best k m ∈ S] := by
  have hq : prob (𝒟[m]) Sᶜ ≤ 1 - p := by
    rw [prob_compl_eq_one_sub]
    exact tsub_le_tsub_left hp 1
  have hfail : prob (𝒟[amplify best k m]) Sᶜ ≤ (1 - p) ^ k :=
    le_trans (prob_amplify_compl_le hsupp hclosed hkeep k)
      (pow_le_pow_left' hq k)
  calc 1 - (1 - p) ^ k
      ≤ 1 - prob (𝒟[amplify best k m]) Sᶜ := tsub_le_tsub_left hfail 1
    _ = prob (𝒟[amplify best k m]) S := (prob_eq_one_sub_compl _ _).symm

/-- `amplify_success` for the ubiquitous "keep the smallest answer"
case: if every output of `m` is at least `v` (one-sided error) and
`m` hits `v` with probability at least `p`, the minimum over `k`
independent runs is exactly `v` with probability at least
`1 − (1 − p) ^ k`. The two hypotheses are exactly the support and
success theorems a one-sided algorithm already provides. -/
theorem amplify_min_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} [LinearOrder β] {m : M β} {v : β} {p : ℝ≥0∞}
    (hsupp : ∀ b ∈ (𝒟[m]).support, v ≤ b)
    (hp : p ≤ ℙ[m = v]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify min k m = v] := by
  have h := amplify_success (best := min) (S := {v}) (V := Set.Ici v) (p := p)
    hsupp
    (fun a ha b hb => Set.mem_Ici.mpr (le_min (Set.mem_Ici.mp ha) (Set.mem_Ici.mp hb)))
    (fun a ha b hb hor => by
      rw [Set.mem_Ici] at ha hb
      rw [Set.mem_singleton_iff]
      rcases hor with h1 | h1 <;> rw [Set.mem_singleton_iff] at h1 <;> subst h1
      · exact min_eq_left hb
      · exact min_eq_right ha)
    (by rw [prob_singleton]; exact hp) k
  rwa [prob_singleton] at h

/-- Dual of `amplify_min_success`: keep the largest answer of a
never-overshooting algorithm. -/
theorem amplify_max_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {β : Type} [LinearOrder β] {m : M β} {v : β} {p : ℝ≥0∞}
    (hsupp : ∀ b ∈ (𝒟[m]).support, b ≤ v)
    (hp : p ≤ ℙ[m = v]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ[amplify max k m = v] := by
  have h := amplify_success (best := max) (S := {v}) (V := Set.Iic v) (p := p)
    hsupp
    (fun a ha b hb => Set.mem_Iic.mpr (max_le (Set.mem_Iic.mp ha) (Set.mem_Iic.mp hb)))
    (fun a ha b hb hor => by
      rw [Set.mem_Iic] at ha hb
      rw [Set.mem_singleton_iff]
      rcases hor with h1 | h1 <;> rw [Set.mem_singleton_iff] at h1 <;> subst h1
      · exact max_eq_left hb
      · exact max_eq_right ha)
    (by rw [prob_singleton]; exact hp) k
  rwa [prob_singleton] at h

/-! ## Cost: amplification is linear -/

/-- `k + 1` runs cost `k + 1` times one run. -/
theorem expected_cost_amplify
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M] {β : Type}
    (best : β → β → β) (k : ℕ) (m : TimeMT ℕ M β) :
    𝔼_runtime[amplify best (k + 1) m] = (k + 1 : ℝ≥0∞) * 𝔼_runtime[m] := by
  induction k with
  | zero => simp only [zero_add, Nat.cast_zero, amplify_one, one_mul]
  | succ k ih =>
    rw [amplify_succ_succ,
      expected_cost_toPMF_bind_const _ _ fun a => expected_cost_toPMF_bind_pure _ _,
      ih]
    push_cast
    ring

end ARA
