/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Randomness.LawfulRandMonad

/-!
# The probability core: expectations, events, and the `ℙ` notation

The generic probability functionals of a randomized computation,
independent of any cost model: what an algorithm *outputs* with what
probability, and the expected value of a functional of its output.
Everything here is about `PMF` and `toPMF` alone, so it sits below
both the correctness and the complexity layers — a pure-probability
case study (`Geometric`, `CouponCollector`) never has to import the
cost machinery to use it.

## Main declarations

* `expVal p g` — the expectation `Σ' a, p a * g a`, with the
  `pure`/`bind`/`map`/uniform decomposition API. Used both for
  *structural* output functionals (a random tree's height) and, one
  layer up, as the definition behind `expected_cost`.
* `prob p s` — the probability of an event, with the event algebra
  (singletons, complements, `bind`, `pure`).
* `mul_prob_ge_le_expVal` / `prob_ge_le_expVal_div` — Markov's
  inequality on `expVal`, the estimate every tail bound rests on.
* `ℙ[e = v | M]` / `ℙ[e ∈ S | M]` — the output-probability notation,
  correctness twin of `𝔼_runtime[e | M]`.
-/

namespace ARA

open ENNReal

/-!
## Expected values of output functionals

For randomized algorithms whose interesting measure is a *structural*
functional of the output — the height of a random tree, the size of a
random cut — rather than a tick count, we provide the bare expectation
`expVal p g = Σ' a, p a * g a` with the same `bind`/`pure`/uniform
decomposition API as `expected_cost`.
-/

/-- Expected value of `g` under `p`. -/
noncomputable def expVal {α : Type*} (p : PMF α) (g : α → ENNReal) : ENNReal :=
  ∑' a, p a * g a

@[simp] lemma expVal_pure {α : Type*} (a : α) (g : α → ENNReal) :
    expVal (PMF.pure a) g = g a := by
  unfold expVal
  rw [tsum_eq_single a fun b hb => by
    rw [PMF.pure_apply, if_neg hb, zero_mul]]
  rw [PMF.pure_apply, if_pos rfl, one_mul]

/-- Tower rule: the expected value through a bind is the expected
expected value. -/
lemma expVal_bind {α β : Type*} (p : PMF α) (f : α → PMF β)
    (g : β → ENNReal) :
    expVal (p.bind f) g = expVal p fun a => expVal (f a) g := by
  unfold expVal
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

lemma expVal_const {α : Type*} (p : PMF α) (c : ENNReal) :
    expVal p (fun _ => c) = c := by
  unfold expVal
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma expVal_mono {α : Type*} (p : PMF α) {g₁ g₂ : α → ENNReal}
    (h : ∀ a, g₁ a ≤ g₂ a) : expVal p g₁ ≤ expVal p g₂ :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

lemma expVal_add {α : Type*} (p : PMF α) (g₁ g₂ : α → ENNReal) :
    expVal p (fun a => g₁ a + g₂ a) = expVal p g₁ + expVal p g₂ := by
  unfold expVal
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun a => mul_add _ _ _

lemma expVal_const_mul {α : Type*} (p : PMF α) (g : α → ENNReal)
    (c : ENNReal) :
    expVal p (fun a => c * g a) = c * expVal p g := by
  unfold expVal
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun a => by ring

lemma expVal_mul_right {α : Type*} (p : PMF α) (g : α → ENNReal)
    (c : ENNReal) :
    expVal p (fun a => g a * c) = expVal p g * c := by
  unfold expVal
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun a => (mul_assoc _ _ _).symm

/-- `expVal` through a `map`: relabelling then averaging is averaging
the composite. -/
lemma expVal_map {α β : Type*} (p : PMF α) (f : α → β) (g : β → ENNReal) :
    expVal (p.map f) g = expVal p (fun a => g (f a)) := by
  rw [PMF.map, expVal_bind]
  simp only [Function.comp_apply, expVal_pure]

/-- **Uniform-pivot step for output functionals**: the expected value
of `g` over `randIdx >>= branch` is the uniform average of the branch
expectations — the `expVal` analogue of `expected_cost_uniform_step`. -/
lemma expVal_toPMF_randIdx_bind
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type*} {β : Type} {L : List α} {hL : 0 < L.length}
    (f : Fin L.length → M β) (g : β → ENNReal) :
    expVal (inst.toPMF (randIdx L hL >>= f)) g =
      (L.length : ENNReal)⁻¹ * ∑ i : Fin L.length, expVal (inst.toPMF (f i)) g := by
  have : Nonempty (Fin L.length) := ⟨⟨0, hL⟩⟩
  rw [inst.toPMF_bind, inst.toPMF_randIdx, pmf_bind_eq, expVal_bind]
  unfold expVal
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]

/-!
## Probability of an event
-/

/-- Probability of the event `s` under the distribution `p`. -/
noncomputable def prob {α : Type*} (p : PMF α) (s : Set α) : ENNReal :=
  ∑' a, s.indicator p a

/-- `prob` agrees with the outer measure induced by the `PMF`, giving
access to the Mathlib measure-theory API when needed. -/
lemma prob_eq_toOuterMeasure {α : Type*} (p : PMF α) (s : Set α) :
    prob p s = p.toOuterMeasure s :=
  (p.toOuterMeasure_apply s).symm

/-- A larger event is at least as probable. -/
lemma prob_mono {α : Type*} (p : PMF α) {s t : Set α} (h : s ⊆ t) :
    prob p s ≤ prob p t := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hs : a ∈ s
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (h hs)]
  · rw [Set.indicator_of_notMem hs]
    exact zero_le

@[simp] lemma prob_univ {α : Type*} (p : PMF α) :
    prob p Set.univ = 1 := by
  unfold prob
  rw [Set.indicator_univ]
  exact p.tsum_coe

/-- Probabilities are at most `1`. -/
lemma prob_le_one {α : Type*} (p : PMF α) (s : Set α) :
    prob p s ≤ 1 :=
  le_trans (prob_mono p (Set.subset_univ s)) (prob_univ p).le

/-!
### The event algebra

Singletons, complements, `bind` and `pure` — everything an event
computation needs.
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

/-!
## Markov's inequality for `expVal`
-/

/-- **Markov's inequality**, product form: `k · P(g ≥ k) ≤ E[g]`.
No side conditions — this is the fundamental estimate. -/
theorem mul_prob_ge_le_expVal {α : Type*} (p : PMF α)
    (g : α → ENNReal) (k : ENNReal) :
    k * prob p {a | k ≤ g a} ≤ expVal p g := by
  unfold prob expVal
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : k ≤ g a
  · rw [Set.indicator_of_mem (show a ∈ {a | k ≤ g a} from h), mul_comm]
    exact mul_le_mul' le_rfl h
  · rw [Set.indicator_of_notMem (show a ∉ {a | k ≤ g a} from h), mul_zero]
    exact zero_le

/-- **Markov's inequality**, division form: `P(g ≥ k) ≤ E[g] / k`. -/
theorem prob_ge_le_expVal_div {α : Type*} (p : PMF α)
    (g : α → ENNReal) {k : ENNReal} (hk0 : k ≠ 0) (hktop : k ≠ ⊤) :
    prob p {a | k ≤ g a} ≤ expVal p g / k := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop), mul_comm]
  exact mul_prob_ge_le_expVal p g k

/-!
## Success probability of outputs

`ℙ[e = v | M]` / `ℙ[e ∈ S | M]` are the correctness twins of
`ℙ_runtime[e > k | M]`: the probability that the algorithm `e`, run
at the random monad `M`, outputs exactly `v` (resp. lands in the
event `S`). A Monte-Carlo statement then reads as English:
`2 / (n(n−1)) ≤ ℙ[Karger g = g.minCutValue | M]`. Both expand to the
underlying `toPMF`/`prob` form so `simp`/`rw` match lemmas without
unfolding hints; `prob_singleton` mediates between the two.
-/

/-- `ℙ[e = v | M]` — probability that the algorithm `e`, run at the
random monad `M`, outputs exactly `v`. -/
scoped macro "ℙ[" e:term:51 " = " v:term:51 " | " M:term "]" : term =>
  `(LawfulRandMonad.toPMF ($e : $M _) $v)

/-- `ℙ[m = v]` — output probability of an already-typed
computation. -/
scoped macro "ℙ[" m:term:51 " = " v:term "]" : term =>
  `(LawfulRandMonad.toPMF $m $v)

/-- `ℙ[e ∈ S | M]` — probability that the algorithm `e`, run at the
random monad `M`, outputs a value in the event `S`. -/
scoped macro "ℙ[" e:term:51 " ∈ " S:term:51 " | " M:term "]" : term =>
  `(prob (LawfulRandMonad.toPMF ($e : $M _)) $S)

/-- `ℙ[m ∈ S]` — event probability of an already-typed
computation. -/
scoped macro "ℙ[" m:term:51 " ∈ " S:term "]" : term =>
  `(prob (LawfulRandMonad.toPMF $m) $S)

end ARA
