/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.ExpectedCost

/-!
# Tail bounds

Markov's inequality for randomized computations: the probability that
the cost exceeds `k` is at most the expected cost divided by `k`.
This is the third analysis tier, next to correctness and expected
cost — an expected-cost theorem upgrades to a tail bound for free:

```
ℙ_runtime[m > k] ≤ 𝔼_runtime[m] / (k + 1)
```

## Main declarations

* `prob` — probability of an event under a `PMF`
* `mul_prob_ge_le_expVal`, `prob_ge_le_expVal_div` — Markov's
  inequality for `expVal`
* `runtime_markov`, `runtime_markov_gt` — the cost tail bounds, in
  `ℙ_runtime[m ≥ k]` / `ℙ_runtime[m > k]` notation

Since costs are `ℕ`-valued, the strict form `runtime_markov_gt`
divides by `k + 1` (via `P(cost > k) = P(cost ≥ k + 1)`): it is both
sharper than the classical `E/k` and free of any `k ≠ 0` hypothesis.
-/

namespace ARA

open Cslib.Algorithms.Lean
open ENNReal

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

/-- `expected_cost` is the `expVal` of the running time — the bridge
that lets every `expVal` estimate apply to costs. -/
lemma expected_cost_eq_expVal {α : Type} (p : PMF (TimeM ℕ α)) :
    expected_cost p = expVal p fun tm => (tm.time : ENNReal) := rfl

/-!
## Runtime tail bounds

`ℙ_runtime[m > k]` is the probability that the running time of `m`
exceeds `k`, mirroring the `𝔼_runtime[m]` notation. Like it, the
notation expands to the underlying `prob (TimedPMF m) {…}` form so
`simp`/`rw` can match lemmas without unfolding hints.
-/

/-- `ℙ_runtime[m ≥ k]` — probability that the running time of `m` is
at least `k : ℕ`. -/
scoped macro "ℙ_runtime[" m:term:51 " ≥ " k:term "]" : term =>
  `(prob (TimedPMF $m) {tm | $k ≤ tm.time})

/-- `ℙ_runtime[m > k]` — probability that the running time of `m`
exceeds `k : ℕ`. -/
scoped macro "ℙ_runtime[" m:term:51 " > " k:term "]" : term =>
  `(prob (TimedPMF $m) {tm | $k < tm.time})

/-- `ℙ_runtime[e ≥ k | M]` — tail probability of the
monad-polymorphic algorithm `e`, instantiated at the random monad
`M`; sugar for `ℙ_runtime[(e : TimeMT ℕ M _) ≥ k]`. -/
scoped macro "ℙ_runtime[" e:term:51 " ≥ " k:term:51 " | " M:term "]" : term =>
  `(prob (TimedPMF ($e : TimeMT ℕ $M _)) {tm | $k ≤ tm.time})

/-- `ℙ_runtime[e > k | M]` — strict-tail variant of
`ℙ_runtime[e ≥ k | M]`. -/
scoped macro "ℙ_runtime[" e:term:51 " > " k:term:51 " | " M:term "]" : term =>
  `(prob (TimedPMF ($e : TimeMT ℕ $M _)) {tm | $k < tm.time})

/-- **Markov tail bound for runtimes**: `P(cost ≥ k) ≤ E[cost] / k`.
Any expected-cost theorem yields a tail bound for free. -/
theorem runtime_markov
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {β : Type} (m : TimeMT ℕ M β) {k : ℕ} (hk : k ≠ 0) :
    ℙ_runtime[m ≥ k] ≤ 𝔼_runtime[m] / (k : ENNReal) := by
  have h := prob_ge_le_expVal_div (TimedPMF m)
    (fun tm => (tm.time : ENNReal)) (k := (k : ENNReal))
    (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)
  rw [← expected_cost_eq_expVal] at h
  convert h using 2
  ext tm
  simp

/-- **Strict Markov tail bound**: `P(cost > k) ≤ E[cost] / (k + 1)`.
Since costs are `ℕ`-valued this is sharper than the classical `E/k`
and needs no `k ≠ 0` hypothesis. -/
theorem runtime_markov_gt
    {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    {β : Type} (m : TimeMT ℕ M β) (k : ℕ) :
    ℙ_runtime[m > k] ≤ 𝔼_runtime[m] / (k + 1 : ENNReal) := by
  have h := runtime_markov m (k := k + 1) k.succ_ne_zero
  have hset : {tm : TimeM ℕ β | k < tm.time} =
      {tm : TimeM ℕ β | k + 1 ≤ tm.time} := by
    ext tm; exact Nat.lt_iff_add_one_le
  rw [hset]
  simpa using h

-- Smoke test: the notation elaborates and a tail bound is one line.
example {M : Type → Type} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (m : TimeMT ℕ M Unit) :
    ℙ_runtime[m > 9] ≤ 𝔼_runtime[m] / 10 := by
  have h := runtime_markov_gt m 9
  norm_num at h
  exact h

/-!
## Success probability of outputs

`ℙ[e = v | M]` / `ℙ[e ∈ S | M]` are the correctness twins of
`ℙ_runtime[e > k | M]`: the probability that the algorithm `e`, run
at the random monad `M`, outputs exactly `v` (resp. lands in the
event `S`). A Monte-Carlo statement then reads as English:
`2 / (n(n−1)) ≤ ℙ[Karger g = g.minCutValue | M]`. Both expand to the
underlying `toPMF`/`prob` form so `simp`/`rw` match lemmas without
unfolding hints; `prob_singleton` (in `ARA.Infrastructure.Amplify`)
mediates between the two.
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
