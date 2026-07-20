/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA.Infrastructure.Complexity.ExpectedCost
import ARA.Infrastructure.Complexity.Variance

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

* `expected_cost_eq_expVal` — the bridge making every `expVal`
  estimate (Markov, Chebyshev) apply to running times
* `ℙ_runtime[m ≥ k]` / `ℙ_runtime[m > k]` notation
* `runtime_markov`, `runtime_markov_gt` — the first-moment cost tail
  bounds
* `runtime_chebyshev` — the second-moment cost tail bound

The event algebra (`prob`, singletons, complements, `bind`) and
Markov's inequality on `expVal` itself live one layer down in
`ARA.Infrastructure.Randomness.Prob`, together with the
output-probability notation `ℙ[e = v | M]`.

Since costs are `ℕ`-valued, the strict form `runtime_markov_gt`
divides by `k + 1` (via `P(cost > k) = P(cost ≥ k + 1)`): it is both
sharper than the classical `E/k` and free of any `k ≠ 0` hypothesis.
-/

namespace ARA

open Cslib.Algorithms.Lean
open ENNReal

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

end ARA
