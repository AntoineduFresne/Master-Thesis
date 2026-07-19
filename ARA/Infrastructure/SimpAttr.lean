/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-! Register the custom simp attributes for ARA.
These must be in a separate file from where they are used, per Lean 4
constraints.

* `pmf_simp_attr` — concrete probability computations
  (`tsum`, `bind_apply`, `uniformOfFintype_apply`, …).
* `expected_cost_simp` — bridge lemmas that decompose `expected_cost` /
  `runtime` through `TimeMT` combinators (`pure`, `bind`, `tick`, `lift`).
* `toPMF_simp` — lemmas that push `toPMF` through an algorithm branch
  (`toPMF_bind`, `toPMF_pure`, lawful `tick`, monad laws); the engine
  of the `toPMF_step` tactic in `ARA.Infrastructure.Correctness`.
  Tier-agnostic: the same set drives Dirac, distributional and
  support proofs.
* `spec_transport` — per-algorithm lemmas stating how a specification
  commutes with one branch of the algorithm (e.g. `orderStat_lt_branch`).
  Consumed by `dirac_finish`; the *only* lemmas a new algorithm must
  provide for its Dirac-correctness proof.
-/

register_simp_attr pmf_simp_attr
register_simp_attr expected_cost_simp
register_simp_attr toPMF_simp
register_simp_attr spec_transport
