/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA

/-! Register the custom simp attributes for ARA.
These must be in a separate file from where they are used, per Lean 4
constraints.

* `pmf_simp_attr` — concrete probability computations
  (`tsum`, `bind_apply`, `uniformOfFintype_apply`, …).
* `expected_cost_simp` — bridge lemmas that decompose `expected_cost` /
  `runtime` through `TimeMT` combinators (`pure`, `bind`, `tick`, `lift`).
* `dirac_simp` — lemmas that push `toPMF` through an algorithm branch
  (`toPMF_bind`, `toPMF_pure`, no-op `tick`, monad laws); the engine of
  the `dirac_step` tactic in `ARA.Correctness`.
* `spec_transport` — per-algorithm lemmas stating how a specification
  commutes with one branch of the algorithm (e.g. `orderStat_lt_branch`).
  Consumed by `dirac_finish`; the *only* lemmas a new algorithm must
  provide for its Dirac-correctness proof.
-/

register_simp_attr pmf_simp_attr
register_simp_attr expected_cost_simp
register_simp_attr dirac_simp
register_simp_attr spec_transport
