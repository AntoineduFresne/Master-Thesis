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
-/

register_simp_attr pmf_simp_attr
register_simp_attr expected_cost_simp
