import Mathlib

/-! Register the custom simp attribute for PMF computations.
This must be in a separate file from where it is used, per Lean 4 constraints. -/

register_simp_attr pmf_simp_attr
