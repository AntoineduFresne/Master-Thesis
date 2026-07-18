# Cold-eyes usability review — 2026-07-15

Produced by a read-only reviewer agent (fresh context, no project
history), mandate: naming consistency, learnability, statement
naturality, redundancy, generality, doc drift. 30 ranked findings.

## Executive summary
1. Adopt ONE naming convention (Mathlib-style, keyed on the definition
   name): `<algo>_correct` / `_correct_pmf`, `<algo>_cost_exact`
   (equalities) vs `<algo>_cost_le*` (bounds). Previously four schemes
   coexisted, including a case-only collision
   (Freivalds_complete vs freivalds_complete) and names that lied
   about strength (Expected_Complexity_Quickselect was a bound).
2. Remove the two pieces of cargo-cult magic a Tutorial reader must
   copy: the `@Algo _ _ _ M _ _ instMonadCostDefault` incantation in
   correctness statements, and the desugared
   `show expected_cost (inst.toPMF (...).run)` blocks in cost proofs.
3. Make Quicksort follow the Tutorial's own recipe: state correctness
   as a Dirac mass at `L.mergeSort (· ≤ ·)` instead of an existential.

## Findings applied (2026-07-15)
- [x] Full rename table (see git log "Adopt the uniform naming convention")
- [x] TimeMT double `Monad` instance removed (diamond risk)
- [x] `instMonadCostTimeMT` generalized from ℕ to any cost type `T`
- [x] Doc drift: Treap stale "future work" note, MonadCost instance
      names, README instance count, Tutorial step numbering and
      "one rewrite" claim, ExpectedCost docstring comments
- [x] Redundant `((… : ℕ) : ENNReal)` double-casts on `choose` terms
- [x] Karger switched to the `𝔼_runtime[e | M]` notation
- [x] Duplicate `Correctness_Quickselect_PMF` deleted
- [x] `@…instMonadCostDefault` dropped from correctness statements
- [x] Quicksort correctness restated as Dirac at `mergeSort`
- [x] API promotions: `TimeMT_randFin_run`, `uniform_avg_const`,
      Pascal `choose_two_succ` + `choose_two_add_le` into Helpers,
      `pmf_map_some_apply`/`_none` into Tactics
- [ ] #5  cost-proof `show`-blocks (needs expected_cost_simp surgery)
- [ ] #23 promote `randBit`/`randVec` out of Freivalds
- [ ] #26 Karger success-probability statement with named `n`
- [ ] #28 de-`have` the `toPMF_randFin`/`toPMF_randIdx` statements
- [ ] #29 `pmf_simp_attr` naming exception (documented only)
