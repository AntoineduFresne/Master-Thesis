/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import ARA

/-!
# Axiom audit

Checks that every headline theorem of the framework depends only on
the three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular, no `sorryAx` and no `native_decide`.

Run with `lake env lean scripts/AxiomAudit.lean` (after `lake build`);
the command exits nonzero on any violation. CI runs this on every push.
-/

open Lean

/-- The axioms a finished proof is allowed to use. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The headline theorems of the framework: the strongest
user-facing statement(s) of each case study, plus the generic
tail-bound tier. Auditing these transitively audits everything
they depend on. -/
def headliners : List Name := [
  -- Tutorial
  ``ARA.randMax_correct_pmf,
  ``ARA.randMax_cost_exact,
  -- Quicksort
  ``ARA.quicksort_correct_pmf,
  ``ARA.quicksort_cost_le_pmf,
  ``ARA.quicksort_cost_exact_pmf,
  -- Quickselect
  ``ARA.quickselect_correct_pmf,
  ``ARA.quickselect_cost_le_linear_pmf,
  ``ARA.quickselect_cost_exact_pmf,
  -- Karger
  ``ARA.karger_correct_pmf,
  ``ARA.karger_success_prob_pmf,
  ``ARA.karger_cost_le_real,
  -- Reservoir sampling
  ``ARA.reservoir_correct_pmf,
  ``ARA.reservoir_cost_exact,
  -- Freivalds
  ``ARA.freivalds_complete_pmf,
  ``ARA.freivalds_sound_pmf,
  ``ARA.freivalds_cost_exact,
  -- Treap
  ``ARA.treap_correct_pmf,
  ``ARA.treap_expected_height_le_pmf,
  -- Tail-bound tier
  ``ARA.runtime_markov,
  ``ARA.runtime_markov_gt]

open Elab Command in
#eval show CommandElabM Unit from do
  let mut bad : Array (Name × List Name) := #[]
  for n in headliners do
    let axioms ← collectAxioms n
    let disallowed := axioms.toList.filter (fun a => !allowedAxioms.contains a)
    if disallowed.isEmpty then
      logInfo m!"ok: {n}"
    else
      bad := bad.push (n, disallowed)
  unless bad.isEmpty do
    throwError "axiom audit failed:{bad.foldl
      (fun msg (n, axs) => msg ++ m!"\n  {n} uses {axs}") (m!"" : MessageData)}"
