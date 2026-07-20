/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/
import Lean

/-!
# Axiom audit

A standalone checker that every declaration of the `ARA` library rests only on
Lean's three classical axioms — `propext`, `Classical.choice`, `Quot.sound` —
the trusted base mathlib itself is built on. Anything else is a failure. In
particular this catches

* `sorryAx`: a proof that was never finished. `lake build` accepts a `sorry`
  with only a warning, and a `sorry` buried in an auxiliary lemma is easy to
  lose track of;
* `Lean.ofReduceBool` / `Lean.trustCompiler`: results that hold only if the
  compiler is correct (`native_decide`).

Run it with `lake exe axiom_audit` *after* `lake build`. The audit reads the
`.olean` files, it never elaborates anything itself, so it is fast (a second or
two) and it audits exactly the artefacts a reader of the repository would get.
-/

open Lean

namespace ARA.AxiomAudit

/-- The axioms a declaration may depend on: Lean's classical foundations. -/
def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Is `mod` a module of ARA itself, as opposed to mathlib, cslib or core? -/
def isARAModule (mod : Name) : Bool :=
  (`ARA).isPrefixOf mod

/-- `collectAxioms` asks only for a `MonadEnv`, not for the rest of `CoreM`. -/
private abbrev AuditM := StateM Environment

private instance : MonadEnv AuditM where
  getEnv := get
  modifyEnv f := modify f

/-- The disallowed axioms `decl` transitively depends on; `#[]` if it is clean. -/
def badAxioms (env : Environment) (decl : Name) : Array Name :=
  let axioms := (collectAxioms (m := AuditM) decl).run' env
  axioms.filter fun ax => !allowedAxioms.contains ax

end ARA.AxiomAudit

open ARA.AxiomAudit in
/-- `unsafe` only because `enableInitializersExecution` is. -/
unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- `loadExts` is what makes this fast: it restores the environment extension in
  -- which each `.olean` already records its declarations' axiom dependencies, so
  -- no proof term has to be walked again.
  enableInitializersExecution
  let env ← importModules #[{ module := `ARA }] (opts := {}) (loadExts := true)
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData
  let mut checked := 0
  let mut offenders : Array (Name × Array Name) := #[]
  for i in [:moduleData.size] do
    if !isARAModule moduleNames[i]! then continue
    for decl in moduleData[i]!.constNames do
      checked := checked + 1
      let bad := badAxioms env decl
      if !bad.isEmpty then
        offenders := offenders.push (decl, bad)
  if offenders.isEmpty then
    IO.println s!"axiom audit passed: {checked} ARA declarations depend only on \
      propext, Classical.choice and Quot.sound"
    return 0
  IO.eprintln s!"axiom audit FAILED: {offenders.size} of {checked} ARA declarations \
    depend on axioms outside Lean's classical foundations"
  for (decl, bad) in offenders do
    IO.eprintln s!"  {decl} — {String.intercalate ", " (bad.toList.map toString)}"
  return 1
