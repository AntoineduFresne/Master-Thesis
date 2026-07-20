import Lake
open Lake DSL

package «MasterThesis» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"
require cslib from git "https://github.com/leanprover/cslib" @ "v4.31.0"

@[default_target]

lean_lib ARA

/-- `lake exe axiom_audit`: check that no ARA declaration depends on an axiom
outside `propext`, `Classical.choice`, `Quot.sound`. The audit reads the
`.olean` files rather than the sources, hence `needs`. -/
lean_exe axiom_audit where
  root := `AxiomAudit
  srcDir := "scripts"
  needs := #[ARA]
  supportInterpreter := true

