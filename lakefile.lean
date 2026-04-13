import Lake
open Lake DSL

package "MasterThesis" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «ARA» where
  roots := #[`ARA.Basic, `ARA.Phase1, `ARA.Phase2, `ARA.Tactics,
             `ARA.Demos, `ARA.QuickSort, `ARA.Rnd, `ARA.FutureWork]
  leanLibDeps := #[«TimeM»]

lean_lib «MasterThesis» where

lean_lib «TimeM» where
