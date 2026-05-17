import Lake
open Lake DSL

package «MasterThesis» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"
-- require cslib from git "https://github.com/leanprover/cslib" @ "4.28.0"

@[default_target]

lean_lib ARA

lean_lib TimeM
