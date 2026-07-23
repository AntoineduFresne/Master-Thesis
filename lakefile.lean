import Lake
open Lake DSL

package «MasterThesis» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"
require cslib from git "https://github.com/leanprover/cslib" @ "v4.32.0"

@[default_target]

lean_lib ARA

