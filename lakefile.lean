import Lake

open System Lake DSL

package «ml-opt-bounds-formalization» where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib MlOptBoundsFormalization

@[default_target] lean_exe «ml-opt-bounds-formalization» where root := `Main
