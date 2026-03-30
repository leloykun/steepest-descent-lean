import Lake

open System Lake DSL

package «steepest-descent-lean» where version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib SteepestDescentOptimizationBounds

lean_lib SteepestDescentScalingLaws

@[default_target] lean_lib SteepestDescent
