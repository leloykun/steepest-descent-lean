/-
The umbrella module for the hyperparameter scaling-law layer.

Upstream:
- `SteepestDescentOptimizationBounds`
- the individual files in `SteepestDescentScalingLaws/`

Downstream:
- `SteepestDescent.lean`

This module groups the shared asymptotic helper layer together with the three
scaling-law families:
- star-convex expected suboptimality
- Frank-Wolfe expected gap
- Frank-Wolfe expected suboptimality
-/

import SteepestDescentScalingLaws.Commons

import SteepestDescentScalingLaws.StarConvexScalingLawsTheorem1
import SteepestDescentScalingLaws.StarConvexScalingLawsTheorem2

import SteepestDescentScalingLaws.FWExpectedGapSLTheorem1
import SteepestDescentScalingLaws.FWExpectedGapSLTheorem2

import SteepestDescentScalingLaws.FWExpectedSuboptimalitySLTheorem1
import SteepestDescentScalingLaws.FWExpectedSuboptimalitySLTheorem2
