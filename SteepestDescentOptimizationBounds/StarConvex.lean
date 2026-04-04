import Mathlib
import SteepestDescentOptimizationBounds.DescentLemma
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds
import SteepestDescentOptimizationBounds.NesterovMomentumBounds

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Deterministic and pathwise star-convex descent layer.

Upstream dependencies:

- `DescentLemma.lean` supplies the local Taylor comparison.
- `WeightAndUpdateBounds.lean` supplies the decoupled weight-decay geometry.
- `NesterovMomentumBounds.lean` supplies the Nesterov-residual split.

Downstream use:

- `StarConvexExpectedSuboptimality.lean` integrates the pathwise recurrence.
- the scaling-law layer reuses the deterministic coefficient definitions on the
  stochastic wrapper namespace.
-/

namespace StarConvexPathGeometryContext

section PublicDefinitions

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Canonical pairing context for the continuous dual. -/
def continuousDualPairing :
    ContinuousDualPairingContext V (StrongDual ℝ V) where
  toLinear := by
    simpa using (ContinuousLinearMap.id ℝ (StrongDual ℝ V))
  opNorm_le := by
    intro xDual
    simp

/-- The linear functional induced by the current true gradient. -/
def gradientLinear (S : StarConvexPathGeometryContext V) (t : ℕ) : V →ₗ[ℝ] ℝ :=
  (S.grad t).toLinearMap

/-- The interpolation point `X_t = (1 - λη) W_t + λη W_*`. -/
def interpolatedPoint (S : StarConvexPathGeometryContext V) (t : ℕ) : V :=
  S.stepCenter t + (S.lambda * S.eta) • S.WStar

end PublicDefinitions

section PrivateDefinitions

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

-- No private definitions are introduced in this file.

end PrivateDefinitions

section PrivateLemmas

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Unpacks `∇f(W_t) = C_t + error_t` on a concrete vector. -/
private lemma grad_split_apply
    (S : StarConvexPathGeometryContext V) (t : ℕ) (v : V) :
    S.gradientLinear t v = (S.C t) v + S.nesterovError t v := by
  rw [gradientLinear, SteepestDescentPathGeometryContext.nesterovError, S.C_spec t]
  simp [SteepestDescentPathGeometryContext.grad, sub_eq_add_neg]
  ring

/-- File-local star-convex interpolation inequality from Assumption 12. -/
private lemma star_convex_prop
    (S : StarConvexPathGeometryContext V) :
    ∀ W α, 0 ≤ α → α ≤ 1 →
      S.f ((1 - α) • W + α • S.WStar) ≤ (1 - α) * S.f W + α * S.f S.WStar :=
  Assumption12_StarConvexityAtReferencePoint.star_convex S.assumption12_starConvexity

/-- Shared scaling estimate for vectors already in the radius-`1 / λ` ball. -/
private lemma scaled_norm_le_eta
    (S : StarConvexPathGeometryContext V) {x : V}
    (hx : ‖x‖ ≤ 1 / S.lambda) :
    ‖(S.lambda * S.eta) • x‖ ≤ S.eta := by
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  calc
    ‖(S.lambda * S.eta) • x‖ = (S.lambda * S.eta) * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
      exact mul_le_mul_of_nonneg_left hx hScaleNonneg
    _ = S.eta := by
      field_simp [S.lambda_pos.ne']

end PrivateLemmas

section PublicTheorems

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Rewrites the displacement from the step center to `X_t`. -/
lemma interpolatedPoint_sub_stepCenter
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    S.interpolatedPoint t - S.stepCenter t = (S.lambda * S.eta) • S.WStar := by
  simp [interpolatedPoint]

/-- The interpolation point is feasible for the linearized update ball. -/
lemma interpolatedPoint_feasible
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t - S.stepCenter t‖ ≤ S.eta := by
  calc
    ‖S.interpolatedPoint t - S.stepCenter t‖ = ‖(S.lambda * S.eta) • S.WStar‖ := by
      rw [interpolatedPoint_sub_stepCenter]
    _ ≤ S.eta := S.scaled_norm_le_eta S.WStar_bound

/-- The interpolation point also stays in the primal radius-`1 / λ` ball. -/
lemma interpolatedPoint_bound
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda := by
  have hWeight := S.weight_bound_from_feasible_step t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hDecayNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
  calc
    ‖S.interpolatedPoint t‖
      = ‖(1 - S.lambda * S.eta) • S.W t + (S.lambda * S.eta) • S.WStar‖ := by
          simp [interpolatedPoint, SteepestDescentPathGeometryContext.stepCenter]
    _ ≤ ‖(1 - S.lambda * S.eta) • S.W t‖ + ‖(S.lambda * S.eta) • S.WStar‖ := norm_add_le _ _
    _ = (1 - S.lambda * S.eta) * ‖S.W t‖ + (S.lambda * S.eta) * ‖S.WStar‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hDecayNonneg, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (1 - S.lambda * S.eta) * (1 / S.lambda) + (S.lambda * S.eta) * (1 / S.lambda) := by
          have hFirst :
              (1 - S.lambda * S.eta) * ‖S.W t‖ ≤
                (1 - S.lambda * S.eta) * (1 / S.lambda) := by
            exact mul_le_mul_of_nonneg_left hWeight hDecayNonneg
          have hSecond :
              (S.lambda * S.eta) * ‖S.WStar‖ ≤
                (S.lambda * S.eta) * (1 / S.lambda) := by
            exact mul_le_mul_of_nonneg_left S.WStar_bound hScaleNonneg
          linarith
    _ = 1 / S.lambda := by
          field_simp [S.lambda_pos.ne']
          ring

/-- Geometry package for the interpolation point used in the one-step proof. -/
theorem lemma13_interpolatedPoint_geometry
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda ∧
      (S.C t) (S.W (t + 1) - S.interpolatedPoint t) ≤ 0 ∧
      ‖S.interpolatedPoint t - S.W t‖ ≤ 2 * S.eta ∧
      ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤ 2 * S.eta := by
  have hInterp := interpolatedPoint_bound S t
  have hXFeasible := interpolatedPoint_feasible S t
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step t
  have hWeightCenter : ‖S.W t - S.stepCenter t‖ ≤ S.eta := by
    rw [S.weight_sub_stepCenter t]
    exact S.scaled_norm_le_eta hWeight
  have hOptimal := S.step_optimal t (S.interpolatedPoint t) hXFeasible
  refine ⟨hInterp, ?_, ?_, ?_⟩
  · rw [(S.C t).map_sub]
    exact sub_nonpos.mpr hOptimal
  · calc
      ‖S.interpolatedPoint t - S.W t‖
          = ‖(S.interpolatedPoint t - S.stepCenter t) - (S.W t - S.stepCenter t)‖ := by
              abel_nf
      _ ≤ ‖S.interpolatedPoint t - S.stepCenter t‖ + ‖S.W t - S.stepCenter t‖ := norm_sub_le _ _
      _ ≤ S.eta + S.eta := add_le_add hXFeasible hWeightCenter
      _ = 2 * S.eta := by ring
  · calc
      ‖S.W (t + 1) - S.interpolatedPoint t‖
          = ‖(S.W (t + 1) - S.stepCenter t) - (S.interpolatedPoint t - S.stepCenter t)‖ := by
              have hDecomp :
                  S.W (t + 1) - S.interpolatedPoint t =
                    (S.W (t + 1) - S.stepCenter t) -
                      (S.interpolatedPoint t - S.stepCenter t) := by
                abel_nf
              rw [hDecomp]
      _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.interpolatedPoint t - S.stepCenter t‖ := norm_sub_le _ _
      _ ≤ S.eta + S.eta := add_le_add (S.step_feasible t) hXFeasible
      _ = 2 * S.eta := by ring

/-- Pathwise one-step star-convex descent with an explicit Nesterov residual. -/
theorem one_step_descent_bound
    (S : StarConvexPathGeometryContext V) :
    ∀ t,
      S.f (S.W (t + 1)) ≤
        S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hLemma13 := lemma13_interpolatedPoint_geometry S t
  rcases hLemma13 with ⟨hInterpWeight, hOptimalDir, hXWeightBound, hNextXBound⟩
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step t
  have hNextWeight : ‖S.W (t + 1)‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step (t + 1)
  have hTaylorInterp :=
    taylor_bound_of_LSmoothOnClosedBallUnderPair
      (continuousDualPairing (V := V))
      (f := S.f)
      (grad := S.fGrad)
      (L := S.L)
      (R := 1 / S.lambda)
      S.fderiv_eq
      S.assumption3_fLocalSmoothness.local_lipschitz
      hWeight
      hInterpWeight
  have hTaylorNext :=
    taylor_bound_of_LSmoothOnClosedBallUnderPair
      (continuousDualPairing (V := V))
      (f := S.f)
      (grad := S.fGrad)
      (L := S.L)
      (R := 1 / S.lambda)
      S.fderiv_eq
      S.assumption3_fLocalSmoothness.local_lipschitz
      hWeight
      hNextWeight
  have hUpdateBound : ‖S.W (t + 1) - S.W t‖ ≤ 2 * S.eta :=
    (S.proposition9_weight_and_update_bounds t).2
  have hGradDecomp :
      S.gradientLinear t (S.W (t + 1) - S.W t) =
        (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
          S.gradientLinear t (S.interpolatedPoint t - S.W t) +
          S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) := by
    have hSplit := grad_split_apply S t (S.W (t + 1) - S.interpolatedPoint t)
    have hDecomp :
        S.W (t + 1) - S.W t =
          (S.W (t + 1) - S.interpolatedPoint t) + (S.interpolatedPoint t - S.W t) := by
      abel_nf
    rw [hDecomp, LinearMap.map_add, hSplit]
    ring
  have hErrorTerm :
      S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) ≤
        2 * S.eta * S.nesterovErrorNorm t := by
    have hErr :
        S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) ≤
          S.nesterovErrorNorm t * ‖S.W (t + 1) - S.interpolatedPoint t‖ :=
      le_trans (le_abs_self _)
        (S.nesterovError_apply_le t (S.W (t + 1) - S.interpolatedPoint t))
    have hMul :
        S.nesterovErrorNorm t * ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤
          S.nesterovErrorNorm t * (2 * S.eta) := by
      gcongr
      exact S.nesterovErrorNorm_nonneg t
    nlinarith [hErr, hMul, hNextXBound]
  have hSmoothCompare :
      S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) ≤
        S.f (S.interpolatedPoint t) + 2 * S.L * S.eta ^ 2 := by
    have hCompLeftRaw := (abs_le.mp hTaylorInterp).1
    have hLinearInterp :
        S.gradientLinear t (S.interpolatedPoint t - S.W t) =
          (S.fGrad (S.W t)) (S.interpolatedPoint t) - (S.fGrad (S.W t)) (S.W t) := by
      simp [gradientLinear, SteepestDescentPathGeometryContext.grad]
    have hCompLeft :
        S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) ≤
          S.f (S.interpolatedPoint t) + S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 := by
      rw [hLinearInterp]
      have hTmp :
          -(S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2) ≤
            S.f (S.interpolatedPoint t) -
              (S.f (S.W t)
                + ((S.fGrad (S.W t)) (S.interpolatedPoint t) - (S.fGrad (S.W t)) (S.W t))) := by
        simpa [continuousDualPairing, SteepestDescentPathGeometryContext.grad] using hCompLeftRaw
      linarith
    have hQuad :
        S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤ 2 * S.L * S.eta ^ 2 := by
      have hSquare : ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤ (2 * S.eta) ^ 2 := by
        nlinarith [norm_nonneg (S.interpolatedPoint t - S.W t), hXWeightBound]
      have hHalfLNonneg : 0 ≤ S.L / 2 := by
        exact div_nonneg S.assumption3_fLocalSmoothness.nonneg (by norm_num)
      nlinarith [hSquare, hHalfLNonneg]
    have hQuad' :
        S.f (S.interpolatedPoint t) + S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤
          S.f (S.interpolatedPoint t) + 2 * S.L * S.eta ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hQuad (S.f (S.interpolatedPoint t)))
    exact le_trans hCompLeft hQuad'
  have hSmoothStep :
      S.f (S.W (t + 1)) ≤
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
    have hStepRightRaw := (abs_le.mp hTaylorNext).2
    have hLinearNext :
        S.gradientLinear t (S.W (t + 1) - S.W t) =
          (S.fGrad (S.W t)) (S.W (t + 1)) - (S.fGrad (S.W t)) (S.W t) := by
      simp [gradientLinear, SteepestDescentPathGeometryContext.grad]
    have hStepRight :
        S.f (S.W (t + 1)) ≤
          S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
      rw [hLinearNext]
      have hTmp :
          S.f (S.W (t + 1)) -
              (S.f (S.W t)
                + ((S.fGrad (S.W t)) (S.W (t + 1)) - (S.fGrad (S.W t)) (S.W t))) ≤
            S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
        simpa [continuousDualPairing, SteepestDescentPathGeometryContext.grad] using hStepRightRaw
      linarith
    have hQuad :
        S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ 2 * S.L * S.eta ^ 2 := by
      have hSquare : ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ (2 * S.eta) ^ 2 := by
        nlinarith [norm_nonneg (S.W (t + 1) - S.W t), hUpdateBound]
      have hHalfLNonneg : 0 ≤ S.L / 2 := by
        exact div_nonneg S.assumption3_fLocalSmoothness.nonneg (by norm_num)
      nlinarith [hSquare, hHalfLNonneg]
    have hQuad' :
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤
          S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hQuad (S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t)))
    exact le_trans hStepRight hQuad'
  calc
    S.f (S.W (t + 1))
      ≤ S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := hSmoothStep
    _ =
        S.f (S.W t) +
          ((S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
            S.gradientLinear t (S.interpolatedPoint t - S.W t) +
            S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)) +
          2 * S.L * S.eta ^ 2 := by rw [hGradDecomp]
    _ ≤ S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) + 2 * S.L * S.eta ^ 2 +
          2 * S.eta * S.nesterovErrorNorm t := by
            have hPairErr :
                (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
                  S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)
                  ≤ 2 * S.eta * S.nesterovErrorNorm t := by
              calc
                (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
                    S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)
                    ≤ 0 + 2 * S.eta * S.nesterovErrorNorm t := add_le_add hOptimalDir hErrorTerm
                _ = 2 * S.eta * S.nesterovErrorNorm t := by ring
            nlinarith [hPairErr]
    _ ≤ S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
          linarith [hSmoothCompare]

/-- Pathwise star-convex scalar recurrence. -/
theorem suboptimality_recurrence_step
    (S : StarConvexPathGeometryContext V) :
    ∀ t,
      S.suboptimality (t + 1) ≤
        (1 - S.lambda * S.eta) * S.suboptimality t
          + 4 * S.L * S.eta ^ 2
          + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hAlphaNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hStar :=
    star_convex_prop S (S.W t) (S.lambda * S.eta) hAlphaNonneg S.lambda_eta_le_one
  have hX :
      S.f (S.interpolatedPoint t) ≤
        (1 - S.lambda * S.eta) * S.f (S.W t) + (S.lambda * S.eta) * S.f S.WStar := by
    simpa [interpolatedPoint, SteepestDescentPathGeometryContext.stepCenter] using hStar
  have hLocal := S.one_step_descent_bound t
  dsimp [SteepestDescentPathGeometryContext.suboptimality]
  linarith

end PublicTheorems

end StarConvexPathGeometryContext

namespace StochasticStarConvexGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The pathwise interpolation point `X_t(ω)`. -/
def interpolatedPoint (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (ω : Ω) : V :=
  (S.path ω).interpolatedPoint t

/-- The batch-size-dependent `1 / sqrt(b)` coefficient in the star-convex bound. -/
def starConvexExpectedSuboptimalityMinibatchCoefficient
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma

/-- The batch-size-independent drift floor in the star-convex bound. -/
def starConvexExpectedSuboptimalityDriftFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta ^ 2

/-- The batch-size-dependent noise floor in the star-convex bound. -/
def starConvexExpectedSuboptimalityNoiseFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ

/-- The residual floor used by the expected star-convex bounds. -/
def starConvexExpectedSuboptimalityResidualFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
      + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta

end PublicDefinitions

section PrivateDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

-- No private definitions are introduced in this wrapper layer.

end PrivateDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

-- No private lemmas are needed beyond the pathwise wrappers.

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Pathwise displacement from the step center to `X_t(ω)`. -/
lemma interpolatedPoint_sub_stepCenter
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.interpolatedPoint t ω - S.stepCenter t ω = (S.lambda * S.eta) • S.WStar := by
  simpa [interpolatedPoint, StochasticSteepestDescentGeometryContext.stepCenter] using
    (S.path ω).interpolatedPoint_sub_stepCenter t

/-- Pathwise feasibility of the interpolation point. -/
lemma interpolatedPoint_feasible
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.interpolatedPoint t ω - S.stepCenter t ω‖ ≤ S.eta := by
  simpa [interpolatedPoint, StochasticSteepestDescentGeometryContext.stepCenter] using
    (S.path ω).interpolatedPoint_feasible t

/-- Pathwise radius-`1 / λ` bound for the interpolation point. -/
lemma interpolatedPoint_bound
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.interpolatedPoint t ω‖ ≤ 1 / S.lambda := by
  simpa [interpolatedPoint] using (S.path ω).interpolatedPoint_bound t

/-- Pathwise packaging of the interpolation geometry used in the descent proof. -/
theorem lemma13_interpolatedPoint_geometry
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.interpolatedPoint t ω‖ ≤ 1 / S.lambda ∧
      (S.C t ω) (S.W (t + 1) ω - S.interpolatedPoint t ω) ≤ 0 ∧
      ‖S.interpolatedPoint t ω - S.W t ω‖ ≤ 2 * S.eta ∧
      ‖S.W (t + 1) ω - S.interpolatedPoint t ω‖ ≤ 2 * S.eta := by
  simpa [interpolatedPoint] using (S.path ω).lemma13_interpolatedPoint_geometry t

/-- Pathwise one-step star-convex descent bound. -/
theorem one_step_descent_bound
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ t ω,
      S.f (S.W (t + 1) ω) ≤
        S.f (S.interpolatedPoint t ω) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω := by
  intro t ω
  simpa [interpolatedPoint] using (S.path ω).one_step_descent_bound t

/-- Pathwise scalar star-convex recurrence. -/
theorem suboptimality_recurrence_step
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ t ω,
      S.suboptimality (t + 1) ω ≤
        (1 - S.lambda * S.eta) * S.suboptimality t ω
          + 4 * S.L * S.eta ^ 2
          + 2 * S.eta * S.nesterovErrorNorm t ω := by
  intro t ω
  have h := (S.path ω).suboptimality_recurrence_step t
  simpa [SteepestDescentPathGeometryContext.suboptimality,
    StochasticSteepestDescentGeometryContext.suboptimality] using h

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
