import Mathlib
import SteepestDescentOptimizationBounds.DescentLemma
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds
import SteepestDescentOptimizationBounds.NesterovMomentumBounds

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file contains the deterministic and analytic star-convex layer used by the
project's expected-suboptimality development.

Upstream dependencies:

- `DescentLemma.lean` provides the local Taylor bound.
- `WeightAndUpdateBounds.lean` provides Proposition 9 and the common
  weight-decay geometry.
- `NesterovMomentumBounds.lean` provides the Nesterov residual split.

Downstream use:

- `StarConvexExpectedSuboptimality.lean` imports this file and adds the
  Corollary-11 stochastic assembly.
- `SteepestDescentScalingLaws/Commons.lean` imports the public coefficient
  definitions from this file.
-/

namespace StochasticStarConvexGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- Canonical pairing context for the actual continuous dual. -/
def continuousDualPairing :
    ContinuousDualPairingContext V (StrongDual ℝ V) where
  toLinear := by
    simpa using (ContinuousLinearMap.id ℝ (StrongDual ℝ V))
  opNorm_le := by
    intro xDual
    simp

/-- The linear functional induced by the current gradient. -/
def gradientLinear
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) : V →ₗ[ℝ] ℝ :=
  (S.grad t).toLinearMap

/-- The point `X_t = (1 - λη) W_t + λη W_*`. -/
def interpolatedPoint (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) : V :=
  S.stepCenter t + (S.lambda * S.eta) • S.WStar

/-- The initial suboptimality gap `f(W_0) - f(W_*)`. -/
def starConvexExpectedSuboptimalityInitialGap
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  S.suboptimality 0

/-- The batch-size-dependent `1 / sqrt(b)` coefficient in Theorem 14. -/
def starConvexExpectedSuboptimalityMinibatchCoefficient
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma

/-- The batch-size-independent drift floor accumulated in Theorem 14. -/
def starConvexExpectedSuboptimalityDriftFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta ^ 2

/-- The batch-size-dependent noise floor accumulated in Theorem 14. -/
def starConvexExpectedSuboptimalityNoiseFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ

/-- The residual floor `Z` from Theorem 14. -/
def starConvexExpectedSuboptimalityResidualFloor
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
      + (2 * S.beta / (1 - S.beta)) * S.initialGradNorm) * S.eta

end PublicDefinitions

section PrivateDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

-- No private definitions are introduced in this file.

end PrivateDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

/-- Unpacks the decomposition `∇f(W_t) = C_t + error_t` on a concrete vector. -/
private lemma grad_split_apply
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) (v : V) :
    S.gradientLinear t v = (S.C t) v + S.nesterovError t v := by
  have h := congrArg (fun f : StrongDual ℝ V => f v) (S.nesterovError_split t)
  simpa [gradientLinear] using h

/-- File-local star-convex interpolation inequality from Assumption 12. -/
private lemma star_convex_prop
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ W α, 0 ≤ α → α ≤ 1 →
      S.f ((1 - α) • W + α • S.WStar) ≤ (1 - α) * S.f W + α * S.f S.WStar :=
  Assumption12_StarConvexityAtReferencePoint.star_convex S.assumption12_starConvexity

/-- Shared scaling estimate for vectors already in the `1 / λ` ball. -/
private lemma scaled_norm_le_eta
    (S : StochasticStarConvexGeometryContext Ω V) {x : V}
    (hx : ‖x‖ ≤ 1 / S.lambda) :
    ‖(S.lambda * S.eta) • x‖ ≤ S.eta := by
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  calc
    ‖(S.lambda * S.eta) • x‖ = (S.lambda * S.eta) * ‖x‖ := by
      simp [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
      gcongr
    _ = S.eta := by
      field_simp [S.lambda_pos.ne']

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

/-- Rewrites the displacement from the step center to `X_t` as a scaled copy of `W_*`. -/
lemma interpolatedPoint_sub_stepCenter
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    S.interpolatedPoint t - S.stepCenter t = (S.lambda * S.eta) • S.WStar := by
  simp [StochasticStarConvexGeometryContext.interpolatedPoint]

/-- Shows that the auxiliary point `X_t` is feasible for the linear minimization step. -/
lemma interpolatedPoint_feasible
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    ‖S.interpolatedPoint t - S.stepCenter t‖ ≤ S.eta := by
  calc
    ‖S.interpolatedPoint t - S.stepCenter t‖ = ‖(S.lambda * S.eta) • S.WStar‖ := by
      rw [interpolatedPoint_sub_stepCenter]
    _ ≤ S.eta := by
      exact S.scaled_norm_le_eta S.WStar_bound

/-- The auxiliary point `X_t` also stays inside the primal `1 / λ` ball. -/
lemma interpolatedPoint_bound
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda := by
  have hWeight := S.weight_bound_from_feasible_step t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hDecayNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
  calc
    ‖S.interpolatedPoint t‖
      = ‖(1 - S.lambda * S.eta) • S.W t + (S.lambda * S.eta) • S.WStar‖ := by
          simp [StochasticStarConvexGeometryContext.interpolatedPoint,
            StochasticSteepestDescentGeometryContext.stepCenter]
    _ ≤ ‖(1 - S.lambda * S.eta) • S.W t‖ + ‖(S.lambda * S.eta) • S.WStar‖ := norm_add_le _ _
    _ = (1 - S.lambda * S.eta) * ‖S.W t‖ + (S.lambda * S.eta) * ‖S.WStar‖ := by
          simp [norm_smul, Real.norm_of_nonneg hDecayNonneg, Real.norm_of_nonneg hScaleNonneg]
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

/--
File-local packaging of the `X_t` geometry used in the one-step descent proof.
-/
theorem lemma13_interpolatedPoint_geometry
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda ∧
      (S.C t) (S.W (t + 1) - S.interpolatedPoint t) ≤ 0 ∧
      ‖S.interpolatedPoint t - S.W t‖ ≤ 2 * S.eta ∧
      ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤ 2 * S.eta := by
  have hInterp := interpolatedPoint_bound S t
  have hXFeasible := interpolatedPoint_feasible S t
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step t
  have hWeightCenter : ‖S.W t - S.stepCenter t‖ ≤ S.eta := by
    rw [StochasticSteepestDescentGeometryContext.weight_sub_stepCenter]
    exact S.scaled_norm_le_eta hWeight
  have hOptimal := S.step_optimal t (S.interpolatedPoint t) hXFeasible
  refine ⟨hInterp, ?_, ?_, ?_⟩
  · rw [(S.C t).map_sub]
    exact sub_nonpos.mpr hOptimal
  · calc
      ‖S.interpolatedPoint t - S.W t‖
          = ‖(S.interpolatedPoint t - S.stepCenter t) - (S.W t - S.stepCenter t)‖ := by
              abel_nf
      _ ≤ ‖S.interpolatedPoint t - S.stepCenter t‖ + ‖S.W t - S.stepCenter t‖ :=
          norm_sub_le _ _
      _ ≤ S.eta + S.eta := by
          exact add_le_add hXFeasible hWeightCenter
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
      _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.interpolatedPoint t - S.stepCenter t‖ :=
          norm_sub_le _ _
      _ ≤ S.eta + S.eta := by
          exact add_le_add (S.step_feasible t) hXFeasible
      _ = 2 * S.eta := by ring

/--
Concrete one-step descent theorem proved directly from the descent-lemma Taylor
bound plus Proposition 9 and the star-convex geometry lemmas.
-/
theorem one_step_descent_bound
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ t,
      S.f (S.W (t + 1)) ≤
        S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hLemma13 := lemma13_interpolatedPoint_geometry S t
  rcases hLemma13 with ⟨hInterpWeight, hOptimalDir, hXWeightBound, hNextXBound⟩
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda :=
    S.weight_bound_from_feasible_step t
  have hNextWeight : ‖S.W (t + 1)‖ ≤ 1 / S.lambda :=
    S.weight_bound_from_feasible_step (t + 1)
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
      S.nesterovError_apply_le t (S.W (t + 1) - S.interpolatedPoint t)
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
      simp [gradientLinear, StochasticSteepestDescentGeometryContext.grad]
    have hCompLeft :
        S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) ≤
          S.f (S.interpolatedPoint t) + S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 := by
      rw [hLinearInterp]
      have hTmp :
          -(S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2) ≤
            S.f (S.interpolatedPoint t) -
              (S.f (S.W t)
                + ((S.fGrad (S.W t)) (S.interpolatedPoint t) - (S.fGrad (S.W t)) (S.W t))) := by
        simpa [continuousDualPairing, StochasticSteepestDescentGeometryContext.grad] using hCompLeftRaw
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
      simp [gradientLinear, StochasticSteepestDescentGeometryContext.grad]
    have hStepRight :
        S.f (S.W (t + 1)) ≤
          S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
      rw [hLinearNext]
      have hTmp :
          S.f (S.W (t + 1)) -
              (S.f (S.W t)
                + ((S.fGrad (S.W t)) (S.W (t + 1)) - (S.fGrad (S.W t)) (S.W t))) ≤
            S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
        simpa [continuousDualPairing, StochasticSteepestDescentGeometryContext.grad] using hStepRightRaw
      linarith
    have hQuad :
        S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ 2 * S.L * S.eta ^ 2 := by
      have hSquare : ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ (2 * S.eta) ^ 2 := by
        nlinarith [norm_nonneg (S.W (t + 1) - S.W t), hUpdateBound]
      have hHalfLNonneg : 0 ≤ S.L / 2 := by
        exact div_nonneg S.assumption3_fLocalSmoothness.nonneg (by norm_num)
      nlinarith [hSquare, hHalfLNonneg]
    have hQuad' :
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) +
            S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤
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
                    ≤ 0 + 2 * S.eta * S.nesterovErrorNorm t := by
                      exact add_le_add hOptimalDir hErrorTerm
                _ = 2 * S.eta * S.nesterovErrorNorm t := by ring
            nlinarith [hPairErr]
    _ ≤ S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
          linarith [hSmoothCompare]

/--
Public scalar suboptimality recurrence extracted from the one-step descent
argument and Assumption 12.
-/
theorem suboptimality_recurrence_step
    (S : StochasticStarConvexGeometryContext Ω V) :
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
    simpa [StochasticStarConvexGeometryContext.interpolatedPoint,
      StochasticSteepestDescentGeometryContext.stepCenter] using hStar
  have hLocal := S.one_step_descent_bound t
  dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
  linarith

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
