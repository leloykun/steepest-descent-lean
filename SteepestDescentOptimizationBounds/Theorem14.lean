import Mathlib
import SteepestDescentOptimizationBounds.DescentLemma
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds
import SteepestDescentOptimizationBounds.NesterovMomentumBounds

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

open MeasureTheory

/-!
This file formalizes the final Theorem 14 assembly from
`content/ponder/steepest-descent-crit-bz/index.md`.

The geometric layer (Proposition 9 and Lemma 13) and the momentum/Nesterov
bounds now live in their own upstream files; this module keeps only the
one-step descent argument, the scalar recurrence, and the final assembly from
the concrete stochastic setup.
-/

noncomputable section

section AnalyticOneStep

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

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
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : V →ₗ[ℝ] ℝ :=
  (S.grad t).toLinearMap

/-- Unpacks the decomposition `∇f(W_t) = C_t + error_t` on a concrete vector. -/
private lemma grad_split_apply
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (v : V) :
    S.gradientLinear t v = (S.C t) v + S.nesterovError t v := by
  have h := congrArg (fun f : StrongDual ℝ V => f v) (S.nesterovError_split t)
  simpa [gradientLinear] using h

/-- Controls an `L/2 * n^2` term whenever `n ≤ 2η`. -/
private lemma quadratic_two_eta_bound
    (L η n : ℝ)
    (hL : 0 ≤ L) (hn : 0 ≤ n) (h : n ≤ 2 * η) :
    (L / 2) * n ^ 2 ≤ 2 * L * η ^ 2 := by
  have hSquare : n ^ 2 ≤ (2 * η) ^ 2 := by
    nlinarith
  calc
    (L / 2) * n ^ 2 ≤ (L / 2) * (2 * η) ^ 2 := by
      gcongr
    _ = 2 * L * η ^ 2 := by
      ring

/--
Concrete one-step descent theorem proved directly from the descent-lemma Taylor
bound plus Proposition 9 / Lemma 13 geometry.
-/
private theorem one_step_descent_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.f (S.W (t + 1)) ≤
        S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hProp9 := S.proposition9_weight_and_update_bounds t
  have hNextWeight : ‖S.W (t + 1)‖ ≤ 1 / S.lambda :=
    S.weight_bound_from_feasible_step (t + 1)
  have hInterpWeight : ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda :=
    S.interpolatedPoint_bound t
  have hLemma13 := S.lemma13_directional_and_distance_bounds t
  rcases hProp9 with ⟨hWeight, hUpdateBound⟩
  rcases hLemma13 with ⟨hOptimalDir, hWeightXBound, hNextXBound⟩
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
  have hGradDecomp :
      S.gradientLinear t (S.W (t + 1) - S.W t) =
        (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
          S.gradientLinear t (S.interpolatedPoint t - S.W t) +
          S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) := by
    have hSplit := S.grad_split_apply t (S.W (t + 1) - S.interpolatedPoint t)
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
    have h0 : 0 ≤ ‖S.interpolatedPoint t - S.W t‖ := norm_nonneg _
    have hQuad :=
      quadratic_two_eta_bound
        S.L S.eta ‖S.interpolatedPoint t - S.W t‖
        S.assumption3_fLocalSmoothness.nonneg h0 <| by
          simpa [norm_sub_rev] using hWeightXBound
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
    linarith
  have hSmoothStep :
      S.f (S.W (t + 1)) ≤
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
    have h0 : 0 ≤ ‖S.W (t + 1) - S.W t‖ := norm_nonneg _
    have hQuad :=
      quadratic_two_eta_bound
        S.L S.eta ‖S.W (t + 1) - S.W t‖
        S.assumption3_fLocalSmoothness.nonneg h0 hUpdateBound
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
    linarith
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

/-- The initial suboptimality gap `f(W_0) - f(W_*)`. -/
def theorem14InitialGap (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.suboptimality 0

/-- The batch-size-dependent `1 / sqrt(b)` coefficient in Theorem 14. -/
def theorem14MinibatchCoefficient (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma

/-- The batch-size-independent drift floor accumulated in Theorem 14. -/
def theorem14DriftFloor (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta ^ 2

/-- The batch-size-dependent noise floor accumulated in Theorem 14. -/
def theorem14NoiseFloor (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ

/-- The residual floor `Z` from Theorem 14. -/
def theorem14ResidualFloor (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
      + (2 * S.beta / (1 - S.beta)) * S.initialGradNorm) * S.eta

end StochasticSteepestDescentGeometryContext

end AnalyticOneStep

section Theorem14Recurrence

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/--
Combines the one-step descent inequality with Assumption 12 to obtain the scalar
suboptimality recurrence used in Theorem 14.
-/
private theorem suboptimality_recurrence_step
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.suboptimality (t + 1) ≤
        (1 - S.lambda * S.eta) * S.suboptimality t
          + 4 * S.L * S.eta ^ 2
          + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hAlphaNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hStar :=
    S.star_convex_prop (S.W t) (S.lambda * S.eta) hAlphaNonneg S.lambda_eta_le_one
  have hX :
      S.f (S.interpolatedPoint t) ≤
        (1 - S.lambda * S.eta) * S.f (S.W t) + (S.lambda * S.eta) * S.f S.WStar := by
    simpa [StochasticSteepestDescentGeometryContext.interpolatedPoint,
      StochasticSteepestDescentGeometryContext.stepCenter] using hStar
  have hLocal := S.one_step_descent_bound t
  dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
  linarith

/--
Theorem 14 in explicit-constants form, assuming the pointwise Corollary-11
bound.
-/
private theorem theorem14_expected_suboptimality_bound_of_corollary11
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * S.theorem14InitialGap
          + S.theorem14MinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.theorem14ResidualFloor := by
  intro T
  let a : ℝ := 1 - S.lambda * S.eta
  let k : ℝ := S.theorem14DriftFloor + S.theorem14NoiseFloor
  let d : ℝ := 2 * S.eta * S.initialGradNorm
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    nlinarith [S.lambda_eta_le_one]
  have haLeOne : a ≤ 1 := by
    dsimp [a]
    nlinarith [S.lambda_eta_nonneg]
  have haLtOne : a < 1 := by
    dsimp [a]
    nlinarith [S.lambda_eta_pos]
  have hkNonneg : 0 ≤ k := by
    dsimp [k, StochasticSteepestDescentGeometryContext.theorem14DriftFloor,
      StochasticSteepestDescentGeometryContext.theorem14NoiseFloor]
    have hNoiseNonneg :
        0 ≤ (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
      have hNumNonneg :
          0 ≤ 2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma := by
        have hEtaNonneg : 0 ≤ 2 * S.eta := by
          nlinarith [S.eta_pos]
        have hPrefNonneg : 0 ≤ 2 * S.eta * S.momentumNoisePrefactor := by
          exact mul_nonneg hEtaNonneg S.momentumNoisePrefactor_nonneg
        have hTripleNonneg : 0 ≤ 2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D := by
          exact mul_nonneg hPrefNonneg (Real.sqrt_nonneg _)
        exact mul_nonneg hTripleNonneg S.sigma_nonneg
      exact div_nonneg hNumNonneg (Real.sqrt_nonneg _)
    have hDriftNonneg : 0 ≤ 4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta ^ 2 := by
      have hFracNonneg : 0 ≤ S.beta ^ 2 / (1 - S.beta) := S.beta_sq_div_one_sub_nonneg
      have hCoeffNonneg : 0 ≤ 4 * (1 + S.beta ^ 2 / (1 - S.beta)) := by positivity
      have hFirstNonneg : 0 ≤ 4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L := by
        exact mul_nonneg hCoeffNonneg S.assumption3_fLocalSmoothness.nonneg
      exact mul_nonneg hFirstNonneg (sq_nonneg S.eta)
    linarith
  have hdNonneg : 0 ≤ d := by
    dsimp [d, StochasticSteepestDescentGeometryContext.initialGradNorm]
    have hEtaNonneg : 0 ≤ 2 * S.eta := by
      nlinarith [S.eta_pos]
    exact mul_nonneg hEtaNonneg (norm_nonneg _)
  have hRec :
      ∀ t,
        S.suboptimality (t + 1) ≤
          a * S.suboptimality t + k + d * S.beta ^ (t + 1) := by
    intro t
    have hStepRec := suboptimality_recurrence_step S t
    have hErr := hCor11 t
    have hScaledErr :
        2 * S.eta * S.nesterovErrorNorm t ≤
          2 * S.eta *
            (S.beta ^ (t + 1) * S.initialGradNorm
              + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
              + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
      exact mul_le_mul_of_nonneg_left hErr (by nlinarith [S.eta_pos])
    have hAux :
        4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t
          ≤ k + d * S.beta ^ (t + 1) := by
      dsimp [k, d, StochasticSteepestDescentGeometryContext.theorem14DriftFloor,
        StochasticSteepestDescentGeometryContext.theorem14NoiseFloor]
      ring_nf at hScaledErr ⊢
      nlinarith [hScaledErr]
    dsimp [a]
    linarith [hStepRec, hAux]
  have hUnrolled :=
    recurrence_unroll haNonneg haLeOne S.beta_nonneg hkNonneg hdNonneg hRec T
  have hkMul :
      k * geometricPrefix a T ≤ k * (1 / (1 - a)) := by
    gcongr
    exact geometricPrefix_le_inv_sub a haNonneg haLtOne T
  have hdMul :
      d * shiftedGeometricPrefix S.beta T ≤ d * (S.beta / (1 - S.beta)) := by
    gcongr
    exact shifted_geometricPrefix_le S.beta S.beta_nonneg S.beta_lt_one T
  have hMain :
      S.suboptimality T ≤
        a ^ T * S.theorem14InitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
    have : S.suboptimality T ≤
        a ^ T * S.suboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
      nlinarith [hUnrolled, hkMul, hdMul]
    simpa [StochasticSteepestDescentGeometryContext.theorem14InitialGap,
      StochasticSteepestDescentGeometryContext.suboptimality] using this
  have hOneMinusA : 1 - a = S.lambda * S.eta := by
    dsimp [a]
    ring
  calc
    S.suboptimality T
      ≤ a ^ T * S.theorem14InitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := hMain
    _ = (1 - S.lambda * S.eta) ^ T * S.theorem14InitialGap
          + S.theorem14MinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.theorem14ResidualFloor := by
            dsimp [a, k, d, StochasticSteepestDescentGeometryContext.theorem14MinibatchCoefficient,
              StochasticSteepestDescentGeometryContext.theorem14ResidualFloor,
              StochasticSteepestDescentGeometryContext.theorem14DriftFloor,
              StochasticSteepestDescentGeometryContext.theorem14NoiseFloor,
              StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            rw [hOneMinusA]
            field_simp [S.lambda_eta_ne_zero, S.lambda_pos.ne', S.eta_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

/-- Existential-constants form of Theorem 14, assuming Corollary 11. -/
private theorem theorem14_exists_constants_of_corollary11
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∃ X Y Z : ℝ,
      X = S.theorem14InitialGap ∧
      Y = S.theorem14MinibatchCoefficient ∧
      Z = S.theorem14ResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  refine ⟨S.theorem14InitialGap, S.theorem14MinibatchCoefficient, S.theorem14ResidualFloor,
    rfl, rfl, rfl, ?_⟩
  intro T
  simpa using theorem14_expected_suboptimality_bound_of_corollary11 S hCor11 T

end Theorem14Recurrence

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The direct Theorem-14 path from the concrete minibatch and Proposition-6 processes. -/
theorem theorem14_expected_suboptimality_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * S.theorem14InitialGap
          + S.theorem14MinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.theorem14ResidualFloor := by
  exact theorem14_expected_suboptimality_bound_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound S)

/-- Existential-constants form of the direct Theorem-14 bound. -/
theorem theorem14_exists_constants
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∃ X Y Z : ℝ,
      X = S.theorem14InitialGap ∧
      Y = S.theorem14MinibatchCoefficient ∧
      Z = S.theorem14ResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  exact theorem14_exists_constants_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound S)


end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
