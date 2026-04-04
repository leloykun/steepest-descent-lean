import Mathlib
import SteepestDescentOptimizationBounds.StarConvexExpectedSuboptimality

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Schedule-form convergence layer for star-convex expected suboptimality.

Upstream dependencies:

- `StarConvexExpectedSuboptimality.lean` supplies the base expectation-level
  expected-suboptimality bound.

Downstream use:

- this file packages the schedule-facing convergence statements used by the
  public summaries and scaling-law layer.
-/

namespace StochasticStarConvexGeometryContext

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem momentumNoisePrefactor_le_sqrtTwo_mul_sqrtOneSubBeta
    (S : StochasticStarConvexGeometryContext Ω V) :
    S.momentumNoisePrefactor ≤ Real.sqrt 2 * Real.sqrt (1 - S.beta) := by
  have hDivSq :
      (S.beta / Real.sqrt (1 + S.beta)) ^ 2 ≤ (Real.sqrt S.beta) ^ 2 := by
    have hAux : (S.beta / Real.sqrt (1 + S.beta)) ^ 2 ≤ S.beta := by
      have hSqrtNe : Real.sqrt (1 + S.beta) ≠ 0 := Real.sqrt_ne_zero'.2 S.one_add_beta_pos
      field_simp [hSqrtNe]
      rw [Real.sq_sqrt S.one_add_beta_pos.le]
      nlinarith [S.beta_nonneg]
    have hBetaNonneg : 0 ≤ S.beta := S.beta_nonneg
    simpa [Real.sq_sqrt hBetaNonneg] using hAux
  have hDivNonneg : 0 ≤ S.beta / Real.sqrt (1 + S.beta) := by
    exact div_nonneg S.beta_nonneg (Real.sqrt_nonneg _)
  have hSqrtBetaNonneg : 0 ≤ Real.sqrt S.beta := by
    exact Real.sqrt_nonneg _
  have hDivLe : S.beta / Real.sqrt (1 + S.beta) ≤ Real.sqrt S.beta := by
    nlinarith
  have hProdSq :
      (Real.sqrt S.beta * Real.sqrt (1 - S.beta)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    calc
      (Real.sqrt S.beta * Real.sqrt (1 - S.beta)) ^ 2 = S.beta * (1 - S.beta) := by
        rw [pow_two]
        calc
          (Real.sqrt S.beta * Real.sqrt (1 - S.beta)) * (Real.sqrt S.beta * Real.sqrt (1 - S.beta))
              = (Real.sqrt S.beta * Real.sqrt S.beta) *
                  (Real.sqrt (1 - S.beta) * Real.sqrt (1 - S.beta)) := by
                    ring
          _ = S.beta * (1 - S.beta) := by
                rw [Real.mul_self_sqrt S.beta_nonneg, Real.mul_self_sqrt S.one_sub_beta_pos.le]
      _ ≤ (1 / 2 : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (S.beta - 1 / 2)]
  have hProdNonneg : 0 ≤ Real.sqrt S.beta * Real.sqrt (1 - S.beta) := by positivity
  have hProdLe : Real.sqrt S.beta * Real.sqrt (1 - S.beta) ≤ (1 / 2 : ℝ) := by
    nlinarith
  have hSumSq :
      (Real.sqrt S.beta + Real.sqrt (1 - S.beta)) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
    calc
      (Real.sqrt S.beta + Real.sqrt (1 - S.beta)) ^ 2
          = 1 + 2 * (Real.sqrt S.beta * Real.sqrt (1 - S.beta)) := by
              rw [pow_two]
              calc
                (Real.sqrt S.beta + Real.sqrt (1 - S.beta)) * (Real.sqrt S.beta + Real.sqrt (1 - S.beta))
                    = Real.sqrt S.beta * Real.sqrt S.beta
                        + Real.sqrt S.beta * Real.sqrt (1 - S.beta)
                        + (Real.sqrt (1 - S.beta) * Real.sqrt S.beta
                            + Real.sqrt (1 - S.beta) * Real.sqrt (1 - S.beta)) := by
                              ring
                _ = 1 + 2 * (Real.sqrt S.beta * Real.sqrt (1 - S.beta)) := by
                      rw [Real.mul_self_sqrt S.beta_nonneg, Real.mul_self_sqrt S.one_sub_beta_pos.le]
                      ring
      _ ≤ 1 + 2 * (1 / 2 : ℝ) := by nlinarith [hProdLe]
      _ = (Real.sqrt 2) ^ 2 := by
            rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
            norm_num
  have hSumNonneg : 0 ≤ Real.sqrt S.beta + Real.sqrt (1 - S.beta) := by positivity
  have hSqrtTwoNonneg : 0 ≤ Real.sqrt 2 := by positivity
  have hSumLe : Real.sqrt S.beta + Real.sqrt (1 - S.beta) ≤ Real.sqrt 2 := by
    nlinarith
  have hInner :
      S.beta / Real.sqrt (1 + S.beta) + Real.sqrt (1 - S.beta) ≤ Real.sqrt 2 := by
    linarith
  have hRewrite :
      S.momentumNoisePrefactor =
        Real.sqrt (1 - S.beta) *
          (S.beta / Real.sqrt (1 + S.beta) + Real.sqrt (1 - S.beta)) := by
    dsimp [StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
    rw [Real.sqrt_div S.one_sub_beta_pos.le (1 + S.beta)]
    nth_rewrite 2 [show 1 - S.beta = Real.sqrt (1 - S.beta) * Real.sqrt (1 - S.beta) by
      rw [Real.mul_self_sqrt S.one_sub_beta_pos.le]]
    ring
  calc
    S.momentumNoisePrefactor
      = Real.sqrt (1 - S.beta) *
          (S.beta / Real.sqrt (1 + S.beta) + Real.sqrt (1 - S.beta)) := hRewrite
    _ ≤ Real.sqrt (1 - S.beta) * Real.sqrt 2 := by
      exact mul_le_mul_of_nonneg_left hInner (by positivity)
    _ = Real.sqrt 2 * Real.sqrt (1 - S.beta) := by ring

private theorem one_add_betaSqDiv_le_two_div_oneSub
    (S : StochasticStarConvexGeometryContext Ω V) :
    1 + S.beta ^ 2 / (1 - S.beta) ≤ 2 / (1 - S.beta) := by
  have hPos : 0 < 1 - S.beta := S.one_sub_beta_pos
  have hNum : 1 - S.beta + S.beta ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (S.beta - 1), S.beta_nonneg, le_of_lt S.beta_lt_one]
  have hRewrite :
      1 + S.beta ^ 2 / (1 - S.beta) = (1 - S.beta + S.beta ^ 2) / (1 - S.beta) := by
    field_simp [S.one_sub_beta_ne_zero]
  rw [hRewrite]
  exact (div_le_div_iff_of_pos_right hPos).2 hNum

private theorem contraction_term_le_quarter
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hε : 0 < ε)
    (hT :
      Real.log (4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) ≤ ε / 4 := by
  have hGapNonneg : 0 ≤ S.toStochasticSteepestDescentGeometryContext.initialSuboptimality := by
    dsimp [StochasticSteepestDescentGeometryContext.initialSuboptimality]
    linarith [S.WStar_optimality S.W0]
  by_cases hGapZero : S.toStochasticSteepestDescentGeometryContext.initialSuboptimality = 0
  · have hQuarterNonneg : 0 ≤ ε / 4 := by positivity
    simpa [hGapZero] using hQuarterNonneg
  · have hGapPos : 0 < S.toStochasticSteepestDescentGeometryContext.initialSuboptimality :=
      lt_of_le_of_ne hGapNonneg (by
        intro h
        exact hGapZero h.symm)
    have hLogArgPos :
        0 < 4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε := by
      positivity
    have hLogLe :
        Real.log (4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε) ≤
          S.lambda * S.eta * T := by
      have hLambdaEtaPos : 0 < S.lambda * S.eta := S.lambda_eta_pos
      have hMul := (div_le_iff₀ hLambdaEtaPos).mp hT
      simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
    have hExpLe :
        4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε ≤
          Real.exp (S.lambda * S.eta * T) := by
      exact (Real.log_le_iff_le_exp hLogArgPos).mp hLogLe
    have hGapLe :
        S.toStochasticSteepestDescentGeometryContext.initialSuboptimality ≤
          (ε / 4) * Real.exp (S.lambda * S.eta * T) := by
      have hScale := mul_le_mul_of_nonneg_left hExpLe (show 0 ≤ ε / 4 by positivity)
      field_simp [hε.ne'] at hScale
      linarith
    have hPowExp :
        (1 - S.lambda * S.eta) ^ T ≤ Real.exp (-(S.lambda * S.eta * T)) := by
      have hBase :
          1 - S.lambda * S.eta ≤ Real.exp (-(S.lambda * S.eta)) :=
        Real.one_sub_le_exp_neg (S.lambda * S.eta)
      have hPow :
          (1 - S.lambda * S.eta) ^ T ≤ (Real.exp (-(S.lambda * S.eta))) ^ T := by
        exact pow_le_pow_left₀ S.one_sub_lambda_eta_nonneg hBase T
      calc
        (1 - S.lambda * S.eta) ^ T ≤ (Real.exp (-(S.lambda * S.eta))) ^ T := hPow
        _ = Real.exp (-(S.lambda * S.eta * T)) := by
              rw [← Real.exp_nat_mul]
              ring_nf
    have hMul :
        Real.exp (-(S.lambda * S.eta * T))
          * S.toStochasticSteepestDescentGeometryContext.initialSuboptimality ≤ ε / 4 := by
      have hScaled :
          Real.exp (-(S.lambda * S.eta * T))
            * S.toStochasticSteepestDescentGeometryContext.initialSuboptimality
            ≤
              Real.exp (-(S.lambda * S.eta * T))
                * ((ε / 4) * Real.exp (S.lambda * S.eta * T)) := by
        exact mul_le_mul_of_nonneg_left hGapLe (Real.exp_nonneg _)
      have hCancel :
          (ε / 4) * Real.exp (S.lambda * S.eta * T) * Real.exp (-(S.lambda * S.eta * T)) = ε / 4 := by
        calc
          (ε / 4) * Real.exp (S.lambda * S.eta * T) * Real.exp (-(S.lambda * S.eta * T))
              = (ε / 4) * (Real.exp (S.lambda * S.eta * T) * Real.exp (-(S.lambda * S.eta * T))) := by
                  ring
          _ = (ε / 4) * Real.exp ((S.lambda * S.eta * T) + (-(S.lambda * S.eta * T))) := by
                rw [← Real.exp_add]
          _ = ε / 4 := by simp
      calc
        Real.exp (-(S.lambda * S.eta * T))
            * S.toStochasticSteepestDescentGeometryContext.initialSuboptimality
          ≤ Real.exp (-(S.lambda * S.eta * T)) * ((ε / 4) * Real.exp (S.lambda * S.eta * T)) := by
              gcongr
        _ = ε / 4 := by
              rw [mul_assoc]
              simpa [mul_assoc, mul_left_comm, mul_comm] using hCancel
    calc
      (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
        ≤ Real.exp (-(S.lambda * S.eta * T))
            * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) := by
              gcongr
      _ ≤ ε / 4 := hMul

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The expected-suboptimality bound in the `θ = 1 - β` schedule form. -/
theorem starConvexExpectedSuboptimality_bound_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ T,
      (∫ ω, S.suboptimality T ω ∂S.μ) ≤
        (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
          + (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ := by
  intro T
  have hBase := S.starConvexExpectedSuboptimality_bound T
  have hDrift :
      ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))) * S.eta
        ≤ (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
    have hCoeff :
        1 + S.beta ^ 2 / (1 - S.beta) ≤ 2 / (1 - S.beta) :=
      one_add_betaSqDiv_le_two_div_oneSub S
    have hScaleNonneg : 0 ≤ (4 * S.L / S.lambda) * S.eta := by
      have hNum : 0 ≤ 4 * S.L := by nlinarith [S.L_pos]
      exact mul_nonneg (div_nonneg hNum S.lambda_pos.le) S.eta_pos.le
    have hMul := mul_le_mul_of_nonneg_left hCoeff hScaleNonneg
    calc
      ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))) * S.eta
        = ((4 * S.L / S.lambda) * S.eta) * (1 + S.beta ^ 2 / (1 - S.beta)) := by ring
      _ ≤ ((4 * S.L / S.lambda) * S.eta) * (2 / (1 - S.beta)) := hMul
      _ = (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
            field_simp [S.lambda_pos.ne', S.one_sub_beta_ne_zero]
            ring
  have hInitialGrad :
      ((2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta
        ≤ (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError := by
    have hBetaLeOne : S.beta ≤ 1 := le_of_lt S.beta_lt_one
    have hScaleNonneg : 0 ≤ ((2 * S.eta) / (1 - S.beta)) * S.initialExpectedMomentumError := by
      have hNum : 0 ≤ 2 * S.eta := by nlinarith [S.eta_pos]
      exact mul_nonneg (div_nonneg hNum S.one_sub_beta_pos.le) S.initialExpectedMomentumError_nonneg
    have hMul := mul_le_mul_of_nonneg_right hBetaLeOne hScaleNonneg
    calc
      ((2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta
        = S.beta * (((2 * S.eta) / (1 - S.beta)) * S.initialExpectedMomentumError) := by
            field_simp [S.one_sub_beta_ne_zero]
      _ ≤ ((2 * S.eta) / (1 - S.beta)) * S.initialExpectedMomentumError := by
            simpa using hMul
  have hResidual :
      (((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
          + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta)
        ≤ (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
            + (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError := by
    nlinarith [hDrift, hInitialGrad]
  calc
    (∫ ω, S.suboptimality T ω ∂S.μ)
      ≤ (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ
          + (((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
                + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta) := hBase
    _ ≤ (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ
          + ((8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
              + (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError) := by
            gcongr
    _ = (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
          + (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ := by
            ring

/-- Termwise-budget convergence criterion for expected suboptimality. -/
theorem starConvexExpectedSuboptimality_le_epsilon_of_termwise_budget
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hContraction :
      (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) ≤ ε / 4)
    (hDrift :
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta ≤ ε / 4)
    (hInitialGrad :
      (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError ≤ ε / 4)
    (hNoise :
      ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
        / Real.sqrt S.batchSizeℝ ≤ ε / 4) :
    (∫ ω, S.suboptimality T ω ∂S.μ) ≤ ε := by
  have hBound := S.starConvexExpectedSuboptimality_bound_theta_form T
  nlinarith

/-- Exact schedule criterion for expected suboptimality. -/
theorem starConvexExpectedSuboptimality_le_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hε : 0 < ε)
    (hTheta :
      1 - S.beta ≤ S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2))
    (hEtaDrift :
      S.eta ≤ S.lambda * (1 - S.beta) * ε / (32 * S.L))
    (hEtaGrad :
      S.eta ≤ (1 - S.beta) * ε / (8 * S.initialExpectedMomentumError))
    (hT :
      Real.log (4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    (∫ ω, S.suboptimality T ω ∂S.μ) ≤ ε := by
  have hContraction := contraction_term_le_quarter S ε T hε hT
  have hDrift :
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta ≤ ε / 4 := by
    have hScaleNonneg : 0 ≤ (8 * S.L) / (S.lambda * (1 - S.beta)) := by
      have hNum : 0 ≤ 8 * S.L := by nlinarith [S.L_pos]
      have hDen : 0 ≤ S.lambda * (1 - S.beta) := by nlinarith [S.lambda_pos, S.one_sub_beta_pos]
      exact div_nonneg hNum hDen
    have hMul := mul_le_mul_of_nonneg_left hEtaDrift hScaleNonneg
    calc
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
        = ((8 * S.L) / (S.lambda * (1 - S.beta))) * S.eta := by ring
      _ ≤ ((8 * S.L) / (S.lambda * (1 - S.beta)))
            * (S.lambda * (1 - S.beta) * ε / (32 * S.L)) := hMul
      _ = ε / 4 := by
            field_simp [S.lambda_pos.ne', S.one_sub_beta_ne_zero, S.L_pos.ne']
            ring
  have hInitialGrad :
      (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError ≤ ε / 4 := by
    by_cases hGradZero : S.initialExpectedMomentumError = 0
    · have hQuarterNonneg : 0 ≤ ε / 4 := by positivity
      simpa [hGradZero] using hQuarterNonneg
    · have hScaleNonneg : 0 ≤ (2 * S.initialExpectedMomentumError) / (1 - S.beta) := by
        have hNum : 0 ≤ 2 * S.initialExpectedMomentumError := by
          exact mul_nonneg (by norm_num) S.initialExpectedMomentumError_nonneg
        exact div_nonneg hNum S.one_sub_beta_pos.le
      have hMul := mul_le_mul_of_nonneg_left hEtaGrad hScaleNonneg
      calc
        (2 * S.eta / (1 - S.beta)) * S.initialExpectedMomentumError
          = ((2 * S.initialExpectedMomentumError) / (1 - S.beta)) * S.eta := by ring
        _ ≤ ((2 * S.initialExpectedMomentumError) / (1 - S.beta))
              * ((1 - S.beta) * ε / (8 * S.initialExpectedMomentumError)) := hMul
        _ = ε / 4 := by
              field_simp [hGradZero, S.one_sub_beta_ne_zero]
              ring
  have hNoise :
      ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
        / Real.sqrt S.batchSizeℝ ≤ ε / 4 := by
    have hPref := momentumNoisePrefactor_le_sqrtTwo_mul_sqrtOneSubBeta S
    have hThetaNoise :
        (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
          / Real.sqrt S.batchSizeℝ ≤ ε / 4 := by
      by_cases hDZero : S.D = 0
      · have hQuarterNonneg : 0 ≤ ε / 4 := by positivity
        simpa [hDZero] using hQuarterNonneg
      by_cases hSigmaZero : S.sigma = 0
      · have hQuarterNonneg : 0 ≤ ε / 4 := by positivity
        simpa [hSigmaZero] using hQuarterNonneg
      have hDPos : 0 < S.D := by
        exact lt_of_le_of_ne S.D_nonneg (by
          intro h
          exact hDZero h.symm)
      have hSigmaPos : 0 < S.sigma := by
        exact lt_of_le_of_ne S.sigma_nonneg (by
          intro h
          exact hSigmaZero h.symm)
      have hNumSq :
          ((2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ) ^ 2 ≤ (ε / 4) ^ 2 := by
        have hSquare :
            ((2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
                / Real.sqrt S.batchSizeℝ) ^ 2
              = (8 * (1 - S.beta) * S.D * S.sigma ^ 2) / (S.lambda ^ 2 * S.batchSizeℝ) := by
          field_simp [S.lambda_pos.ne', S.sqrt_batchSizeℝ_ne_zero]
          rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2),
            Real.sq_sqrt S.one_sub_beta_pos.le, Real.sq_sqrt S.D_nonneg,
            Real.sq_sqrt S.batchSizeℝ_pos.le]
          field_simp [S.batchSizeℝ_ne_zero]
          ring
        have hQuarter :
            (ε / 4) ^ 2 = ε ^ 2 / 16 := by ring
        rw [hSquare, hQuarter]
        have hScaleNonneg :
            0 ≤ (8 * S.D * S.sigma ^ 2) / (S.lambda ^ 2 * S.batchSizeℝ) := by
          apply div_nonneg
          · positivity
          · exact mul_nonneg (sq_nonneg S.lambda) S.batchSizeℝ_pos.le
        have hScaled := mul_le_mul_of_nonneg_left hTheta hScaleNonneg
        calc
          (8 * (1 - S.beta) * S.D * S.sigma ^ 2) / (S.lambda ^ 2 * S.batchSizeℝ)
            = ((8 * S.D * S.sigma ^ 2) / (S.lambda ^ 2 * S.batchSizeℝ)) * (1 - S.beta) := by
                ring
          _ ≤ ((8 * S.D * S.sigma ^ 2) / (S.lambda ^ 2 * S.batchSizeℝ))
                * (S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2)) := hScaled
          _ = ε ^ 2 / 16 := by
                field_simp [S.lambda_pos.ne', S.batchSizeℝ_ne_zero, hDZero, hSigmaZero]
                ring
      have hNoiseNonneg :
          0 ≤ (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
            / Real.sqrt S.batchSizeℝ := by
        have hNumNonneg :
            0 ≤ (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma := by
          have hLeft : 0 ≤ 2 * Real.sqrt 2 / S.lambda := by
            apply div_nonneg
            · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
            · exact S.lambda_pos.le
          have hLeftMid : 0 ≤ (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) := by
            exact mul_nonneg hLeft (Real.sqrt_nonneg _)
          have hLeftMidD :
              0 ≤ ((2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta)) * Real.sqrt S.D := by
            exact mul_nonneg hLeftMid (Real.sqrt_nonneg _)
          exact mul_nonneg hLeftMidD S.sigma_nonneg
        exact div_nonneg hNumNonneg (Real.sqrt_nonneg _)
      have hQuarterNonneg : 0 ≤ ε / 4 := by positivity
      nlinarith
    have hScaleNonneg :
        0 ≤ ((2 / S.lambda) * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
      have hNumNonneg : 0 ≤ (2 / S.lambda) * Real.sqrt S.D * S.sigma := by
        have hLeft : 0 ≤ 2 / S.lambda := by
          apply div_nonneg
          · norm_num
          · exact S.lambda_pos.le
        exact mul_nonneg (mul_nonneg hLeft (Real.sqrt_nonneg _)) S.sigma_nonneg
      exact div_nonneg hNumNonneg (Real.sqrt_nonneg _)
    have hMul := mul_le_mul_of_nonneg_right hPref hScaleNonneg
    have hBoundExact :
        ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
          / Real.sqrt S.batchSizeℝ ≤
            (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hMul
    exact le_trans hBoundExact hThetaNoise
  exact S.starConvexExpectedSuboptimality_le_epsilon_of_termwise_budget
    ε T hContraction hDrift hInitialGrad hNoise

/-- Practical min-form schedule criterion for expected suboptimality. -/
theorem starConvexExpectedSuboptimality_le_epsilon_of_min_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hε : 0 < ε)
    (hTheta :
      1 - S.beta ≤
        min 1 (S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2)))
    (hEta :
      S.eta ≤
        min
          (S.lambda * (1 - S.beta) * ε / (32 * S.L))
          ((1 - S.beta) * ε / (8 * S.initialExpectedMomentumError)))
    (hT :
      Real.log (4 * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality) / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    (∫ ω, S.suboptimality T ω ∂S.μ) ≤ ε := by
  refine S.starConvexExpectedSuboptimality_le_epsilon_of_schedule ε T hε ?_ ?_ ?_ hT
  · exact le_trans hTheta (min_le_right _ _)
  · exact le_trans hEta (min_le_left _ _)
  · exact le_trans hEta (min_le_right _ _)

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
