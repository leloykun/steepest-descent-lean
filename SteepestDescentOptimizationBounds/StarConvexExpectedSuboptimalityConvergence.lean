import Mathlib
import SteepestDescentOptimizationBounds.StarConvexExpectedSuboptimality

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file packages convergence corollaries for the star-convex expected
suboptimality layer.

It sits directly on top of `StarConvexExpectedSuboptimality.lean` and rewrites
the base bound into the `θ = 1 - β` schedule form used by the project's
convergence statements.
-/

namespace StochasticStarConvexGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem momentumNoisePrefactor_le_theta_sqrt
    (S : StochasticStarConvexGeometryContext Ω V) :
    S.momentumNoisePrefactor ≤ Real.sqrt 2 * Real.sqrt (1 - S.beta) := by
  let a : ℝ := Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta
  let b : ℝ := 1 - S.beta
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (Real.sqrt_nonneg _) S.beta_nonneg
  have hbNonneg : 0 ≤ b := S.one_sub_beta_pos.le
  have hSumSqEq : a ^ 2 + b ^ 2 = (1 - S.beta) / (1 + S.beta) := by
    dsimp [a, b]
    calc
      (Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta) ^ 2 + (1 - S.beta) ^ 2
        = ((1 - S.beta) / (1 + S.beta)) * S.beta ^ 2 + (1 - S.beta) ^ 2 := by
            rw [show (Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta) ^ 2 =
                (Real.sqrt ((1 - S.beta) / (1 + S.beta))) ^ 2 * S.beta ^ 2 by ring]
            rw [Real.sq_sqrt S.one_sub_div_one_add_nonneg]
      _ = (1 - S.beta) / (1 + S.beta) := by
            field_simp [S.one_add_beta_pos.ne']
            ring
  have hSumSqLe : a ^ 2 + b ^ 2 ≤ 1 - S.beta := by
    rw [hSumSqEq]
    exact (div_le_iff₀ S.one_add_beta_pos).2 (by nlinarith [S.beta_nonneg, S.beta_le_one])
  have hABSq : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have hSq :
      (a + b) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt (1 - S.beta)) ^ 2 := by
    have hTmp : 2 * (a ^ 2 + b ^ 2) ≤ (Real.sqrt 2 * Real.sqrt (1 - S.beta)) ^ 2 := by
      calc
        2 * (a ^ 2 + b ^ 2) ≤ 2 * (1 - S.beta) := by
          nlinarith [hSumSqLe]
        _ = (Real.sqrt 2 * Real.sqrt (1 - S.beta)) ^ 2 := by
          rw [show (Real.sqrt 2 * Real.sqrt (1 - S.beta)) ^ 2 =
              (Real.sqrt 2) ^ 2 * (Real.sqrt (1 - S.beta)) ^ 2 by ring]
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt S.one_sub_beta_pos.le]
    exact le_trans hABSq hTmp
  have hNonnegRhs : 0 ≤ Real.sqrt 2 * Real.sqrt (1 - S.beta) := by positivity
  have hLe : a + b ≤ Real.sqrt 2 * Real.sqrt (1 - S.beta) := by
    nlinarith
  simpa [StochasticSteepestDescentGeometryContext.momentumNoisePrefactor, a, b] using hLe

private theorem starConvexExpectedSuboptimalityMinibatchCoefficient_le_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    S.starConvexExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ ≤
      (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
        / Real.sqrt S.batchSizeℝ := by
  have hScaleNonneg :
      0 ≤ (2 / S.lambda) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
    have hTwoDivLambdaNonneg : 0 ≤ 2 / S.lambda := by
      exact div_nonneg (by norm_num) S.lambda_pos.le
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg hTwoDivLambdaNonneg (Real.sqrt_nonneg _))
        S.sigma_nonneg)
      (Real.sqrt_nonneg _)
  calc
    S.starConvexExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
      = S.momentumNoisePrefactor
          * ((2 / S.lambda) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ) := by
            dsimp [StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityMinibatchCoefficient]
            ring
    _ ≤ (Real.sqrt 2 * Real.sqrt (1 - S.beta))
          * ((2 / S.lambda) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ) := by
            exact mul_le_mul_of_nonneg_right (momentumNoisePrefactor_le_theta_sqrt S) hScaleNonneg
    _ = (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
          / Real.sqrt S.batchSizeℝ := by
            ring

private theorem starConvexExpectedSuboptimalityDriftFloor_le_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    S.starConvexExpectedSuboptimalityDriftFloor ≤
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
  have hFrac :
      1 + S.beta ^ 2 / (1 - S.beta) ≤ 2 / (1 - S.beta) := by
    have hEq :
        1 + S.beta ^ 2 / (1 - S.beta) = (1 - S.beta + S.beta ^ 2) / (1 - S.beta) := by
      field_simp [S.one_sub_beta_ne_zero]
    rw [hEq]
    have hNumLe : 1 - S.beta + S.beta ^ 2 ≤ 2 := by
      nlinarith [S.beta_nonneg, S.beta_le_one]
    exact (div_le_div_of_nonneg_right hNumLe S.one_sub_beta_pos.le)
  have hEtaSq : S.eta ^ 2 ≤ S.eta / S.lambda := by
    have hMul : S.lambda * S.eta ^ 2 ≤ S.eta := by
      have h :=
        mul_le_mul_of_nonneg_right S.lambda_eta_le_one S.eta_pos.le
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
    have hMul' : S.eta ^ 2 * S.lambda ≤ S.eta := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hMul
    exact (le_div_iff₀ S.lambda_pos).2 hMul'
  calc
    S.starConvexExpectedSuboptimalityDriftFloor
      = 4 * S.L * (1 + S.beta ^ 2 / (1 - S.beta)) * S.eta ^ 2 := by
          dsimp [StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor]
          ring
    _ ≤ 4 * S.L * (2 / (1 - S.beta)) * S.eta ^ 2 := by
          have hCoeffNonneg : 0 ≤ 4 * S.L * S.eta ^ 2 := by
            exact mul_nonneg
              (mul_nonneg (by positivity) S.assumption3_fLocalSmoothness.nonneg) (sq_nonneg _)
          nlinarith [hFrac, hCoeffNonneg]
    _ ≤ 4 * S.L * (2 / (1 - S.beta)) * (S.eta / S.lambda) := by
          have hCoeffNonneg : 0 ≤ 4 * S.L * (2 / (1 - S.beta)) := by
            have hDivNonneg : 0 ≤ 2 / (1 - S.beta) := by
              exact div_nonneg (by norm_num) S.one_sub_beta_pos.le
            exact mul_nonneg
              (mul_nonneg (by norm_num) S.assumption3_fLocalSmoothness.nonneg) hDivNonneg
          nlinarith [hEtaSq, hCoeffNonneg]
    _ = (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
          field_simp [S.lambda_pos.ne', S.one_sub_beta_ne_zero]
          ring

private theorem starConvexExpectedSuboptimalityInitialGradFloor_le_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    ((2 * S.beta / (1 - S.beta)) * S.initialGradNorm) * S.eta ≤
      (2 * S.eta / (1 - S.beta)) * S.initialGradNorm := by
  have hFrac : 2 * S.beta / (1 - S.beta) ≤ 2 / (1 - S.beta) := by
    exact (div_le_div_of_nonneg_right (by nlinarith [S.beta_le_one]) S.one_sub_beta_pos.le)
  calc
    ((2 * S.beta / (1 - S.beta)) * S.initialGradNorm) * S.eta
      ≤ ((2 / (1 - S.beta)) * S.initialGradNorm) * S.eta := by
          have hCoeffNonneg : 0 ≤ S.initialGradNorm * S.eta := by
            exact mul_nonneg (by simp [StochasticSteepestDescentGeometryContext.initialGradNorm])
              S.eta_pos.le
          nlinarith [hFrac, hCoeffNonneg]
    _ = (2 * S.eta / (1 - S.beta)) * S.initialGradNorm := by
          field_simp [S.one_sub_beta_ne_zero]

private theorem starConvexExpectedSuboptimalityResidualFloor_le_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    S.starConvexExpectedSuboptimalityResidualFloor ≤
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
        + (2 * S.eta / (1 - S.beta)) * S.initialGradNorm := by
  have hDrift :
      ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))) * S.eta
        ≤ (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
    have hBase :
        1 + S.beta ^ 2 / (1 - S.beta) ≤ 2 / (1 - S.beta) := by
      have hEq :
          1 + S.beta ^ 2 / (1 - S.beta) = (1 - S.beta + S.beta ^ 2) / (1 - S.beta) := by
        field_simp [S.one_sub_beta_ne_zero]
      rw [hEq]
      have hNumLe : 1 - S.beta + S.beta ^ 2 ≤ 2 := by
        nlinarith [S.beta_nonneg, S.beta_le_one]
      exact (div_le_div_of_nonneg_right hNumLe S.one_sub_beta_pos.le)
    have hCoeffNonneg : 0 ≤ (4 * S.L / S.lambda) * S.eta := by
      exact mul_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num) S.assumption3_fLocalSmoothness.nonneg) S.lambda_pos.le)
        S.eta_pos.le
    have hScaled := mul_le_mul_of_nonneg_left hBase hCoeffNonneg
    calc
      ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))) * S.eta
        ≤ ((4 * S.L / S.lambda) * (2 / (1 - S.beta))) * S.eta := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hScaled
      _ = (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta := by
            field_simp [S.lambda_pos.ne', S.one_sub_beta_ne_zero]
            ring
  have hInit := starConvexExpectedSuboptimalityInitialGradFloor_le_theta_form S
  dsimp [StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityResidualFloor]
  linarith

private theorem one_sub_lambda_eta_pow_le_exp_neg_mul
    (S : StochasticStarConvexGeometryContext Ω V) (T : ℕ) :
    (1 - S.lambda * S.eta) ^ T ≤ Real.exp (-(S.lambda * S.eta * (T : ℝ))) := by
  by_cases hT : T = 0
  · subst hT
    simp
  · have hTPos : 0 < (T : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hT
    have hArgLe : S.eta * (S.lambda * (T : ℝ)) ≤ (T : ℝ) := by
      have hMul :=
        mul_le_mul_of_nonneg_right S.lambda_eta_le_one (show 0 ≤ (T : ℝ) by positivity)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hMul
    have hRaw :=
      Real.one_sub_div_pow_le_exp_neg
        (n := T) (t := S.eta * (S.lambda * (T : ℝ))) hArgLe
    have hDiv : S.eta * (S.lambda * (T : ℝ)) / (T : ℝ) = S.lambda * S.eta := by
      field_simp [hTPos.ne']
    simpa [hDiv, mul_assoc, mul_left_comm, mul_comm] using hRaw

private theorem starConvexExpectedSuboptimalityInitialGap_nonneg
    (S : StochasticStarConvexGeometryContext Ω V) :
    0 ≤ S.starConvexExpectedSuboptimalityInitialGap := by
  dsimp [StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityInitialGap,
    StochasticSteepestDescentGeometryContext.suboptimality]
  linarith [S.WStar_optimality (S.W 0)]

private theorem contraction_term_le_quarter_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    {ε : ℝ} {T : ℕ}
    (hε : 0 < ε)
    (hT :
      Real.log (4 * S.starConvexExpectedSuboptimalityInitialGap / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap ≤ ε / 4 := by
  by_cases hGapZero : S.starConvexExpectedSuboptimalityInitialGap = 0
  · simp [hGapZero]
    positivity
  have hGapNonneg : 0 ≤ S.starConvexExpectedSuboptimalityInitialGap := S.starConvexExpectedSuboptimalityInitialGap_nonneg
  have hGapPos : 0 < S.starConvexExpectedSuboptimalityInitialGap := by
    exact lt_of_le_of_ne hGapNonneg (by simpa [eq_comm] using hGapZero)
  have hRatioPos : 0 < 4 * S.starConvexExpectedSuboptimalityInitialGap / ε := by
    positivity
  have hLogLe : Real.log (4 * S.starConvexExpectedSuboptimalityInitialGap / ε) ≤ (T : ℝ) * (S.lambda * S.eta) := by
    exact (div_le_iff₀ S.lambda_eta_pos).1 hT
  have hRatioLeExp :
      4 * S.starConvexExpectedSuboptimalityInitialGap / ε ≤ Real.exp ((T : ℝ) * (S.lambda * S.eta)) := by
    exact (Real.log_le_iff_le_exp hRatioPos).1 hLogLe
  have hScaledGap :
      S.starConvexExpectedSuboptimalityInitialGap ≤ (ε / 4) * Real.exp ((T : ℝ) * (S.lambda * S.eta)) := by
    have hMul :=
      mul_le_mul_of_nonneg_left hRatioLeExp (show 0 ≤ ε / 4 by positivity)
    calc
      S.starConvexExpectedSuboptimalityInitialGap = (ε / 4) * (4 * S.starConvexExpectedSuboptimalityInitialGap / ε) := by
        field_simp [hε.ne']
      _ ≤ (ε / 4) * Real.exp ((T : ℝ) * (S.lambda * S.eta)) := hMul
  have hExp := one_sub_lambda_eta_pow_le_exp_neg_mul S T
  have hScaledExp :=
    mul_le_mul_of_nonneg_right hExp hGapPos.le
  calc
    (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap
      ≤ Real.exp (-(S.lambda * S.eta * (T : ℝ))) * S.starConvexExpectedSuboptimalityInitialGap := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hScaledExp
    _ ≤ Real.exp (-(S.lambda * S.eta * (T : ℝ)))
          * ((ε / 4) * Real.exp ((T : ℝ) * (S.lambda * S.eta))) := by
            gcongr
    _ = ε / 4 := by
          calc
            Real.exp (-(S.lambda * S.eta * (T : ℝ)))
                * ((ε / 4) * Real.exp ((T : ℝ) * (S.lambda * S.eta)))
              = (ε / 4) * (Real.exp (-(S.lambda * S.eta * (T : ℝ)))
                  * Real.exp ((T : ℝ) * (S.lambda * S.eta))) := by ring
            _ = (ε / 4) * Real.exp (-(S.lambda * S.eta * (T : ℝ))
                  + (T : ℝ) * (S.lambda * S.eta)) := by rw [← Real.exp_add]
            _ = ε / 4 := by
                  have hZero :
                      -(S.lambda * S.eta * (T : ℝ)) + (T : ℝ) * (S.lambda * S.eta) = 0 := by
                    ring
                  rw [hZero, Real.exp_zero, mul_one]

private theorem drift_term_le_quarter_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    {ε : ℝ}
    (hη :
      S.eta ≤ S.lambda * (1 - S.beta) * ε / (32 * S.L)) :
    (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta ≤ ε / 4 := by
  have hLpos : 0 < S.L := S.assumption3_fLocalSmoothness.pos
  have hCoeffNonneg : 0 ≤ (8 / (S.lambda * (1 - S.beta))) * S.L := by
    have hPrefNonneg : 0 ≤ 8 / (S.lambda * (1 - S.beta)) := by
      exact div_nonneg (by norm_num) (mul_nonneg S.lambda_pos.le S.one_sub_beta_pos.le)
    exact mul_nonneg hPrefNonneg hLpos.le
  have hMul := mul_le_mul_of_nonneg_left hη hCoeffNonneg
  calc
    (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
      = ((8 / (S.lambda * (1 - S.beta))) * S.L) * S.eta := by
          ring
    _ ≤ ((8 / (S.lambda * (1 - S.beta))) * S.L)
          * (S.lambda * (1 - S.beta) * ε / (32 * S.L)) := hMul
    _ = (8 * ε) / 32 := by
          field_simp [S.lambda_pos.ne', S.one_sub_beta_ne_zero, hLpos.ne']
    _ = ε / 4 := by ring

private theorem initial_grad_term_le_quarter_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    {ε : ℝ}
    (hη :
      S.eta ≤ (1 - S.beta) * ε / (8 * S.initialGradNorm)) :
    (2 * S.eta / (1 - S.beta)) * S.initialGradNorm ≤ ε / 4 := by
  by_cases hG : S.initialGradNorm = 0
  · have hEtaNonpos : S.eta ≤ 0 := by simpa [hG] using hη
    linarith [S.eta_pos, hEtaNonpos]
  have hCoeffNonneg : 0 ≤ (2 * S.initialGradNorm) / (1 - S.beta) := by
    have hNormNonneg : 0 ≤ S.initialGradNorm := by
      unfold StochasticSteepestDescentGeometryContext.initialGradNorm
      exact norm_nonneg _
    exact div_nonneg (by nlinarith) S.one_sub_beta_pos.le
  have hMul := mul_le_mul_of_nonneg_left hη hCoeffNonneg
  calc
    (2 * S.eta / (1 - S.beta)) * S.initialGradNorm
      = ((2 * S.initialGradNorm) / (1 - S.beta)) * S.eta := by
          field_simp [S.one_sub_beta_ne_zero]
    _ ≤ ((2 * S.initialGradNorm) / (1 - S.beta))
          * ((1 - S.beta) * ε / (8 * S.initialGradNorm)) := hMul
    _ = ε / 4 := by
          field_simp [S.one_sub_beta_ne_zero, hG]
          ring

private theorem theta_noise_term_le_quarter_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    {ε : ℝ}
    (hε : 0 < ε)
    (hTheta :
      1 - S.beta ≤ S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2)) :
    (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
      / Real.sqrt S.batchSizeℝ ≤ ε / 4 := by
  let N : ℝ :=
    (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
      / Real.sqrt S.batchSizeℝ
  have hNNonneg : 0 ≤ N := by
    dsimp [N]
    have hTwoDivLambdaNonneg : 0 ≤ 2 * Real.sqrt 2 / S.lambda := by
      exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) S.lambda_pos.le
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hTwoDivLambdaNonneg (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        S.sigma_nonneg)
      (Real.sqrt_nonneg _)
  by_cases hZero : S.D * S.sigma ^ 2 = 0
  · have hSplit : S.D = 0 ∨ S.sigma ^ 2 = 0 := mul_eq_zero.mp hZero
    have hNZero : N = 0 := by
      rcases hSplit with hD | hSigmaSq
      · dsimp [N]
        simp [hD]
      · have hSigma : S.sigma = 0 := by
          nlinarith
        dsimp [N]
        simp [hSigma]
    have : N ≤ ε / 4 := by
      rw [hNZero]
      positivity
    simpa [N] using this
  · have hProdNonneg : 0 ≤ S.D * S.sigma ^ 2 := by
      exact mul_nonneg S.D_nonneg (sq_nonneg S.sigma)
    have hDNe : S.D ≠ 0 := by
      intro hD
      apply hZero
      simp [hD]
    have hSigmaNe : S.sigma ≠ 0 := by
      intro hSigma
      apply hZero
      simp [hSigma]
    have hSqEq :
        N ^ 2 = (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ)) * (1 - S.beta) := by
      dsimp [N]
      have hCoeffSq : (2 * Real.sqrt 2 / S.lambda) ^ 2 = 8 / S.lambda ^ 2 := by
        field_simp [S.lambda_pos.ne']
        rw [Real.sq_sqrt (by positivity)]
        ring
      calc
        (((2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
            / Real.sqrt S.batchSizeℝ) ^ 2)
            = ((2 * Real.sqrt 2 / S.lambda) ^ 2)
                * (Real.sqrt (1 - S.beta) ^ 2)
                * (Real.sqrt S.D ^ 2)
                * S.sigma ^ 2
                / (Real.sqrt S.batchSizeℝ ^ 2) := by
                    ring
        _ = ((2 * Real.sqrt 2 / S.lambda) ^ 2) * (1 - S.beta) * S.D * S.sigma ^ 2 / S.batchSizeℝ := by
              rw [Real.sq_sqrt S.one_sub_beta_pos.le, Real.sq_sqrt S.D_nonneg,
                Real.sq_sqrt S.batchSizeℝ_pos.le]
        _ = (8 / S.lambda ^ 2) * (1 - S.beta) * S.D * S.sigma ^ 2 / S.batchSizeℝ := by
              rw [hCoeffSq]
        _ = (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ)) * (1 - S.beta) := by
              field_simp [S.lambda_pos.ne', S.batchSizeℝ_ne_zero]
    have hScaleNonneg : 0 ≤ 8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ) := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) S.D_nonneg) (sq_nonneg S.sigma))
        (mul_nonneg (sq_nonneg S.lambda) S.batchSizeℝ_pos.le)
    have hScaled :
        (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ)) * (1 - S.beta)
          ≤ (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ))
              * (S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hTheta hScaleNonneg
    have hSqLe : N ^ 2 ≤ (ε / 4) ^ 2 := by
      rw [hSqEq]
      calc
        (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ)) * (1 - S.beta)
          ≤ (8 * S.D * S.sigma ^ 2 / (S.lambda ^ 2 * S.batchSizeℝ))
              * (S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2)) := hScaled
        _ = (ε / 4) ^ 2 := by
              field_simp [S.lambda_pos.ne', S.batchSizeℝ_ne_zero, hDNe, hSigmaNe]
              ring
    have hTargetNonneg : 0 ≤ ε / 4 := by positivity
    have hLe : N ≤ ε / 4 := by
      nlinarith
    simpa [N] using hLe

/--
The expected-suboptimality bound in the `θ = 1 - β` form used by the
convergence schedule argument.
-/
theorem starConvexExpectedSuboptimality_bound_theta_form
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap
          + (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta
          + (2 * S.eta / (1 - S.beta)) * S.initialGradNorm
          + (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
  intro T
  have hBase := S.starConvexExpectedSuboptimality_bound T
  have hNoise := starConvexExpectedSuboptimalityMinibatchCoefficient_le_theta_form S
  have hResidual := starConvexExpectedSuboptimalityResidualFloor_le_theta_form S
  linarith

/--
If each of the four terms in the `θ`-form expected-suboptimality bound is at
most `ε / 4`, then the total suboptimality is at most `ε`.
-/
theorem starConvexExpectedSuboptimality_le_epsilon_of_termwise_budget
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hContraction :
      (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap ≤ ε / 4)
    (hDrift :
      (8 / (S.lambda * (1 - S.beta))) * S.L * S.eta ≤ ε / 4)
    (hInitialGrad :
      (2 * S.eta / (1 - S.beta)) * S.initialGradNorm ≤ ε / 4)
    (hNoise :
      (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
        / Real.sqrt S.batchSizeℝ ≤ ε / 4) :
    S.suboptimality T ≤ ε := by
  have hNoiseNonneg :
      0 ≤ (2 * Real.sqrt 2 / S.lambda) * Real.sqrt (1 - S.beta) * Real.sqrt S.D * S.sigma
        / Real.sqrt S.batchSizeℝ := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) S.lambda_pos.le)
            (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        S.sigma_nonneg)
      (Real.sqrt_nonneg _)
  have hQuarterNonneg : 0 ≤ ε / 4 := le_trans hNoiseNonneg hNoise
  have hBound := S.starConvexExpectedSuboptimality_bound_theta_form T
  linarith

/--
An exact convergence schedule guaranteeing that the expected suboptimality at
time `T` is at most `ε`.
-/
theorem starConvexExpectedSuboptimality_le_epsilon_of_schedule
    (S : StochasticStarConvexGeometryContext Ω V)
    (ε : ℝ) (T : ℕ)
    (hε : 0 < ε)
    (hTheta :
      1 - S.beta ≤ S.lambda ^ 2 * S.batchSizeℝ * ε ^ 2 / (128 * S.D * S.sigma ^ 2))
    (hEtaDrift :
      S.eta ≤ S.lambda * (1 - S.beta) * ε / (32 * S.L))
    (hEtaGrad :
      S.eta ≤ (1 - S.beta) * ε / (8 * S.initialGradNorm))
    (hT :
      Real.log (4 * S.starConvexExpectedSuboptimalityInitialGap / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    S.suboptimality T ≤ ε := by
  apply S.starConvexExpectedSuboptimality_le_epsilon_of_termwise_budget ε T
  · exact contraction_term_le_quarter_epsilon_of_schedule S hε hT
  · exact drift_term_le_quarter_epsilon_of_schedule S hEtaDrift
  · exact initial_grad_term_le_quarter_epsilon_of_schedule S hEtaGrad
  · exact theta_noise_term_le_quarter_epsilon_of_schedule S hε hTheta

/--
A practical schedule theorem: it suffices to choose `θ = 1 - β` below the
displayed `min` bound, choose `η` below the displayed `min` bound, and choose
`T` above the logarithmic threshold.
-/
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
          ((1 - S.beta) * ε / (8 * S.initialGradNorm)))
    (hT :
      Real.log (4 * S.starConvexExpectedSuboptimalityInitialGap / ε) / (S.lambda * S.eta) ≤ (T : ℝ)) :
    S.suboptimality T ≤ ε := by
  apply S.starConvexExpectedSuboptimality_le_epsilon_of_schedule ε T hε
  · exact le_trans hTheta (min_le_right _ _)
  · exact le_trans hEta (min_le_left _ _)
  · exact le_trans hEta (min_le_right _ _)
  · exact hT

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
