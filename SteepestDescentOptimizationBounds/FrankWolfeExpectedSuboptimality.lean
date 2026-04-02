import Mathlib
import SteepestDescentOptimizationBounds.FrankWolfe

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file formalizes the Frank-Wolfe expected suboptimality layer under the
FW-KL assumption.

Upstream dependencies:

- `FrankWolfe.lean` provides the deterministic Frank-Wolfe one-step descent
  theorem.
- `NesterovMomentumBounds.lean`, imported transitively through `FrankWolfe`,
  provides the
  Corollary-11 pointwise tracking bound.

Downstream use:

- later Frank-Wolfe convergence and scaling-law layers can reuse the public
  suboptimality recurrence and the loose Theorem-14-style bound from this file.
-/

namespace StochasticFrankWolfeKLGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- The initial Frank-Wolfe expected-suboptimality gap `f(W_0) - f(W_*)`. -/
def frankWolfeExpectedSuboptimalityInitialGap
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  S.suboptimality 0

/-- The batch-size-dependent `1 / sqrt(b)` coefficient in the loose FW-KL bound. -/
def frankWolfeExpectedSuboptimalityMinibatchCoefficient
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  (2 / (S.muFW * S.lambda)) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma

/-- The drift floor appearing before the geometric-sum simplification. -/
def frankWolfeExpectedSuboptimalityDriftFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  2 * S.L * S.eta ^ 2 * (1 + 2 * S.beta ^ 2 / (1 - S.beta))

/-- The batch-size-dependent noise floor appearing before the geometric-sum simplification. -/
def frankWolfeExpectedSuboptimalityNoiseFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ

/-- The residual floor `Z` in the loose FW-KL expected-suboptimality bound. -/
def frankWolfeExpectedSuboptimalityResidualFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  ((2 * S.beta / (1 - S.beta)) * S.initialGradNorm
      + (2 * S.L / (S.muFW * S.lambda)) * (1 + 2 * S.beta ^ 2 / (1 - S.beta))) * S.eta

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

/-- Loose FW-KL expected-suboptimality bound after plugging in Corollary 11. -/
private theorem frankWolfeExpectedSuboptimality_bound_of_corollary11
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.muFW * S.lambda * S.eta) ^ T * S.frankWolfeExpectedSuboptimalityInitialGap
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
  intro T
  let a : ℝ := 1 - S.muFW * S.lambda * S.eta
  let k : ℝ :=
    S.frankWolfeExpectedSuboptimalityDriftFloor + S.frankWolfeExpectedSuboptimalityNoiseFloor
  let d : ℝ := 2 * S.eta * S.initialGradNorm
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    nlinarith [S.muFW_lambda_eta_le_one]
  have haLeOne : a ≤ 1 := by
    dsimp [a]
    nlinarith [S.muFW_lambda_eta_nonneg]
  have haLtOne : a < 1 := by
    dsimp [a]
    nlinarith [S.muFW_lambda_eta_pos]
  have hkNonneg : 0 ≤ k := by
    dsimp [k, StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityDriftFloor,
      StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityNoiseFloor]
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
    have hDriftNonneg :
        0 ≤ 2 * S.L * S.eta ^ 2 * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
      have hFracNonneg : 0 ≤ 2 * S.beta ^ 2 / (1 - S.beta) := by
        exact div_nonneg (by positivity) S.one_sub_beta_pos.le
      have hCoeffNonneg : 0 ≤ 1 + 2 * S.beta ^ 2 / (1 - S.beta) := by
        nlinarith
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) S.assumption3_fLocalSmoothness.nonneg)
          (sq_nonneg _))
        hCoeffNonneg
    linarith
  have hdNonneg : 0 ≤ d := by
    dsimp [d, StochasticSteepestDescentGeometryContext.initialGradNorm]
    exact mul_nonneg (by nlinarith [S.eta_pos]) (norm_nonneg _)
  have hRec :
      ∀ t,
        S.suboptimality (t + 1) ≤ a * S.suboptimality t + k + d * S.beta ^ (t + 1) := by
    intro t
    have hErrParent :
        ∀ n,
          S.toStochasticFrankWolfeGeometryContext.nesterovErrorNorm n ≤
              S.beta ^ (n + 1) * S.initialGradNorm
                + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
      intro n
      simpa using hCor11 n
    have hStepBase := S.toStochasticFrankWolfeGeometryContext.one_step_descent_fwGap t
    have hScaledErr :
        2 * S.eta * S.toStochasticFrankWolfeGeometryContext.nesterovErrorNorm t ≤
          2 * S.eta *
            (S.beta ^ (t + 1) * S.initialGradNorm
              + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
              + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
      exact mul_le_mul_of_nonneg_left (hErrParent t) (by nlinarith [S.eta_pos])
    have hStep :
        S.f (S.W (t + 1)) ≤
          S.f (S.W t)
            - S.lambda * S.eta * S.frankWolfeGap t
            + 2 * S.eta *
                (S.beta ^ (t + 1) * S.initialGradNorm
                  + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                  + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
            + 2 * S.L * S.eta ^ 2 := by
      linarith [hStepBase, hScaledErr]
    have hGap :
        S.muFW * S.suboptimality t ≤ S.frankWolfeGap t := by
      simpa [StochasticSteepestDescentGeometryContext.suboptimality,
        StochasticFrankWolfeGeometryContext.frankWolfeGap,
        StochasticFrankWolfeGeometryContext.frankWolfeGapAt,
        StochasticFrankWolfeGeometryContext.constraintBall,
        StochasticSteepestDescentGeometryContext.grad] using
        S.assumptionFrankWolfeKL.gap_lower_bound t
    have hGapMul :
        (S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar)) ≤
          (S.lambda * S.eta) * S.frankWolfeGap t := by
      exact mul_le_mul_of_nonneg_left hGap S.lambda_eta_nonneg
    have hGapScaled :
        -S.lambda * S.eta * S.frankWolfeGap t ≤
          -(S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar)) := by
      have hNeg := neg_le_neg hGapMul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hNeg
    have hStepRec :
        S.suboptimality (t + 1) ≤
          (1 - S.muFW * S.lambda * S.eta) * S.suboptimality t
            + 2 * S.eta *
                (S.beta ^ (t + 1) * S.initialGradNorm
                  + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                  + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
            + 2 * S.L * S.eta ^ 2 := by
      dsimp [StochasticSteepestDescentGeometryContext.suboptimality] at hGap ⊢
      linarith [hStep, hGapScaled]
    have hAux :
        2 * S.eta *
            (S.beta ^ (t + 1) * S.initialGradNorm
              + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
              + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
          + 2 * S.L * S.eta ^ 2
        ≤ k + d * S.beta ^ (t + 1) := by
      dsimp [k, d, StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityDriftFloor,
        StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityNoiseFloor]
      ring_nf
      nlinarith
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
        a ^ T * S.frankWolfeExpectedSuboptimalityInitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
    have : S.suboptimality T ≤
        a ^ T * S.suboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
      nlinarith [hUnrolled, hkMul, hdMul]
    simpa [StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityInitialGap,
      StochasticSteepestDescentGeometryContext.suboptimality] using this
  have hOneMinusA : 1 - a = S.muFW * S.lambda * S.eta := by
    dsimp [a]
    ring
  calc
    S.suboptimality T
      ≤ a ^ T * S.frankWolfeExpectedSuboptimalityInitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := hMain
    _ = (1 - S.muFW * S.lambda * S.eta) ^ T * S.frankWolfeExpectedSuboptimalityInitialGap
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
            dsimp [a, k, d, StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityMinibatchCoefficient,
              StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityResidualFloor,
              StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityDriftFloor,
              StochasticFrankWolfeKLGeometryContext.frankWolfeExpectedSuboptimalityNoiseFloor,
              StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            rw [hOneMinusA]
            field_simp [S.muFW_lambda_eta_ne_zero, S.muFW_pos.ne', S.lambda_pos.ne', S.eta_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

/-- Existential-constants form of the loose FW-KL expected-suboptimality bound. -/
private theorem frankWolfeExpectedSuboptimality_existsConstants_of_corollary11
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∃ X Y Z : ℝ,
      X = S.frankWolfeExpectedSuboptimalityInitialGap ∧
      Y = S.frankWolfeExpectedSuboptimalityMinibatchCoefficient ∧
      Z = S.frankWolfeExpectedSuboptimalityResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤ (1 - S.muFW * S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  refine ⟨S.frankWolfeExpectedSuboptimalityInitialGap, S.frankWolfeExpectedSuboptimalityMinibatchCoefficient,
    S.frankWolfeExpectedSuboptimalityResidualFloor, rfl, rfl, rfl, ?_⟩
  intro T
  simpa using frankWolfeExpectedSuboptimality_bound_of_corollary11 S hCor11 T

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

/-- The FW-KL assumption lower-bounds the Frank-Wolfe gap by the suboptimality gap. -/
theorem frankWolfeGap_ge_muFW_mul_suboptimality
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ t, S.muFW * S.suboptimality t ≤ S.frankWolfeGap t := by
  intro t
  simpa [StochasticSteepestDescentGeometryContext.suboptimality,
    StochasticFrankWolfeGeometryContext.frankWolfeGap,
    StochasticFrankWolfeGeometryContext.frankWolfeGapAt,
    StochasticFrankWolfeGeometryContext.constraintBall,
    StochasticSteepestDescentGeometryContext.grad] using
    S.assumptionFrankWolfeKL.gap_lower_bound t

/-- Pointwise Frank-Wolfe expected-suboptimality recurrence under a tracking envelope. -/
theorem frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (err : ℕ → ℝ)
    (hErr : ∀ t, S.nesterovErrorNorm t ≤ err t) :
    ∀ t,
      S.suboptimality (t + 1) ≤
        (1 - S.muFW * S.lambda * S.eta) * S.suboptimality t
          + 2 * S.eta * err t
          + 2 * S.L * S.eta ^ 2 := by
  intro t
  have hErrParent :
      ∀ n, S.toStochasticFrankWolfeGeometryContext.nesterovErrorNorm n ≤ err n := by
    intro n
    simpa using hErr n
  have hStepBase := S.toStochasticFrankWolfeGeometryContext.one_step_descent_fwGap t
  have hScaledErr :
      2 * S.eta * S.toStochasticFrankWolfeGeometryContext.nesterovErrorNorm t ≤
        2 * S.eta * err t := by
    exact mul_le_mul_of_nonneg_left (hErrParent t) (by nlinarith [S.eta_pos])
  have hStep :
      S.f (S.W (t + 1)) ≤
        S.f (S.W t)
          - S.lambda * S.eta * S.frankWolfeGap t
          + 2 * S.eta * err t
          + 2 * S.L * S.eta ^ 2 := by
    linarith [hStepBase, hScaledErr]
  have hGap := S.frankWolfeGap_ge_muFW_mul_suboptimality t
  have hGapMul :
      (S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar)) ≤
        (S.lambda * S.eta) * S.frankWolfeGap t := by
    exact mul_le_mul_of_nonneg_left hGap S.lambda_eta_nonneg
  have hGapScaled :
      -S.lambda * S.eta * S.frankWolfeGap t ≤
        -(S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar)) := by
    have hNeg := neg_le_neg hGapMul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hNeg
  have hStepSub :
      S.f (S.W (t + 1)) - S.f S.WStar ≤
        S.f (S.W t) - S.f S.WStar
          - S.lambda * S.eta * S.frankWolfeGap t
          + 2 * S.eta * err t
          + 2 * S.L * S.eta ^ 2 := by
    linarith [hStep]
  have hRaw :
      S.f (S.W (t + 1)) - S.f S.WStar ≤
        (S.f (S.W t) - S.f S.WStar)
          - (S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar))
          + 2 * S.eta * err t
          + 2 * S.L * S.eta ^ 2 := by
    linarith [hStepSub, hGapScaled]
  have hFactor :
      (S.f (S.W t) - S.f S.WStar)
        - (S.lambda * S.eta) * (S.muFW * (S.f (S.W t) - S.f S.WStar)) =
      (1 - S.muFW * S.lambda * S.eta) * (S.f (S.W t) - S.f S.WStar) := by
    ring
  dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
  rw [hFactor] at hRaw
  simpa using hRaw

/-- The pointwise FW-KL suboptimality recurrence with the actual Nesterov residual. -/
theorem frankWolfeSuboptimality_recurrence_step
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ t,
      S.suboptimality (t + 1) ≤
        (1 - S.muFW * S.lambda * S.eta) * S.suboptimality t
          + 2 * S.eta * S.nesterovErrorNorm t
          + 2 * S.L * S.eta ^ 2 := by
  exact frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound S
    (err := fun t => S.nesterovErrorNorm t) (fun t => le_rfl)

/-- Loose Theorem-14-style Frank-Wolfe expected-suboptimality bound. -/
theorem frankWolfeExpectedSuboptimality_bound
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.muFW * S.lambda * S.eta) ^ T * S.frankWolfeExpectedSuboptimalityInitialGap
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
  exact frankWolfeExpectedSuboptimality_bound_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound
      S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext)

/-- Existential-constants form of the loose FW-KL expected-suboptimality bound. -/
theorem frankWolfeExpectedSuboptimality_existsConstants
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∃ X Y Z : ℝ,
      X = S.frankWolfeExpectedSuboptimalityInitialGap ∧
      Y = S.frankWolfeExpectedSuboptimalityMinibatchCoefficient ∧
      Z = S.frankWolfeExpectedSuboptimalityResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤
          (1 - S.muFW * S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  exact frankWolfeExpectedSuboptimality_existsConstants_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound
      S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext)

end PublicTheorems

end StochasticFrankWolfeKLGeometryContext

end

end SteepestDescentOptimizationBounds
