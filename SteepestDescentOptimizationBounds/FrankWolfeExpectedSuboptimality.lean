import Mathlib
import SteepestDescentOptimizationBounds.FrankWolfe

open scoped BigOperators
open MeasureTheory

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Frank-Wolfe expected-suboptimality layer under the FW-KL assumption.

Upstream dependencies:

- `FrankWolfe.lean` supplies the pathwise Frank-Wolfe gap and one-step descent
  layers.
- `NesterovMomentumBounds.lean`, imported transitively, supplies the expected
  Nesterov-residual bound.

Downstream use:

- the Frank-Wolfe scaling-law family reuses the deterministic coefficient
  definitions from this file.
-/

namespace StochasticFrankWolfeKLGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The batch-size-dependent `1 / sqrt(b)` coefficient in the loose FW-KL bound. -/
def frankWolfeExpectedSuboptimalityMinibatchCoefficient
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  (2 / (S.muFW * S.lambda)) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma

/-- The drift floor in the loose FW-KL expected-suboptimality bound. -/
def frankWolfeExpectedSuboptimalityDriftFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  2 * S.L * S.eta ^ 2 * (1 + 2 * S.beta ^ 2 / (1 - S.beta))

/-- The minibatch-noise floor in the loose FW-KL expected-suboptimality bound. -/
def frankWolfeExpectedSuboptimalityNoiseFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ

/-- The residual floor in the loose FW-KL expected-suboptimality bound. -/
def frankWolfeExpectedSuboptimalityResidualFloor
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  ((2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError
    + (2 * S.L / (S.muFW * S.lambda)) * (1 + 2 * S.beta ^ 2 / (1 - S.beta))) * S.eta

section PrivateTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem suboptimality_aestronglyMeasurable
    (S : StochasticFrankWolfeKLGeometryContext Ω V) (t : ℕ) :
    AEStronglyMeasurable (fun ω => S.suboptimality t ω) S.μ := by
  have hFCont : Continuous S.f := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (S.fderiv_eq x).continuousAt
  exact
    (((hFCont.measurable.comp (S.W_measurable t)).stronglyMeasurable).sub
      stronglyMeasurable_const).aestronglyMeasurable

private theorem suboptimality_integrable
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ t, Integrable (fun ω => S.suboptimality t ω) S.μ
  | 0 => by
      letI := S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.prob
      refine (integrable_const S.initialSuboptimality).congr ?_
      filter_upwards with ω
      simp [StochasticSteepestDescentGeometryContext.suboptimality,
        StochasticSteepestDescentGeometryContext.initialSuboptimality, S.W_zero]
  | t + 1 => by
      have hPrev : Integrable (fun ω => S.suboptimality t ω) S.μ :=
        suboptimality_integrable S t
      letI := S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.prob
      have hConst : Integrable (fun _ : Ω => 2 * S.L * S.eta ^ 2) S.μ :=
        integrable_const _
      have hNesterov :
          Integrable (fun ω => 2 * S.eta * S.nesterovErrorNorm t ω) S.μ :=
        ((S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t)).const_mul
          (2 * S.eta)
      have hUpper :
          Integrable
            (fun ω => S.suboptimality t ω + 2 * S.eta * S.nesterovErrorNorm t ω + 2 * S.L * S.eta ^ 2) S.μ :=
        (hPrev.add hNesterov).add hConst
      refine Integrable.mono' hUpper (suboptimality_aestronglyMeasurable S (t + 1)) ?_
      filter_upwards with ω
      have hNonneg : 0 ≤ S.suboptimality (t + 1) ω := by
        dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
        linarith [S.WStar_optimality (S.W (t + 1) ω)]
      have hOne :=
        S.toStochasticFrankWolfeGeometryContext.one_step_descent_fwGap t ω
      have hSuboptNonneg : 0 ≤ S.suboptimality t ω := by
        dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
        linarith [S.WStar_optimality (S.W t ω)]
      have hGapLower :
          S.muFW * S.suboptimality t ω ≤ S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω := by
        simpa [StochasticSteepestDescentGeometryContext.suboptimality,
          StochasticFrankWolfeGeometryContext.frankWolfeGap,
          StochasticSteepestDescentGeometryContext.grad,
          StochasticFrankWolfeGeometryContext.constraintBall] using
          S.assumptionFrankWolfeKL t ω
      have hGapNonneg : 0 ≤ S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω := by
        have hMuSubNonneg : 0 ≤ S.muFW * S.suboptimality t ω :=
          mul_nonneg S.muFW_pos.le hSuboptNonneg
        linarith
      have hRec :
          S.suboptimality (t + 1) ω
            ≤ S.suboptimality t ω + 2 * S.eta * S.nesterovErrorNorm t ω + 2 * S.L * S.eta ^ 2 := by
        calc
          S.suboptimality (t + 1) ω
            = S.f (S.W (t + 1) ω) - S.f S.WStar := rfl
          _ ≤ S.f (S.W t ω) - S.f S.WStar
                - S.lambda * S.eta * S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω
                + 2 * S.eta * S.nesterovErrorNorm t ω
                + 2 * S.L * S.eta ^ 2 := by
                  linarith [sub_le_sub_right hOne (S.f S.WStar)]
          _ ≤ S.f (S.W t ω) - S.f S.WStar
                + 2 * S.eta * S.nesterovErrorNorm t ω
                + 2 * S.L * S.eta ^ 2 := by
                  have hNegGap :
                      -(S.lambda * S.eta * S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω) ≤ 0 := by
                    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg S.lambda_pos.le S.eta_pos.le) hGapNonneg)
                  have hDrop :=
                    add_le_add_left
                      (add_le_add_right hNegGap
                        (2 * S.eta * S.nesterovErrorNorm t ω + 2 * S.L * S.eta ^ 2))
                      (S.f (S.W t ω) - S.f S.WStar)
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hDrop
          _ = S.suboptimality t ω + 2 * S.eta * S.nesterovErrorNorm t ω + 2 * S.L * S.eta ^ 2 := by
                rfl
      calc
        ‖S.suboptimality (t + 1) ω‖ = S.suboptimality (t + 1) ω := by
          exact Real.norm_of_nonneg hNonneg
        _ ≤ S.suboptimality t ω + 2 * S.eta * S.nesterovErrorNorm t ω + 2 * S.L * S.eta ^ 2 := hRec

private theorem frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound_base
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (err : ℕ → Ω → ℝ)
    (hErr : ∀ t ω, S.nesterovErrorNorm t ω ≤ err t ω)
    (hErrInt : ∀ t, MeasureTheory.Integrable (fun ω => err t ω) S.μ) :
    ∀ t,
      S.expectedSuboptimality (t + 1) ≤
        (1 - S.muFW * S.lambda * S.eta) * S.expectedSuboptimality t
          + 2 * S.eta * (∫ ω, err t ω ∂S.μ)
          + 2 * S.L * S.eta ^ 2 := by
  intro t
  let a : ℝ := 1 - S.muFW * S.lambda * S.eta
  have hPointwise :
      ∀ ω,
        S.suboptimality (t + 1) ω ≤
          a * S.suboptimality t ω + 2 * S.eta * err t ω + 2 * S.L * S.eta ^ 2 := by
    intro ω
    have hOne :=
      S.toStochasticFrankWolfeGeometryContext.one_step_descent_fwGap t ω
    have hGap : S.muFW * S.suboptimality t ω ≤ S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω := by
      simpa [StochasticSteepestDescentGeometryContext.suboptimality,
        StochasticFrankWolfeGeometryContext.frankWolfeGap,
        StochasticSteepestDescentGeometryContext.grad,
        StochasticFrankWolfeGeometryContext.constraintBall] using
        S.assumptionFrankWolfeKL t ω
    have hScaledErr :
        2 * S.eta * S.nesterovErrorNorm t ω ≤ 2 * S.eta * err t ω := by
      exact mul_le_mul_of_nonneg_left (hErr t ω) (by nlinarith [S.eta_pos])
    have hScaledGap :
        -(S.lambda * S.eta) * S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω ≤
          -(S.lambda * S.eta) * (S.muFW * S.suboptimality t ω) := by
      exact mul_le_mul_of_nonpos_left hGap (by nlinarith [S.lambda_pos, S.eta_pos])
    calc
      S.suboptimality (t + 1) ω
        = S.f (S.W (t + 1) ω) - S.f S.WStar := rfl
      _ ≤ S.f (S.W t ω) - S.f S.WStar
            - (S.lambda * S.eta) * S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω
            + 2 * S.eta * S.nesterovErrorNorm t ω
            + 2 * S.L * S.eta ^ 2 := by
              linarith [sub_le_sub_right hOne (S.f S.WStar)]
      _ ≤ S.f (S.W t ω) - S.f S.WStar
            - (S.lambda * S.eta) * (S.muFW * S.suboptimality t ω)
            + 2 * S.eta * err t ω
            + 2 * S.L * S.eta ^ 2 := by
              have hCore :
                  -(S.lambda * S.eta) * S.toStochasticFrankWolfeGeometryContext.frankWolfeGap t ω
                    + 2 * S.eta * S.nesterovErrorNorm t ω
                    ≤
                  -(S.lambda * S.eta) * (S.muFW * S.suboptimality t ω)
                    + 2 * S.eta * err t ω := by
                exact add_le_add hScaledGap hScaledErr
              have hAdd :=
                add_le_add_left
                  (add_le_add_right hCore (2 * S.L * S.eta ^ 2))
                  (S.f (S.W t ω) - S.f S.WStar)
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hAdd
      _ = a * S.suboptimality t ω + 2 * S.eta * err t ω + 2 * S.L * S.eta ^ 2 := by
            dsimp [a, StochasticSteepestDescentGeometryContext.suboptimality]
            ring
  have hLower :
      MeasureTheory.Integrable (fun ω => S.suboptimality (t + 1) ω) S.μ :=
    suboptimality_integrable S (t + 1)
  have hScaledSubopt :
      MeasureTheory.Integrable (fun ω => a * S.suboptimality t ω) S.μ :=
    (suboptimality_integrable S t).const_mul a
  have hErrScaled :
      MeasureTheory.Integrable (fun ω => 2 * S.eta * err t ω) S.μ :=
    (hErrInt t).const_mul (2 * S.eta)
  have hConst : MeasureTheory.Integrable (fun _ : Ω => 2 * S.L * S.eta ^ 2) S.μ := by
    letI := S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.prob
    exact MeasureTheory.integrable_const _
  have hUpper :
      MeasureTheory.Integrable
        (fun ω => a * S.suboptimality t ω + 2 * S.eta * err t ω + 2 * S.L * S.eta ^ 2)
        S.μ :=
    (hScaledSubopt.add hErrScaled).add hConst
  have hIntegralSum :
      ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω + 2 * S.L * S.eta ^ 2) ∂S.μ
        =
        ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω) ∂S.μ
          + ∫ ω, 2 * S.L * S.eta ^ 2 ∂S.μ := by
    simpa [add_assoc] using
      (MeasureTheory.integral_add (hScaledSubopt.add hErrScaled) hConst :
        ∫ ω, ((a * S.suboptimality t ω + 2 * S.eta * err t ω) + 2 * S.L * S.eta ^ 2) ∂S.μ
          =
          ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω) ∂S.μ
            + ∫ ω, 2 * S.L * S.eta ^ 2 ∂S.μ)
  have hIntegralClosed :
      ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω) ∂S.μ
        + ∫ ω, 2 * S.L * S.eta ^ 2 ∂S.μ
        =
        a * S.expectedSuboptimality t + 2 * S.eta * (∫ ω, err t ω ∂S.μ) + 2 * S.L * S.eta ^ 2 := by
    rw [MeasureTheory.integral_add hScaledSubopt hErrScaled]
    have hSuboptInt :
        ∫ ω, a * S.suboptimality t ω ∂S.μ = a * S.expectedSuboptimality t := by
      simpa [expectedSuboptimality, mul_assoc, mul_left_comm, mul_comm] using
        (MeasureTheory.integral_const_mul a (fun ω => S.suboptimality t ω))
    have hErrInt' :
        ∫ ω, 2 * S.eta * err t ω ∂S.μ = (2 * S.eta) * (∫ ω, err t ω ∂S.μ) := by
      calc
        ∫ ω, 2 * S.eta * err t ω ∂S.μ
          = (2 * S.eta) * (∫ ω, err t ω ∂S.μ) := by
              rw [MeasureTheory.integral_const_mul]
        _ = 2 * S.eta * (∫ ω, err t ω ∂S.μ) := by ring
    rw [hSuboptInt, hErrInt']
    letI := S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.prob
    simp
  calc
    S.expectedSuboptimality (t + 1)
        = ∫ ω, S.suboptimality (t + 1) ω ∂S.μ := rfl
    _ ≤ ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω + 2 * S.L * S.eta ^ 2) ∂S.μ := by
          exact MeasureTheory.integral_mono_ae hLower hUpper (Filter.Eventually.of_forall hPointwise)
    _ = ∫ ω, (a * S.suboptimality t ω + 2 * S.eta * err t ω) ∂S.μ
          + ∫ ω, 2 * S.L * S.eta ^ 2 ∂S.μ := hIntegralSum
    _ = a * S.expectedSuboptimality t + 2 * S.eta * (∫ ω, err t ω ∂S.μ) + 2 * S.L * S.eta ^ 2 := hIntegralClosed

private theorem frankWolfeExpectedSuboptimality_bound_base
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (hContraction : S.muFW * S.lambda * S.eta ≤ 1) :
    ∀ T,
      S.expectedSuboptimality T ≤
        (1 - S.muFW * S.lambda * S.eta) ^ T * S.initialSuboptimality
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
  intro T
  let a : ℝ := 1 - S.muFW * S.lambda * S.eta
  let k : ℝ :=
    2 * S.eta
      * ((2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
      + 2 * S.L * S.eta ^ 2
  let d : ℝ := 2 * S.eta * S.initialExpectedMomentumError
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    exact one_sub_muFW_lambda_eta_nonneg (S := S) hContraction
  have haLeOne : a ≤ 1 := by
    dsimp [a]
    exact S.one_sub_muFW_lambda_eta_le_one
  have haLtOne : a < 1 := by
    dsimp [a]
    exact S.one_sub_muFW_lambda_eta_lt_one
  have hkNonneg : 0 ≤ k := by
    dsimp [k]
    have hNoiseNonneg :
        0 ≤
          (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg S.momentumNoisePrefactor_nonneg (Real.sqrt_nonneg _)) S.sigma_nonneg)
        (Real.sqrt_nonneg _)
    have hDriftNonneg : 0 ≤ (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta := by
      have hCoeffNonneg : 0 ≤ 2 * S.beta ^ 2 / (1 - S.beta) := by
        exact div_nonneg (by positivity) S.one_sub_beta_pos.le
      exact mul_nonneg (mul_nonneg hCoeffNonneg S.assumption3_fLocalSmoothness.nonneg) S.eta_pos.le
    have hLeadingNonneg :
        0 ≤ 2 * S.eta
            * ((2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
      exact mul_nonneg (by nlinarith [S.eta_pos]) (add_nonneg hDriftNonneg hNoiseNonneg)
    have hTailNonneg : 0 ≤ 2 * S.L * S.eta ^ 2 := by
      exact mul_nonneg (mul_nonneg (by norm_num) S.assumption3_fLocalSmoothness.nonneg) (sq_nonneg _)
    exact add_nonneg hLeadingNonneg hTailNonneg
  have hdNonneg : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg (by nlinarith [S.eta_pos]) S.initialExpectedMomentumError_nonneg
  have hCor11 :
      ∀ t,
        S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.expectedNesterovError t ≤
          S.beta ^ (t + 1) * S.initialExpectedMomentumError
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
    intro t
    simpa [StochasticSteepestDescentGeometryContext.initialExpectedMomentumError] using
      (StochasticSteepestDescentGeometryContext.Corollary11PointwiseNesterovErrorBound
        S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext t)
  have hRec :
      ∀ t,
        S.expectedSuboptimality (t + 1) ≤
          a * S.expectedSuboptimality t + k + d * S.beta ^ (t + 1) := by
    intro t
    have hStep :=
      frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound_base
        S
        (fun n ω => S.nesterovErrorNorm n ω)
        (fun _ _ => le_rfl)
        (S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable)
        t
    have hScaledErr :
        2 * S.eta
            * S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.expectedNesterovError t
          ≤
          2 * S.eta
            * (S.beta ^ (t + 1) * S.initialExpectedMomentumError
                + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
      exact mul_le_mul_of_nonneg_left (hCor11 t) (by nlinarith [S.eta_pos])
    have hAux :
        2 * S.eta
            * S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.expectedNesterovError t
          + 2 * S.L * S.eta ^ 2 ≤
          k + d * S.beta ^ (t + 1) := by
      dsimp [k, d]
      ring_nf at hScaledErr ⊢
      nlinarith [hScaledErr]
    calc
      S.expectedSuboptimality (t + 1)
        ≤ a * S.expectedSuboptimality t
            + 2 * S.eta
                * S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.expectedNesterovError t
            + 2 * S.L * S.eta ^ 2 := hStep
      _ ≤ a * S.expectedSuboptimality t + k + d * S.beta ^ (t + 1) := by
            linarith [hAux]
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
      S.expectedSuboptimality T ≤
        a ^ T * S.expectedSuboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
    nlinarith [hUnrolled, hkMul, hdMul]
  have hOneMinusA : 1 - a = S.muFW * S.lambda * S.eta := by
    dsimp [a]
    ring
  calc
    S.expectedSuboptimality T
      ≤ a ^ T * S.expectedSuboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := hMain
    _ = a ^ T * S.initialSuboptimality + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
          have hInit :
              S.expectedSuboptimality 0 = S.initialSuboptimality := by
            simpa [expectedSuboptimality,
              StochasticSteepestDescentGeometryContext.initialExpectedSuboptimality] using
              (StochasticSteepestDescentGeometryContext.initialExpectedSuboptimality_eq_initialSuboptimality
                S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext)
          rw [hInit]
    _ = (1 - S.muFW * S.lambda * S.eta) ^ T * S.initialSuboptimality
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
            dsimp [a, k, d, frankWolfeExpectedSuboptimalityMinibatchCoefficient,
              frankWolfeExpectedSuboptimalityResidualFloor]
            rw [hOneMinusA]
            field_simp [S.muFW_lambda_eta_ne_zero, S.muFW_pos.ne', S.lambda_pos.ne', S.eta_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

end PrivateTheorems

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Pathwise FW-KL lower bound of the Frank-Wolfe gap by the suboptimality gap. -/
theorem frankWolfeGap_ge_muFW_mul_suboptimality
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ t ω,
      S.muFW * S.suboptimality t ω ≤
        sSup ((fun V => (S.fGrad (S.W t ω)) (S.W t ω - V)) '' Metric.closedBall (0 : V) (1 / S.lambda)) := by
  intro t ω
  change S.muFW * (S.f (S.W t ω) - S.f S.WStar) ≤
    sSup ((fun V => (S.fGrad (S.W t ω)) (S.W t ω - V)) '' Metric.closedBall (0 : V) (1 / S.lambda))
  exact S.assumptionFrankWolfeKL t ω

/-- Expected FW-KL recurrence under a pathwise tracking envelope. -/
theorem frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (err : ℕ → Ω → ℝ)
    (hErr : ∀ t ω, S.nesterovErrorNorm t ω ≤ err t ω)
    (hErrInt : ∀ t, MeasureTheory.Integrable (fun ω => err t ω) S.μ) :
    ∀ t,
      S.expectedSuboptimality (t + 1) ≤
        (1 - S.muFW * S.lambda * S.eta) * S.expectedSuboptimality t
          + 2 * S.eta * (∫ ω, err t ω ∂S.μ)
          + 2 * S.L * S.eta ^ 2 := by
  exact frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound_base S err hErr hErrInt

/-- Expected FW-KL recurrence specialized to the actual expected Nesterov residual. -/
theorem frankWolfeSuboptimality_recurrence_step
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    ∀ t,
      S.expectedSuboptimality (t + 1) ≤
        (1 - S.muFW * S.lambda * S.eta) * S.expectedSuboptimality t
          + 2 * S.eta * S.expectedNesterovError t
          + 2 * S.L * S.eta ^ 2 := by
  intro t
  simpa [StochasticSteepestDescentGeometryContext.expectedNesterovError] using
    frankWolfeExpectedSuboptimality_recurrence_of_tracking_bound_base
      S
      (err := fun n ω => S.nesterovErrorNorm n ω)
      (hErr := fun _ _ => le_rfl)
      (hErrInt := S.toStochasticFrankWolfeGeometryContext.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable) t

/-- Loose FW-KL expected-suboptimality bound with explicit coefficient floors. -/
theorem frankWolfeExpectedSuboptimality_bound
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (hContraction : S.muFW * S.lambda * S.eta ≤ 1) :
    ∀ T,
      S.expectedSuboptimality T ≤
        (1 - S.muFW * S.lambda * S.eta) ^ T * S.initialSuboptimality
          + S.frankWolfeExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.frankWolfeExpectedSuboptimalityResidualFloor := by
  exact frankWolfeExpectedSuboptimality_bound_base S hContraction

/-- Existential-constants form of the loose FW-KL expected-suboptimality bound. -/
theorem frankWolfeExpectedSuboptimality_existsConstants
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (hContraction : S.muFW * S.lambda * S.eta ≤ 1) :
    ∃ X Y Z : ℝ,
      X = S.initialSuboptimality ∧
      Y = S.frankWolfeExpectedSuboptimalityMinibatchCoefficient ∧
      Z = S.frankWolfeExpectedSuboptimalityResidualFloor ∧
      ∀ T,
        S.expectedSuboptimality T ≤
          (1 - S.muFW * S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  refine ⟨S.initialSuboptimality, S.frankWolfeExpectedSuboptimalityMinibatchCoefficient,
    S.frankWolfeExpectedSuboptimalityResidualFloor, rfl, rfl, rfl, ?_⟩
  intro T
  simpa using S.frankWolfeExpectedSuboptimality_bound hContraction T

end PublicTheorems

end StochasticFrankWolfeKLGeometryContext

end

end SteepestDescentOptimizationBounds
