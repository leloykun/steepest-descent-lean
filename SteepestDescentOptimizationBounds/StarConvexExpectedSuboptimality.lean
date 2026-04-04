import Mathlib
import SteepestDescentOptimizationBounds.StarConvex

open scoped BigOperators
open MeasureTheory

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Expected star-convex suboptimality layer.

Upstream dependencies:

- `StarConvex.lean` provides the pathwise one-step recurrence and the
  deterministic coefficient definitions.
- `NesterovMomentumBounds.lean`, imported transitively, provides the expected
  Nesterov-residual bound.

Downstream use:

- `StarConvexExpectedSuboptimalityConvergence.lean` rewrites the bound into the
  schedule form used by the convergence statements.
-/

namespace StochasticStarConvexGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

section PrivateTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem suboptimality_aestronglyMeasurable
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    AEStronglyMeasurable (fun ω => S.suboptimality t ω) S.μ := by
  have hFCont : Continuous S.f := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (S.fderiv_eq x).continuousAt
  exact
    (((hFCont.measurable.comp (S.W_measurable t)).stronglyMeasurable).sub
      stronglyMeasurable_const).aestronglyMeasurable

private theorem suboptimality_integrable
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ t, Integrable (fun ω => S.suboptimality t ω) S.μ
  | 0 => by
      letI := S.prob
      refine (integrable_const S.initialSuboptimality).congr ?_
      filter_upwards with ω
      simp [StochasticSteepestDescentGeometryContext.suboptimality,
        StochasticSteepestDescentGeometryContext.initialSuboptimality, S.W_zero]
  | t + 1 => by
      let a : ℝ := 1 - S.lambda * S.eta
      have hPrev : Integrable (fun ω => S.suboptimality t ω) S.μ :=
        suboptimality_integrable S t
      have hScaled : Integrable (fun ω => a * S.suboptimality t ω) S.μ :=
        hPrev.const_mul a
      letI := S.prob
      have hConst : Integrable (fun _ : Ω => 4 * S.L * S.eta ^ 2) S.μ :=
        integrable_const _
      have hNesterov :
          Integrable (fun ω => 2 * S.eta * S.nesterovErrorNorm t ω) S.μ :=
        (S.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t).const_mul
          (2 * S.eta)
      have hUpper :
          Integrable
            (fun ω => a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω)
            S.μ :=
        (hScaled.add hConst).add hNesterov
      refine Integrable.mono' hUpper (suboptimality_aestronglyMeasurable S (t + 1)) ?_
      filter_upwards with ω
      have hNonneg : 0 ≤ S.suboptimality (t + 1) ω := by
        dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
        linarith [S.WStar_optimality (S.W (t + 1) ω)]
      have hRec :
          S.suboptimality (t + 1) ω ≤
            a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω := by
        simpa [a] using S.suboptimality_recurrence_step t ω
      calc
        ‖S.suboptimality (t + 1) ω‖ = S.suboptimality (t + 1) ω := by
          exact Real.norm_of_nonneg hNonneg
        _ ≤ a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω :=
          hRec

/-- Expected suboptimality is nonnegative because `W_*` is globally optimal. -/
private theorem expectedSuboptimality_nonneg
    (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) :
    0 ≤ S.expectedSuboptimality t := by
  exact MeasureTheory.integral_nonneg fun ω => by
    dsimp [StochasticSteepestDescentGeometryContext.suboptimality]
    linarith [S.WStar_optimality (S.W t ω)]

/-- Expected star-convex suboptimality bound under the derived residual estimate. -/
private theorem starConvexExpectedSuboptimality_bound_of_corollary11
    (S : StochasticStarConvexGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.expectedNesterovError t ≤
          S.beta ^ (t + 1) * S.initialExpectedMomentumError
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T,
      S.expectedSuboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ
          + (((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
                + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta) := by
  intro T
  let a : ℝ := 1 - S.lambda * S.eta
  let k : ℝ :=
    (4 * (1 + S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta ^ 2)
      + ((2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
  let d : ℝ := 2 * S.eta * S.initialExpectedMomentumError
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
    dsimp [k, StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor,
      StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityNoiseFloor]
    have hNoiseNonneg :
        0 ≤ (2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
      have hNumNonneg :
          0 ≤ 2 * S.eta * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma := by
        have hEtaNonneg : 0 ≤ 2 * S.eta := by nlinarith [S.eta_pos]
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
    dsimp [d, StochasticSteepestDescentGeometryContext.initialExpectedMomentumError]
    exact mul_nonneg (by nlinarith [S.eta_pos]) S.initialExpectedMomentumError_nonneg
  have hRec :
      ∀ t,
        S.expectedSuboptimality (t + 1) ≤
          a * S.expectedSuboptimality t + k + d * S.beta ^ (t + 1) := by
    intro t
    letI := S.prob
    have hPointwise :
        ∀ ω,
          S.suboptimality (t + 1) ω ≤
            a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω := by
      simpa [a] using S.suboptimality_recurrence_step t
    have hLower :
        MeasureTheory.Integrable (fun ω => S.suboptimality (t + 1) ω) S.μ :=
      suboptimality_integrable S (t + 1)
    have hScaledSubopt : MeasureTheory.Integrable (fun ω => a * S.suboptimality t ω) S.μ :=
      (suboptimality_integrable S t).const_mul a
    have hConst : MeasureTheory.Integrable (fun _ : Ω => 4 * S.L * S.eta ^ 2) S.μ :=
      MeasureTheory.integrable_const (4 * S.L * S.eta ^ 2)
    have hNesterov : MeasureTheory.Integrable (fun ω => 2 * S.eta * S.nesterovErrorNorm t ω) S.μ :=
      (S.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t).const_mul
        (2 * S.eta)
    have hUpper :
        MeasureTheory.Integrable
          (fun ω => a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω) S.μ :=
      (hScaledSubopt.add hConst).add hNesterov
    have hIntegralSum :
        ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω) ∂S.μ
          = ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2) ∂S.μ
              + ∫ ω, 2 * S.eta * S.nesterovErrorNorm t ω ∂S.μ := by
      simpa [add_assoc] using
        (MeasureTheory.integral_add (hScaledSubopt.add hConst) hNesterov :
          ∫ ω, ((a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2) + 2 * S.eta * S.nesterovErrorNorm t ω) ∂S.μ
            = ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2) ∂S.μ
                + ∫ ω, 2 * S.eta * S.nesterovErrorNorm t ω ∂S.μ)
    have hIntegralClosed :
        ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2) ∂S.μ
          + ∫ ω, 2 * S.eta * S.nesterovErrorNorm t ω ∂S.μ
          = a * S.expectedSuboptimality t + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.expectedNesterovError t := by
      rw [MeasureTheory.integral_add hScaledSubopt hConst]
      have hSuboptInt :
          ∫ ω, a * S.suboptimality t ω ∂S.μ = a * S.expectedSuboptimality t := by
        simpa [expectedSuboptimality, mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_const_mul a (fun ω => S.suboptimality t ω))
      have hNesterovInt :
          ∫ ω, 2 * S.eta * S.nesterovErrorNorm t ω ∂S.μ =
            (2 * S.eta) * S.expectedNesterovError t := by
        simpa [StochasticSteepestDescentGeometryContext.expectedNesterovError, mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_const_mul (2 * S.eta) (fun ω => S.nesterovErrorNorm t ω))
      rw [hSuboptInt, hNesterovInt]
      letI := S.prob
      simp
    have hExpectedStep :
        S.expectedSuboptimality (t + 1) ≤
          a * S.expectedSuboptimality t + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.expectedNesterovError t := by
      calc
        S.expectedSuboptimality (t + 1)
            = ∫ ω, S.suboptimality (t + 1) ω ∂S.μ := rfl
        _ ≤ ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t ω) ∂S.μ := by
              exact MeasureTheory.integral_mono_ae hLower hUpper (Filter.Eventually.of_forall hPointwise)
        _ = ∫ ω, (a * S.suboptimality t ω + 4 * S.L * S.eta ^ 2) ∂S.μ
              + ∫ ω, 2 * S.eta * S.nesterovErrorNorm t ω ∂S.μ := hIntegralSum
        _ = a * S.expectedSuboptimality t + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.expectedNesterovError t := hIntegralClosed
    have hScaledErr :
        2 * S.eta * S.expectedNesterovError t ≤
          2 * S.eta *
            (S.beta ^ (t + 1) * S.initialExpectedMomentumError
              + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
              + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
      exact mul_le_mul_of_nonneg_left (hCor11 t) (by nlinarith [S.eta_pos])
    have hAux :
        4 * S.L * S.eta ^ 2 + 2 * S.eta * S.expectedNesterovError t ≤ k + d * S.beta ^ (t + 1) := by
      dsimp [k, d, StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor,
        StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityNoiseFloor]
      ring_nf at hScaledErr ⊢
      nlinarith [hScaledErr]
    dsimp [a]
    linarith [hExpectedStep, hAux]
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
  have hOneMinusA : 1 - a = S.lambda * S.eta := by
    dsimp [a]
    ring
  calc
    S.expectedSuboptimality T
      ≤ a ^ T * S.expectedSuboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := hMain
    _ = a ^ T * S.initialSuboptimality
          + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
          rw [show S.expectedSuboptimality 0 = S.initialSuboptimality by
            simpa [expectedSuboptimality,
              StochasticSteepestDescentGeometryContext.initialExpectedSuboptimality] using
              (StochasticSteepestDescentGeometryContext.initialExpectedSuboptimality_eq_initialSuboptimality
                S.toStochasticSteepestDescentGeometryContext)]
    _ = (1 - S.lambda * S.eta) ^ T * S.initialSuboptimality
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ
          + (((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
                + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta) := by
            dsimp [a, k, d,
              StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            rw [hOneMinusA]
            field_simp [S.lambda_eta_ne_zero, S.lambda_pos.ne', S.eta_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

/-- Existential-constants form of the expected star-convex bound. -/
private theorem starConvexExpectedSuboptimality_existsConstants_of_corollary11
    (S : StochasticStarConvexGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.expectedNesterovError t ≤
          S.beta ^ (t + 1) * S.initialExpectedMomentumError
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∃ X Y Z : ℝ,
      X = S.initialSuboptimality ∧
      Y = (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma ∧
      Z = ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
            + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta ∧
      ∀ T,
        S.expectedSuboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  refine ⟨S.initialSuboptimality,
    (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma,
    ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
      + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta, rfl, rfl, rfl, ?_⟩
  intro T
  simpa using starConvexExpectedSuboptimality_bound_of_corollary11 S hCor11 T

end PrivateTheorems

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Direct expected star-convex suboptimality bound with arbitrary initial momentum residual. -/
theorem starConvexExpectedSuboptimality_bound
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ T,
      S.expectedSuboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * (S.toStochasticSteepestDescentGeometryContext.initialSuboptimality)
          + ((2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma)
              / Real.sqrt S.batchSizeℝ
          + (((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
                + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta) := by
  have hCor11 :
      ∀ t,
        S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t ≤
          S.toStochasticSteepestDescentGeometryContext.beta ^ (t + 1)
            * S.toStochasticSteepestDescentGeometryContext.initialExpectedMomentumError
          + (2 * S.toStochasticSteepestDescentGeometryContext.beta ^ 2
              / (1 - S.toStochasticSteepestDescentGeometryContext.beta))
              * S.toStochasticSteepestDescentGeometryContext.L
              * S.toStochasticSteepestDescentGeometryContext.eta
          + (S.toStochasticSteepestDescentGeometryContext.momentumNoisePrefactor
              * Real.sqrt S.toStochasticSteepestDescentGeometryContext.D
              * S.toStochasticSteepestDescentGeometryContext.sigma)
              / Real.sqrt S.toStochasticSteepestDescentGeometryContext.batchSizeℝ := by
    intro t
    simpa [StochasticSteepestDescentGeometryContext.initialExpectedMomentumError] using
      (StochasticSteepestDescentGeometryContext.Corollary11PointwiseNesterovErrorBound
        S.toStochasticSteepestDescentGeometryContext t)
  exact starConvexExpectedSuboptimality_bound_of_corollary11 S hCor11

/-- Existential-constants form of the expected star-convex bound. -/
theorem starConvexExpectedSuboptimality_existsConstants
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∃ X Y Z : ℝ,
      X = S.toStochasticSteepestDescentGeometryContext.initialSuboptimality ∧
      Y = (2 / S.lambda) * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma ∧
      Z = ((4 * S.L / S.lambda) * (1 + S.beta ^ 2 / (1 - S.beta))
            + (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError) * S.eta ∧
      ∀ T,
        S.expectedSuboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  exact starConvexExpectedSuboptimality_existsConstants_of_corollary11
    S
    (by
      intro t
      simpa [StochasticSteepestDescentGeometryContext.initialExpectedMomentumError] using
        (StochasticSteepestDescentGeometryContext.Corollary11PointwiseNesterovErrorBound
          S.toStochasticSteepestDescentGeometryContext t))

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
