import Mathlib
import SteepestDescentOptimizationBounds.StarConvex

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file packages the Corollary-11-driven expected-suboptimality assembly for
the star-convex layer.

Upstream dependencies:

- `StarConvex.lean` provides the deterministic one-step descent theorem, the
  pointwise star-convex recurrence, and the public coefficient definitions.
- `NesterovMomentumBounds.lean`, imported transitively, provides the
  Corollary-11 pointwise tracking bound.

Downstream use:

- `StarConvexExpectedSuboptimalityConvergence.lean` rewrites the resulting
  bound into the schedule form used by the project.
-/

section Theorem14Assembly

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

/--
Theorem 14 in explicit-constants form, assuming the pointwise Corollary-11
bound.
-/
private theorem starConvexExpectedSuboptimality_bound_of_corollary11
    (S : StochasticStarConvexGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap
          + S.starConvexExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.starConvexExpectedSuboptimalityResidualFloor := by
  intro T
  let a : ℝ := 1 - S.lambda * S.eta
  let k : ℝ := S.starConvexExpectedSuboptimalityDriftFloor + S.starConvexExpectedSuboptimalityNoiseFloor
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
    dsimp [k, StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor,
      StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityNoiseFloor]
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
    have hStepRec := S.suboptimality_recurrence_step t
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
      dsimp [k, d, StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor,
        StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityNoiseFloor]
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
        a ^ T * S.starConvexExpectedSuboptimalityInitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
    have : S.suboptimality T ≤
        a ^ T * S.suboptimality 0 + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := by
      nlinarith [hUnrolled, hkMul, hdMul]
    simpa [StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityInitialGap,
      StochasticSteepestDescentGeometryContext.suboptimality] using this
  have hOneMinusA : 1 - a = S.lambda * S.eta := by
    dsimp [a]
    ring
  calc
    S.suboptimality T
      ≤ a ^ T * S.starConvexExpectedSuboptimalityInitialGap + k * (1 / (1 - a)) + d * (S.beta / (1 - S.beta)) := hMain
    _ = (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap
          + S.starConvexExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.starConvexExpectedSuboptimalityResidualFloor := by
            dsimp [a, k, d, StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityMinibatchCoefficient,
              StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityResidualFloor,
              StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityDriftFloor,
              StochasticStarConvexGeometryContext.starConvexExpectedSuboptimalityNoiseFloor,
              StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            rw [hOneMinusA]
            field_simp [S.lambda_eta_ne_zero, S.lambda_pos.ne', S.eta_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

/-- Existential-constants form of Theorem 14, assuming Corollary 11. -/
private theorem starConvexExpectedSuboptimality_existsConstants_of_corollary11
    (S : StochasticStarConvexGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∃ X Y Z : ℝ,
      X = S.starConvexExpectedSuboptimalityInitialGap ∧
      Y = S.starConvexExpectedSuboptimalityMinibatchCoefficient ∧
      Z = S.starConvexExpectedSuboptimalityResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  refine ⟨S.starConvexExpectedSuboptimalityInitialGap, S.starConvexExpectedSuboptimalityMinibatchCoefficient, S.starConvexExpectedSuboptimalityResidualFloor,
    rfl, rfl, rfl, ?_⟩
  intro T
  simpa using starConvexExpectedSuboptimality_bound_of_corollary11 S hCor11 T

end Theorem14Assembly

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

-- No new public definitions are introduced in this file.

end PublicDefinitions

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

/-- The direct Theorem-14 path from the concrete minibatch and Proposition-6 processes. -/
theorem starConvexExpectedSuboptimality_bound
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ T,
      S.suboptimality T ≤
        (1 - S.lambda * S.eta) ^ T * S.starConvexExpectedSuboptimalityInitialGap
          + S.starConvexExpectedSuboptimalityMinibatchCoefficient / Real.sqrt S.batchSizeℝ
          + S.starConvexExpectedSuboptimalityResidualFloor := by
  exact starConvexExpectedSuboptimality_bound_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound S.toStochasticSteepestDescentGeometryContext)

/-- Existential-constants form of the direct Theorem-14 bound. -/
theorem starConvexExpectedSuboptimality_existsConstants
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∃ X Y Z : ℝ,
      X = S.starConvexExpectedSuboptimalityInitialGap ∧
      Y = S.starConvexExpectedSuboptimalityMinibatchCoefficient ∧
      Z = S.starConvexExpectedSuboptimalityResidualFloor ∧
      ∀ T,
        S.suboptimality T ≤ (1 - S.lambda * S.eta) ^ T * X + Y / Real.sqrt S.batchSizeℝ + Z := by
  exact starConvexExpectedSuboptimality_existsConstants_of_corollary11
    S
    (Corollary11PointwiseNesterovErrorBound S.toStochasticSteepestDescentGeometryContext)

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
