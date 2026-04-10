import Mathlib
import SteepestDescentOptimizationBounds.FrankWolfe

open scoped BigOperators
open MeasureTheory

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Frank-Wolfe expected-gap layer.

Upstream dependencies:

- `FrankWolfe.lean` supplies the pathwise Frank-Wolfe gap layer.
- `NesterovMomentumBounds.lean`, imported transitively, supplies the expected
  Nesterov-residual bound.

Downstream use:

- the public summaries use the averaged expected-gap theorem and the
  best-iterate corollary from this file.
-/

namespace StochasticFrankWolfeGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-- The expected Frank-Wolfe gap `E[gap_t]`. -/
def expectedFrankWolfeGap
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, S.frankWolfeGap t ω ∂S.μ

end PublicDefinitions

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-- Averaged Frank-Wolfe expected-gap theorem with arbitrary initial momentum residual. -/
theorem avg_frankWolfeExpectedGap_nesterov_wd
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.expectedFrankWolfeGap t) / (T : ℝ) ≤
        (S.initialExpectedSuboptimality) / (S.lambda * S.eta * T)
          + (2 * S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
          + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
              (S.lambda * Real.sqrt S.batchSizeℝ)
          + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
  intro T hT
  letI := S.toStochasticSteepestDescentGeometryContext.prob
  letI : IsFiniteMeasure S.μ := by infer_instance
  let lhs : Ω → ℝ :=
    fun ω => (Finset.sum (Finset.range T) fun t => S.frankWolfeGap t ω) / (T : ℝ)
  let initialSuboptimalityPath : Ω → ℝ := fun ω => S.suboptimality 0 ω
  let rhs : Ω → ℝ :=
    fun ω =>
      initialSuboptimalityPath ω / (S.lambda * S.eta * T)
        + (2 / (S.lambda * T)) * (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t ω)
        + 2 * S.L * S.eta / S.lambda
  have hPointwise : ∀ ω, lhs ω ≤ rhs ω := by
    intro ω
    have hPath :=
      S.frankWolfeGap_bound_of_tracking_bound
        (err := fun t ω => S.nesterovErrorNorm t ω)
        (hErr := fun _ _ => le_rfl)
        T ω hT
    simpa [lhs, rhs, initialSuboptimalityPath, StochasticFrankWolfeGeometryContext.suboptimality] using hPath
  have hLhsIntegrable : MeasureTheory.Integrable lhs S.μ := by
    have hSum :
        MeasureTheory.Integrable (fun ω => Finset.sum (Finset.range T) fun t => S.frankWolfeGap t ω) S.μ := by
      exact MeasureTheory.integrable_finset_sum (Finset.range T) (fun t _ => S.frankWolfeGap_integrable t)
    simpa [lhs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hSum.const_mul ((T : ℝ)⁻¹)
  have hRhsIntegrable : MeasureTheory.Integrable rhs S.μ := by
    have hSum :
        MeasureTheory.Integrable (fun ω => Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t ω) S.μ := by
      exact
        MeasureTheory.integrable_finset_sum
          (Finset.range T)
          (fun t _ => S.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t)
    have hScaled :
        MeasureTheory.Integrable
          (fun ω => (2 / (S.lambda * T)) * (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t ω))
          S.μ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hSum.const_mul (2 / (S.lambda * T))
    have hConst1 :
        MeasureTheory.Integrable
          (fun ω => initialSuboptimalityPath ω / (S.lambda * S.eta * T))
          S.μ := by
      have hConstWStar :
          Integrable (fun _ : Ω => S.f S.WStar) S.μ := by
        letI := S.toStochasticSteepestDescentGeometryContext.prob
        simpa [StochasticSteepestDescentGeometryContext.μ] using
          (integrable_const (μ := S.toStochasticSteepestDescentGeometryContext.μ) (S.f S.WStar))
      have hInit :
          MeasureTheory.Integrable initialSuboptimalityPath S.μ := by
        simpa [initialSuboptimalityPath, StochasticFrankWolfeGeometryContext.suboptimality] using
          (S.toStochasticSteepestDescentGeometryContext.objective_integrable 0).sub
            hConstWStar
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hInit.const_mul ((S.lambda * S.eta * T)⁻¹)
    have hConst2 :
        MeasureTheory.Integrable (fun _ : Ω => 2 * S.L * S.eta / S.lambda) S.μ :=
      MeasureTheory.integrable_const _
    exact (hConst1.add hScaled).add hConst2
  have hIntegrated :
      ∫ ω, lhs ω ∂S.μ ≤ ∫ ω, rhs ω ∂S.μ := by
    exact MeasureTheory.integral_mono_ae hLhsIntegrable hRhsIntegrable (Filter.Eventually.of_forall hPointwise)
  have hLhsEval :
      ∫ ω, lhs ω ∂S.μ =
        (Finset.sum (Finset.range T) fun t => S.expectedFrankWolfeGap t) / (T : ℝ) := by
    have hSum :
        ∫ ω, Finset.sum (Finset.range T) (fun t => S.frankWolfeGap t ω) ∂S.μ
          =
            Finset.sum (Finset.range T) (fun t => ∫ ω, S.frankWolfeGap t ω ∂S.μ) := by
      exact MeasureTheory.integral_finset_sum (Finset.range T) (fun t _ => S.frankWolfeGap_integrable t)
    calc
      ∫ ω, lhs ω ∂S.μ
        = ∫ ω, ((T : ℝ)⁻¹) * (Finset.sum (Finset.range T) fun t => S.frankWolfeGap t ω) ∂S.μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            simp [lhs, div_eq_mul_inv, mul_comm]
      _ = ((T : ℝ)⁻¹) * ∫ ω, Finset.sum (Finset.range T) (fun t => S.frankWolfeGap t ω) ∂S.μ := by
            rw [MeasureTheory.integral_const_mul]
      _ = ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t => ∫ ω, S.frankWolfeGap t ω ∂S.μ) := by
            rw [hSum]
      _ = (Finset.sum (Finset.range T) fun t => S.expectedFrankWolfeGap t) / (T : ℝ) := by
            have hExp :
                Finset.sum (Finset.range T) (fun t => ∫ ω, S.frankWolfeGap t ω ∂S.μ)
                  = Finset.sum (Finset.range T) (fun t => S.expectedFrankWolfeGap t) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              rfl
            rw [hExp, div_eq_mul_inv]
            ring
  have hRhsEval :
      ∫ ω, rhs ω ∂S.μ =
        S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
          + (2 / (S.lambda * T))
              * (Finset.sum (Finset.range T) fun t =>
                  S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)
          + 2 * S.L * S.eta / S.lambda := by
    let c0 : Ω → ℝ := fun ω => initialSuboptimalityPath ω / (S.lambda * S.eta * T)
    let c2 : ℝ := 2 * S.L * S.eta / S.lambda
    let g : Ω → ℝ := fun ω => (2 / (S.lambda * T)) * (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t ω)
    have hSum :
        ∫ ω, Finset.sum (Finset.range T) (fun t => S.nesterovErrorNorm t ω) ∂S.μ
          =
            Finset.sum (Finset.range T)
              (fun t => ∫ ω, S.nesterovErrorNorm t ω ∂S.μ) := by
      exact
        MeasureTheory.integral_finset_sum
          (Finset.range T)
          (fun t _ => S.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t)
    have hIntG :
        ∫ ω, g ω ∂S.μ
          =
            (2 / (S.lambda * T))
              * (Finset.sum (Finset.range T)
                  (fun t => ∫ ω, S.nesterovErrorNorm t ω ∂S.μ)) := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul, hSum]
    have hConst0 :
        MeasureTheory.Integrable c0 S.μ := by
      have hConstWStar :
          Integrable (fun _ : Ω => S.f S.WStar) S.μ := by
        letI := S.toStochasticSteepestDescentGeometryContext.prob
        simpa [StochasticSteepestDescentGeometryContext.μ] using
          (integrable_const (μ := S.toStochasticSteepestDescentGeometryContext.μ) (S.f S.WStar))
      have hInit :
          MeasureTheory.Integrable initialSuboptimalityPath S.μ := by
        simpa [initialSuboptimalityPath, StochasticFrankWolfeGeometryContext.suboptimality] using
          (S.toStochasticSteepestDescentGeometryContext.objective_integrable 0).sub
            hConstWStar
      simpa [c0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hInit.const_mul ((S.lambda * S.eta * T)⁻¹)
    have hConst2 :
        MeasureTheory.Integrable (fun _ : Ω => c2) S.μ := by
      exact MeasureTheory.integrable_const _
    have hG :
        MeasureTheory.Integrable g S.μ := by
      dsimp [g]
      have hSumInt :
          MeasureTheory.Integrable
            (fun ω => Finset.sum (Finset.range T) (fun t => S.nesterovErrorNorm t ω)) S.μ := by
        exact
          MeasureTheory.integrable_finset_sum
            (Finset.range T)
            (fun t _ => S.toStochasticSteepestDescentGeometryContext.nesterovErrorNorm_integrable t)
      simpa [g, mul_assoc, mul_comm] using hSumInt.const_mul (2 / (S.lambda * T))
    calc
      ∫ ω, rhs ω ∂S.μ
        = ∫ ω, (c0 ω + g ω) + (fun _ : Ω => c2) ω ∂S.μ := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              simp [rhs, c0, c2, g, mul_assoc, mul_comm]
      _ =
          ∫ ω, (c0 ω + g ω) ∂S.μ + ∫ ω, (fun _ : Ω => c2) ω ∂S.μ := by
            simpa [add_assoc] using
              (MeasureTheory.integral_add (hConst0.add hG) hConst2 :
                ∫ ω, ((c0 ω + g ω) + (fun _ : Ω => c2) ω) ∂S.μ
                  =
                    ∫ ω, (c0 ω + g ω) ∂S.μ
                      + ∫ ω, (fun _ : Ω => c2) ω ∂S.μ)
      _ =
          ∫ ω, c0 ω ∂S.μ + ∫ ω, g ω ∂S.μ + c2 := by
            rw [MeasureTheory.integral_add hConst0 hG]
            letI := S.toStochasticSteepestDescentGeometryContext.prob
            simp [c2]
      _ =
          S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
            + ∫ ω, g ω ∂S.μ + c2 := by
              have hInit :
                  ∫ ω, c0 ω ∂S.μ = S.initialExpectedSuboptimality / (S.lambda * S.eta * T) := by
                have hConstWStar :
                    Integrable (fun _ : Ω => S.f S.WStar) S.μ := by
                  letI := S.toStochasticSteepestDescentGeometryContext.prob
                  simpa [StochasticSteepestDescentGeometryContext.μ] using
                    (integrable_const (μ := S.toStochasticSteepestDescentGeometryContext.μ) (S.f S.WStar))
                have hGapInt : Integrable initialSuboptimalityPath S.μ := by
                  simpa [initialSuboptimalityPath, StochasticFrankWolfeGeometryContext.suboptimality] using
                    (S.toStochasticSteepestDescentGeometryContext.objective_integrable 0).sub
                      hConstWStar
                calc
                  ∫ ω, c0 ω ∂S.μ
                    = ∫ ω, (((S.lambda * S.eta * T)⁻¹) * initialSuboptimalityPath ω) ∂S.μ := by
                        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                        intro ω
                        simp [c0, div_eq_mul_inv, mul_assoc, mul_comm]
                  _ = ((S.lambda * S.eta * T)⁻¹) * ∫ ω, initialSuboptimalityPath ω ∂S.μ := by
                        rw [MeasureTheory.integral_const_mul]
                  _ = ((S.lambda * S.eta * T)⁻¹) * S.initialExpectedSuboptimality := by
                        unfold StochasticFrankWolfeGeometryContext.initialExpectedSuboptimality
                        unfold StochasticFrankWolfeGeometryContext.expectedSuboptimality
                        simp [initialSuboptimalityPath,
                          StochasticFrankWolfeGeometryContext.suboptimality]
                  _ = S.initialExpectedSuboptimality / (S.lambda * S.eta * T) := by
                        rw [div_eq_mul_inv, mul_comm]
              rw [hInit]
      _ =
          S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
            + (2 / (S.lambda * T))
                * (Finset.sum (Finset.range T)
                    (fun t => ∫ ω, S.nesterovErrorNorm t ω ∂S.μ))
            + c2 := by
              rw [hIntG]
      _ =
          S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
            + (2 / (S.lambda * T))
                * (Finset.sum (Finset.range T) fun t =>
                    S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)
            + 2 * S.L * S.eta / S.lambda := by
              simp [c2, StochasticSteepestDescentGeometryContext.expectedNesterovError]
  have hAvgNesterov :
      (Finset.sum (Finset.range T)
          (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)) / (T : ℝ) ≤
        (S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
    simpa [StochasticSteepestDescentGeometryContext.initialExpectedMomentumError] using
      (StochasticSteepestDescentGeometryContext.corollary11_average_nesterovError_bound
        S.toStochasticSteepestDescentGeometryContext T hT)
  have hScaledAvgNesterov :
      (2 / S.lambda) *
          ((Finset.sum (Finset.range T)
              (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)) / (T : ℝ))
        ≤
        (2 / S.lambda)
          * ((S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (T : ℝ)
              + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
              + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) := by
    have hScaleNonneg : 0 ≤ 2 / S.lambda := by
      exact div_nonneg (by positivity) S.lambda_pos.le
    exact mul_le_mul_of_nonneg_left hAvgNesterov hScaleNonneg
  have hMain :
      (Finset.sum (Finset.range T) fun t => S.expectedFrankWolfeGap t) / (T : ℝ) ≤
        S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
          + (2 / S.lambda) *
              ((Finset.sum (Finset.range T)
                  (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)) / (T : ℝ))
          + 2 * S.L * S.eta / S.lambda := by
    rw [hLhsEval, hRhsEval] at hIntegrated
    have hRewrite :
        (2 / (S.lambda * T))
          * (Finset.sum (Finset.range T)
              (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t))
        =
        (2 / S.lambda) *
          ((Finset.sum (Finset.range T)
              (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)) / (T : ℝ)) := by
      field_simp [show (T : ℝ) ≠ 0 by positivity, S.lambda_pos.ne']
    rw [hRewrite] at hIntegrated
    exact hIntegrated
  calc
    (Finset.sum (Finset.range T) fun t => S.expectedFrankWolfeGap t) / (T : ℝ)
      ≤ S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
          + (2 / S.lambda) *
              ((Finset.sum (Finset.range T)
                  (fun t => S.toStochasticSteepestDescentGeometryContext.expectedNesterovError t)) / (T : ℝ))
          + 2 * S.L * S.eta / S.lambda := hMain
    _ ≤ S.initialExpectedSuboptimality / (S.lambda * S.eta * T)
          + (2 / S.lambda)
              * ((S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (T : ℝ)
                  + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
                  + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ)
          + 2 * S.L * S.eta / S.lambda := by
            gcongr
    _ = (S.initialExpectedSuboptimality) / (S.lambda * S.eta * T)
          + (2 * S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
          + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
              (S.lambda * Real.sqrt S.batchSizeℝ)
          + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
            field_simp [show (T : ℝ) ≠ 0 by positivity, S.lambda_pos.ne',
              S.one_sub_beta_ne_zero, S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero]
            ring

/-- Lean-friendly best-iterate corollary for the expected Frank-Wolfe gap. -/
theorem best_iterate_frankWolfeExpectedGap_nesterov_wd
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    ∀ T, 0 < T →
      ∃ t < T,
        S.expectedFrankWolfeGap t ≤
          (S.initialExpectedSuboptimality) / (S.lambda * S.eta * T)
            + (2 * S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
            + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
                (S.lambda * Real.sqrt S.batchSizeℝ)
            + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
  intro T hT
  let rhs : ℝ :=
    (S.initialExpectedSuboptimality) / (S.lambda * S.eta * T)
      + (2 * S.initialExpectedMomentumError * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
      + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
          (S.lambda * Real.sqrt S.batchSizeℝ)
      + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta))
  have hAvg := S.avg_frankWolfeExpectedGap_nesterov_wd T hT
  have hT' : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hSum :
      Finset.sum (Finset.range T) (fun t => S.expectedFrankWolfeGap t) ≤
        Finset.sum (Finset.range T) (fun _ => rhs) := by
    have := (div_le_iff₀ hT').1 hAvg
    calc
      Finset.sum (Finset.range T) (fun t => S.expectedFrankWolfeGap t) ≤ (T : ℝ) * rhs := by
        simpa [rhs, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this
      _ = Finset.sum (Finset.range T) (fun _ => rhs) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp
  have hNonempty : (Finset.range T).Nonempty := by
    cases T with
    | zero =>
        cases (lt_irrefl 0 hT)
    | succ _ =>
        exact ⟨0, by simp⟩
  obtain ⟨t, htMem, htLe⟩ := Finset.exists_le_of_sum_le hNonempty hSum
  refine ⟨t, Finset.mem_range.mp htMem, ?_⟩
  simpa [rhs] using htLe

end PublicTheorems

end StochasticFrankWolfeGeometryContext

end

end SteepestDescentOptimizationBounds
