import Mathlib
import SteepestDescentOptimizationBounds.FrankWolfe

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file builds the stochastic Frank-Wolfe expected-gap layer on top of
`FrankWolfe.lean`.

Upstream dependencies:

- `FrankWolfe.lean` provides the deterministic Frank-Wolfe-gap definition, the
  one-step descent theorem, and the generic tracking-bound / averaged
  recurrence layer.
- `NesterovMomentumBounds.lean`, imported transitively through `FrankWolfe`,
  provides the Corollary-11 pointwise tracking bound used for the concrete
  stochastic instantiation.

Downstream use:

- This file supplies the averaged Frank-Wolfe expected-gap theorem and the
  Lean-friendly best-iterate existence corollary.
-/

namespace StochasticFrankWolfeGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

-- No new public definitions are needed in this file.

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

-- No private definitions are needed in this file.

end PrivateDefinitions

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

/-- Concrete averaged Frank-Wolfe expected-gap theorem obtained by instantiating the generic tracking-bound theorem with Corollary 11. -/
theorem avg_frankWolfeExpectedGap_nesterov_wd
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.frankWolfeGap t) / (T : ℝ) ≤
        S.suboptimality 0 / (S.lambda * S.eta * T)
          + (2 * S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
          + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
              (S.lambda * Real.sqrt S.batchSizeℝ)
          + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
  intro T hT
  let drift : ℝ := (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
  let noise : ℝ :=
    (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ
  let err : ℕ → ℝ := fun t => S.beta ^ (t + 1) * S.initialGradNorm + drift + noise
  have hBase :=
    S.avg_frankWolfeGap_bound_of_tracking_bound
      (fInf := S.f S.WStar)
      (err := err)
      (hInf := fun t => S.WStar_optimality (S.W t))
      (hErr := Corollary11PointwiseNesterovErrorBound S.toStochasticSteepestDescentGeometryContext)
      T hT
  have hGeom :
      Finset.sum (Finset.range T) (fun t => S.beta ^ (t + 1) * S.initialGradNorm) =
        shiftedGeometricPrefix S.beta T * S.initialGradNorm := by
    simp [shiftedGeometricPrefix, Finset.sum_mul]
  have hErrSum :
      Finset.sum (Finset.range T) err =
        shiftedGeometricPrefix S.beta T * S.initialGradNorm + (T : ℝ) * drift + (T : ℝ) * noise := by
    rw [show Finset.sum (Finset.range T) err =
          Finset.sum (Finset.range T) (fun t => S.beta ^ (t + 1) * S.initialGradNorm)
            + Finset.sum (Finset.range T) (fun _ => drift)
            + Finset.sum (Finset.range T) (fun _ => noise) by
          simp [err, Finset.sum_add_distrib, add_assoc]]
    rw [hGeom]
    simp [drift, noise]
  calc
    (Finset.sum (Finset.range T) fun t => S.frankWolfeGap t) / (T : ℝ)
      ≤ (S.f (S.W 0) - S.f S.WStar) / (S.lambda * S.eta * T)
          + (2 / (S.lambda * T)) * (Finset.sum (Finset.range T) err)
          + 2 * S.L * S.eta / S.lambda := hBase
    _ = S.suboptimality 0 / (S.lambda * S.eta * T)
          + (2 / (S.lambda * T)) *
              (shiftedGeometricPrefix S.beta T * S.initialGradNorm + (T : ℝ) * drift + (T : ℝ) * noise)
          + 2 * S.L * S.eta / S.lambda := by
            rw [hErrSum]
            simp [StochasticSteepestDescentGeometryContext.suboptimality]
    _ = S.suboptimality 0 / (S.lambda * S.eta * T)
          + (2 * S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
          + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
              (S.lambda * Real.sqrt S.batchSizeℝ)
          + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
            simp [drift, noise]
            field_simp [S.lambda_pos.ne', S.eta_pos.ne', S.one_sub_beta_ne_zero,
              S.batchSizeℝ_ne_zero, S.sqrt_batchSizeℝ_ne_zero, show (T : ℝ) ≠ 0 by positivity]
            ring

/-- Lean-friendly best-iterate Frank-Wolfe expected-gap corollary. This is the usual `min ≤ average` conclusion expressed as an existence statement. -/
-- corollary best_iterate_frankWolfeExpectedGap_nesterov_wd
theorem best_iterate_frankWolfeExpectedGap_nesterov_wd
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    ∀ T, 0 < T →
      ∃ t < T,
        S.frankWolfeGap t ≤
          S.suboptimality 0 / (S.lambda * S.eta * T)
            + (2 * S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
            + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
                (S.lambda * Real.sqrt S.batchSizeℝ)
            + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta)) := by
  intro T hT
  let rhs : ℝ :=
    S.suboptimality 0 / (S.lambda * S.eta * T)
      + (2 * S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (S.lambda * T)
      + (2 * S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) /
          (S.lambda * Real.sqrt S.batchSizeℝ)
      + (2 * S.L * S.eta / S.lambda) * (1 + 2 * S.beta ^ 2 / (1 - S.beta))
  have hAvg := S.avg_frankWolfeExpectedGap_nesterov_wd T hT
  have hT' : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hSum :
      Finset.sum (Finset.range T) (fun t => S.frankWolfeGap t) ≤
        Finset.sum (Finset.range T) (fun _ => rhs) := by
    have := (div_le_iff₀ hT').1 hAvg
    calc
      Finset.sum (Finset.range T) (fun t => S.frankWolfeGap t) ≤ (T : ℝ) * rhs := by
        simpa [rhs, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this
      _ = Finset.sum (Finset.range T) (fun _ => rhs) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp
  have hNonempty : (Finset.range T).Nonempty := by
    cases T with
    | zero =>
        cases (lt_irrefl 0 hT)
    | succ n =>
        exact ⟨0, by simp⟩
  obtain ⟨t, htMem, htLe⟩ := Finset.exists_le_of_sum_le hNonempty hSum
  refine ⟨t, Finset.mem_range.mp htMem, ?_⟩
  simpa [rhs] using htLe

end PublicTheorems

end StochasticFrankWolfeGeometryContext

end

end SteepestDescentOptimizationBounds
