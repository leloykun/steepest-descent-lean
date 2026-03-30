import Mathlib
import SteepestDescentOptimizationBounds.Assumptions

namespace SteepestDescentOptimizationBounds

noncomputable section

section Geometry

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The chosen LMO direction lies in the primal unit ball. -/
lemma aStar_norm_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.aStar t‖ ≤ 1 :=
  (S.aStar_spec t).1

/-- The chosen LMO direction minimizes the pairing over the primal unit ball. -/
lemma aStar_optimal
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (A : V) (hA : ‖A‖ ≤ 1) :
    (S.C t) (S.aStar t) ≤ (S.C t) A :=
  (S.aStar_spec t).2 A hA

/-- The weight-decay step is exactly the center plus `η` times the LMO direction. -/
lemma step_sub_center
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.W (t + 1) - S.stepCenter t = S.eta • S.aStar t := by
  rw [S.update_eq t, StochasticSteepestDescentGeometryContext.stepCenter]
  abel_nf

/-- Rewrites the displacement from `W_t` to the step center as a scaled copy of `W_t`. -/
lemma weight_sub_stepCenter
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.W t - S.stepCenter t = (S.lambda * S.eta) • S.W t := by
  simp [StochasticSteepestDescentGeometryContext.stepCenter, sub_eq_add_neg, one_smul, add_smul]

/-- Rewrites the displacement from the step center to `X_t` as a scaled copy of `W_*`. -/
lemma interpolatedPoint_sub_stepCenter
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.interpolatedPoint t - S.stepCenter t = (S.lambda * S.eta) • S.WStar := by
  simp [StochasticSteepestDescentGeometryContext.interpolatedPoint]

/-- The update is feasible because the chosen LMO direction has norm at most `1`. -/
lemma step_feasible
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.W (t + 1) - S.stepCenter t‖ ≤ S.eta := by
  rw [S.step_sub_center t]
  calc
    ‖S.eta • S.aStar t‖ = S.eta * ‖S.aStar t‖ := by
      simp [norm_smul, Real.norm_of_nonneg S.eta_pos.le]
    _ ≤ S.eta * 1 := by
      exact mul_le_mul_of_nonneg_left (S.aStar_norm_le t) S.eta_pos.le
    _ = S.eta := by ring

/--
Any point feasible for the radius-`η` ball is no better than the chosen update
for the linear minimization subproblem.
-/
lemma step_optimal
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (X : V) (hX : ‖X - S.stepCenter t‖ ≤ S.eta) :
    (S.C t) (S.W (t + 1)) ≤ (S.C t) X := by
  let A : V := (1 / S.eta) • (X - S.stepCenter t)
  have hANorm : ‖A‖ ≤ 1 := by
    have hInvNonneg : 0 ≤ 1 / S.eta := one_div_nonneg.mpr S.eta_pos.le
    calc
      ‖A‖ = (1 / S.eta) * ‖X - S.stepCenter t‖ := by
        dsimp [A]
        rw [norm_smul, Real.norm_of_nonneg hInvNonneg]
      _ ≤ (1 / S.eta) * S.eta := by
        exact mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 1 := by
        field_simp [S.eta_pos.ne']
  have hOpt := S.aStar_optimal t A hANorm
  have hScale : S.eta • A = X - S.stepCenter t := by
    dsimp [A]
    calc
      S.eta • ((1 / S.eta) • (X - S.stepCenter t))
          = (S.eta * (1 / S.eta)) • (X - S.stepCenter t) := by
              rw [smul_smul]
      _ = (1 : ℝ) • (X - S.stepCenter t) := by
            field_simp [S.eta_pos.ne']
      _ = X - S.stepCenter t := by simp
  have hXeq : X = S.stepCenter t + S.eta • A := by
    calc
      X = S.stepCenter t + (X - S.stepCenter t) := by
          abel_nf
      _ = S.stepCenter t + S.eta • A := by rw [hScale]
  have hPairX :
      (S.C t) X =
        (S.C t) (S.stepCenter t) + S.eta * (S.C t) A := by
    rw [hXeq, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
    simp [smul_eq_mul]
  calc
    (S.C t) (S.W (t + 1))
      = (S.C t) (S.stepCenter t) + S.eta * (S.C t) (S.aStar t) := by
          rw [S.update_eq t, StochasticSteepestDescentGeometryContext.stepCenter,
            ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
          simp [smul_eq_mul]
    _ ≤ (S.C t) (S.stepCenter t) + S.eta * (S.C t) A := by
          have hScaledOpt :
              S.eta * (S.C t) (S.aStar t) ≤ S.eta * (S.C t) A :=
            mul_le_mul_of_nonneg_left hOpt S.eta_pos.le
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hScaledOpt ((S.C t) (S.stepCenter t))
    _ = (S.C t) X := by
          exact hPairX.symm

/-- Bootstraps the bound `‖W_t‖ ≤ 1 / λ` for every iterate. -/
lemma weight_bound_from_feasible_step
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, ‖S.W t‖ ≤ 1 / S.lambda
  | 0 => S.W0_bound
  | t + 1 => by
      have hScaleNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
      have hPrev := weight_bound_from_feasible_step S t
      calc
        ‖S.W (t + 1)‖ = ‖(S.W (t + 1) - S.stepCenter t) + S.stepCenter t‖ := by
          congr
          simp [StochasticSteepestDescentGeometryContext.stepCenter]
        _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.stepCenter t‖ := norm_add_le _ _
        _ ≤ S.eta + ‖S.stepCenter t‖ := by
          gcongr
          exact S.step_feasible t
        _ = S.eta + (1 - S.lambda * S.eta) * ‖S.W t‖ := by
          simp [StochasticSteepestDescentGeometryContext.stepCenter, norm_smul,
            Real.norm_of_nonneg hScaleNonneg]
        _ ≤ S.eta + (1 - S.lambda * S.eta) * (1 / S.lambda) := by
          gcongr
        _ = 1 / S.lambda := by
          field_simp [S.lambda_pos.ne']
          ring

/--
Proposition 9: every iterate remains inside the `1 / λ` ball, and every update
has size at most `2η`.
-/
theorem proposition9_weight_and_update_bounds
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, ‖S.W t‖ ≤ 1 / S.lambda ∧ ‖S.W (t + 1) - S.W t‖ ≤ 2 * S.eta := by
  intro t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hWeight := weight_bound_from_feasible_step S t
  refine ⟨hWeight, ?_⟩
  calc
    ‖S.W (t + 1) - S.W t‖
        = ‖(S.W (t + 1) - S.stepCenter t) - (S.W t - S.stepCenter t)‖ := by
            have hDecomp :
                S.W (t + 1) - S.W t =
                  (S.W (t + 1) - S.stepCenter t) - (S.W t - S.stepCenter t) := by
              abel_nf
            rw [hDecomp]
    _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.W t - S.stepCenter t‖ := norm_sub_le _ _
    _ ≤ S.eta + ‖S.W t - S.stepCenter t‖ := by
          gcongr
          exact S.step_feasible t
    _ = S.eta + (S.lambda * S.eta) * ‖S.W t‖ := by
          rw [weight_sub_stepCenter]
          simp [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ S.eta + (S.lambda * S.eta) * (1 / S.lambda) := by
          gcongr
    _ = 2 * S.eta := by
          field_simp [S.lambda_pos.ne']
          ring

/-- Shows that the auxiliary point `X_t` is feasible for the linear minimization step. -/
lemma interpolatedPoint_feasible
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.interpolatedPoint t - S.stepCenter t‖ ≤ S.eta := by
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  calc
    ‖S.interpolatedPoint t - S.stepCenter t‖ = ‖(S.lambda * S.eta) • S.WStar‖ := by
      rw [interpolatedPoint_sub_stepCenter]
    _ = (S.lambda * S.eta) * ‖S.WStar‖ := by
      simp [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
      gcongr
      exact S.WStar_bound
    _ = S.eta := by
      field_simp [S.lambda_pos.ne']

/-- The auxiliary point `X_t` also stays inside the primal `1 / λ` ball. -/
lemma interpolatedPoint_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda := by
  have hWeight := weight_bound_from_feasible_step S t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hDecayNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
  have hFirst :
      (1 - S.lambda * S.eta) * ‖S.W t‖ ≤ (1 - S.lambda * S.eta) * (1 / S.lambda) := by
    exact mul_le_mul_of_nonneg_left hWeight hDecayNonneg
  have hSecond :
      (S.lambda * S.eta) * ‖S.WStar‖ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
    exact mul_le_mul_of_nonneg_left S.WStar_bound hScaleNonneg
  calc
    ‖S.interpolatedPoint t‖
      = ‖(1 - S.lambda * S.eta) • S.W t + (S.lambda * S.eta) • S.WStar‖ := by
          simp [StochasticSteepestDescentGeometryContext.interpolatedPoint,
            StochasticSteepestDescentGeometryContext.stepCenter]
    _ ≤ ‖(1 - S.lambda * S.eta) • S.W t‖ + ‖(S.lambda * S.eta) • S.WStar‖ := norm_add_le _ _
    _ = (1 - S.lambda * S.eta) * ‖S.W t‖ + (S.lambda * S.eta) * ‖S.WStar‖ := by
          simp [norm_smul, Real.norm_of_nonneg hDecayNonneg, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (1 - S.lambda * S.eta) * (1 / S.lambda) + (S.lambda * S.eta) * (1 / S.lambda) := by
          linarith
    _ = 1 / S.lambda := by
          field_simp [S.lambda_pos.ne']
          ring

/-- Shows that the current iterate `W_t` is also feasible for the same radius-`η` ball. -/
lemma current_weight_feasible
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.W t - S.stepCenter t‖ ≤ S.eta := by
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hWeight := weight_bound_from_feasible_step S t
  calc
    ‖S.W t - S.stepCenter t‖ = ‖(S.lambda * S.eta) • S.W t‖ := by
      rw [weight_sub_stepCenter]
    _ = (S.lambda * S.eta) * ‖S.W t‖ := by
      simp [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
      gcongr
    _ = S.eta := by
      field_simp [S.lambda_pos.ne']

/--
Lemma 13: the chosen update is directionally optimal against `X_t`, and both
`W_t` and `W_{t+1}` stay within distance `2η` of `X_t`.
-/
theorem lemma13_directional_and_distance_bounds
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      (S.C t) (S.W (t + 1) - S.interpolatedPoint t) ≤ 0 ∧
        ‖S.W t - S.interpolatedPoint t‖ ≤ 2 * S.eta ∧
        ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤ 2 * S.eta := by
  intro t
  have hXFeasible := interpolatedPoint_feasible S t
  have hOptimal := S.step_optimal t (S.interpolatedPoint t) hXFeasible
  refine ⟨?_, ?_, ?_⟩
  · have : (S.C t) (S.W (t + 1)) - (S.C t) (S.interpolatedPoint t) ≤ 0 :=
      sub_nonpos.mpr hOptimal
    simpa using this
  · calc
      ‖S.W t - S.interpolatedPoint t‖
          = ‖(S.W t - S.stepCenter t) - (S.interpolatedPoint t - S.stepCenter t)‖ := by
              have hDecomp :
                  S.W t - S.interpolatedPoint t =
                    (S.W t - S.stepCenter t) - (S.interpolatedPoint t - S.stepCenter t) := by
                abel_nf
              rw [hDecomp]
      _ ≤ ‖S.W t - S.stepCenter t‖ + ‖S.interpolatedPoint t - S.stepCenter t‖ := norm_sub_le _ _
      _ ≤ S.eta + S.eta := by
            gcongr
            exact S.current_weight_feasible t
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
      _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.interpolatedPoint t - S.stepCenter t‖ := norm_sub_le _ _
      _ ≤ S.eta + S.eta := by
            gcongr
            exact S.step_feasible t
      _ = 2 * S.eta := by ring

end StochasticSteepestDescentGeometryContext

end Geometry

end

end SteepestDescentOptimizationBounds
