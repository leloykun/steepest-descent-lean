import Mathlib
import SteepestDescentOptimizationBounds.Assumptions

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Common geometric feasibility and update-control lemmas for the decoupled
weight-decay iteration.

Upstream dependency:

- `Assumptions.lean` provides both the deterministic sample-path geometry
  context and the realized stochastic context that wraps it.

Downstream use:

- `StarConvex.lean` reuses the common iterate/update ball geometry.
- `FrankWolfe.lean` reuses it directly for the pathwise
  Frank-Wolfe-gap descent argument.
- `MomentumBounds.lean` reuses the pathwise update bound inside the expected
  momentum-recursion estimate.
-/

section PathGeometry

namespace SteepestDescentPathGeometryContext

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The center of the radius-`η` feasible ball used by the update. -/
def stepCenter (S : SteepestDescentPathGeometryContext V) (t : ℕ) : V :=
  (1 - S.lambda * S.eta) • S.W t

/-- The chosen LMO direction lies in the primal unit ball. -/
lemma aStar_norm_le
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    ‖S.aStar t‖ ≤ 1 :=
  (S.aStar_spec t).1

/-- The chosen LMO direction minimizes the pairing over the primal unit ball. -/
lemma aStar_optimal
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) (A : V) (hA : ‖A‖ ≤ 1) :
    (S.C t) (S.aStar t) ≤ (S.C t) A :=
  (S.aStar_spec t).2 A hA

/-- The weight-decay step is exactly the center plus `η` times the LMO direction. -/
lemma step_sub_center
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    S.W (t + 1) - S.stepCenter t = S.eta • S.aStar t := by
  rw [S.update_eq t, SteepestDescentPathGeometryContext.stepCenter]
  abel_nf

/-- Rewrites the displacement from `W_t` to the step center as a scaled copy of `W_t`. -/
lemma weight_sub_stepCenter
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    S.W t - S.stepCenter t = (S.lambda * S.eta) • S.W t := by
  simp [SteepestDescentPathGeometryContext.stepCenter, sub_eq_add_neg, one_smul, add_smul]

/-- The update is feasible because the chosen LMO direction has norm at most `1`. -/
lemma step_feasible
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
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
    (S : SteepestDescentPathGeometryContext V)
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
          rw [S.update_eq t, SteepestDescentPathGeometryContext.stepCenter,
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

/-- Bootstraps the bound `‖W_t‖ ≤ constraintRadius` for every iterate. -/
lemma weight_bound_from_feasible_step
    (S : SteepestDescentPathGeometryContext V) :
    ∀ t, ‖S.W t‖ ≤ S.constraintRadius
  | 0 => S.W0_bound
  | t + 1 => by
      have hScaleNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
      have hPrev := weight_bound_from_feasible_step S t
      calc
        ‖S.W (t + 1)‖ = ‖(S.W (t + 1) - S.stepCenter t) + S.stepCenter t‖ := by
          congr
          simp [SteepestDescentPathGeometryContext.stepCenter]
        _ ≤ ‖S.W (t + 1) - S.stepCenter t‖ + ‖S.stepCenter t‖ := norm_add_le _ _
        _ ≤ S.eta + ‖S.stepCenter t‖ := by
          gcongr
          exact S.step_feasible t
        _ = S.eta + (1 - S.lambda * S.eta) * ‖S.W t‖ := by
          simp [SteepestDescentPathGeometryContext.stepCenter, norm_smul,
            Real.norm_of_nonneg hScaleNonneg]
        _ ≤ S.eta + (1 - S.lambda * S.eta) * S.constraintRadius := by
          gcongr
        _ = S.constraintRadius := by
          have hEq : S.lambda * S.constraintRadius = 1 := S.lambda_mul_constraintRadius_eq_one
          have hEq' : (S.lambda * S.eta) * S.constraintRadius = S.eta := by
            calc
              (S.lambda * S.eta) * S.constraintRadius = S.eta * (S.lambda * S.constraintRadius) := by ring
              _ = S.eta := by rw [hEq]; ring
          calc
            S.eta + (1 - S.lambda * S.eta) * S.constraintRadius
                = S.eta + S.constraintRadius - (S.lambda * S.eta) * S.constraintRadius := by ring
            _ = S.eta + S.constraintRadius - S.eta := by rw [hEq']
            _ = S.constraintRadius := by ring

/-- The decoupled weight-decay specialization implies `η ≤ λη * constraintRadius`. -/
private lemma eta_le_lambda_eta_mul_constraintRadius
    (S : SteepestDescentPathGeometryContext V) :
    S.eta ≤ (S.lambda * S.eta) * S.constraintRadius := by
  have hEq : S.lambda * S.constraintRadius = 1 := S.lambda_mul_constraintRadius_eq_one
  nlinarith [S.eta_pos]

/--
Every iterate remains inside the `constraintRadius` ball, and every update has size at
most `2η`.
-/
theorem proposition9_weight_and_update_bounds
    (S : SteepestDescentPathGeometryContext V) :
    ∀ t, ‖S.W t‖ ≤ S.constraintRadius ∧ ‖S.W (t + 1) - S.W t‖ ≤ 2 * S.eta := by
  intro t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hWeight := S.weight_bound_from_feasible_step t
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
    _ ≤ S.eta + (S.lambda * S.eta) * S.constraintRadius := by
          gcongr
    _ ≤ (S.lambda * S.eta) * S.constraintRadius + (S.lambda * S.eta) * S.constraintRadius := by
          have hEta : S.eta ≤ (S.lambda * S.eta) * S.constraintRadius :=
            S.eta_le_lambda_eta_mul_constraintRadius
          linarith
    _ = 2 * S.eta := by
          have hEq : S.lambda * S.constraintRadius = 1 := S.lambda_mul_constraintRadius_eq_one
          calc
            (S.lambda * S.eta) * S.constraintRadius + (S.lambda * S.eta) * S.constraintRadius
                = (S.lambda * S.constraintRadius) * (S.eta + S.eta) := by ring
            _ = 1 * (S.eta + S.eta) := by rw [hEq]
            _ = 2 * S.eta := by ring

end SteepestDescentPathGeometryContext

end PathGeometry

section StochasticWrappers

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-- The center of the radius-`η` feasible ball along a realized sample path. -/
def stepCenter (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : V :=
  (S.path ω).stepCenter t

/-- The chosen LMO direction lies in the primal unit ball pathwise. -/
lemma aStar_norm_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.aStar t ω‖ ≤ 1 := by
  simpa [StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).aStar_norm_le t

/-- The chosen LMO direction minimizes the pairing pathwise. -/
lemma aStar_optimal
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (ω : Ω) (A : V) (hA : ‖A‖ ≤ 1) :
    (S.C t ω) (S.aStar t ω) ≤ (S.C t ω) A := by
  simpa [StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).aStar_optimal t A hA

/-- The weight-decay step is exactly the center plus `η` times the LMO direction pathwise. -/
lemma step_sub_center
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.W (t + 1) ω - S.stepCenter t ω = S.eta • S.aStar t ω := by
  simpa [StochasticSteepestDescentGeometryContext.stepCenter,
    StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).step_sub_center t

/-- Rewrites the displacement from `W_t` to the step center pathwise. -/
lemma weight_sub_stepCenter
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.W t ω - S.stepCenter t ω = (S.lambda * S.eta) • S.W t ω := by
  simpa [StochasticSteepestDescentGeometryContext.stepCenter,
    StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).weight_sub_stepCenter t

/-- The update is feasible pathwise. -/
lemma step_feasible
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.W (t + 1) ω - S.stepCenter t ω‖ ≤ S.eta := by
  simpa [StochasticSteepestDescentGeometryContext.stepCenter,
    StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).step_feasible t

/-- Linear-minimization optimality along a realized sample path. -/
lemma step_optimal
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (ω : Ω) (X : V) (hX : ‖X - S.stepCenter t ω‖ ≤ S.eta) :
    (S.C t ω) (S.W (t + 1) ω) ≤ (S.C t ω) X := by
  simpa [StochasticSteepestDescentGeometryContext.stepCenter,
    StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).step_optimal t X hX

/-- The iterate norm stays inside the generic constraint ball pathwise. -/
lemma weight_bound_from_feasible_step
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω, ‖S.W t ω‖ ≤ S.constraintRadius := by
  intro t ω
  simpa [StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).weight_bound_from_feasible_step t

/-- Pathwise iterate/update ball bound for the decoupled weight-decay step. -/
theorem proposition9_weight_and_update_bounds
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω, ‖S.W t ω‖ ≤ S.constraintRadius ∧ ‖S.W (t + 1) ω - S.W t ω‖ ≤ 2 * S.eta := by
  intro t ω
  simpa [StochasticSteepestDescentGeometryContext.path] using
    (S.path ω).proposition9_weight_and_update_bounds t

end StochasticSteepestDescentGeometryContext

end StochasticWrappers

end

end SteepestDescentOptimizationBounds
