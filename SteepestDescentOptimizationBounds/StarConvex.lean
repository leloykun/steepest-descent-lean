import Mathlib
import SteepestDescentOptimizationBounds.DescentLemma
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds
import SteepestDescentOptimizationBounds.NesterovMomentumBounds

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
Deterministic and pathwise star-convex descent layer.

Upstream dependencies:

- `DescentLemma.lean` supplies the local Taylor comparison.
- `WeightAndUpdateBounds.lean` supplies the decoupled weight-decay geometry.
- `NesterovMomentumBounds.lean` supplies the Nesterov-residual split.

Downstream use:

- `StarConvexExpectedSuboptimality.lean` integrates the pathwise recurrence.
- the scaling-law layer reuses the deterministic coefficient definitions from
  the `StochasticStarConvexGeometryContext` namespace.
-/

namespace StarConvexPathGeometryContext

section PrivateDefinitions

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The linear functional induced by the current true gradient. -/
private def gradientLinear (S : StarConvexPathGeometryContext V) (t : ℕ) : V →ₗ[ℝ] ℝ :=
  (S.grad t).toLinearMap

/-- The interpolation point `X_t = (1 - λη) W_t + λη W_*`. -/
private def interpolatedPoint (S : StarConvexPathGeometryContext V) (t : ℕ) : V :=
  S.stepCenter t + (S.lambda * S.eta) • S.WStar

-- No additional private definitions are needed beyond the helper geometry above.

end PrivateDefinitions

section PrivateLemmas

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Unpacks `∇f(W_t) = C_t + error_t` on a concrete vector. -/
private lemma grad_split_apply
    (S : StarConvexPathGeometryContext V) (t : ℕ) (v : V) :
    S.gradientLinear t v = (S.C t) v + S.nesterovError t v := by
  rw [gradientLinear, SteepestDescentPathGeometryContext.nesterovError, S.C_spec t]
  simp [SteepestDescentPathGeometryContext.grad, sub_eq_add_neg]
  ring

/-- File-local star-convex interpolation inequality from Assumption 12. -/
private lemma star_convex_prop
    (S : StarConvexPathGeometryContext V) :
    ∀ W α, 0 ≤ α → α ≤ 1 →
      S.f ((1 - α) • W + α • S.WStar) ≤ (1 - α) * S.f W + α * S.f S.WStar :=
  Assumption12_StarConvexityAtReferencePoint.star_convex S.assumption12_starConvexity

/-- Shared scaling estimate for vectors already in the radius-`1 / λ` ball. -/
private lemma scaled_norm_le_eta
    (S : StarConvexPathGeometryContext V) {x : V}
    (hx : ‖x‖ ≤ 1 / S.lambda) :
    ‖(S.lambda * S.eta) • x‖ ≤ S.eta := by
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  calc
    ‖(S.lambda * S.eta) • x‖ = (S.lambda * S.eta) * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (S.lambda * S.eta) * (1 / S.lambda) := by
      exact mul_le_mul_of_nonneg_left hx hScaleNonneg
    _ = S.eta := by
      field_simp [S.lambda_pos.ne']

end PrivateLemmas

section PublicTheorems

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Rewrites the displacement from the step center to `X_t`. -/
private lemma interpolatedPoint_sub_stepCenter
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    S.interpolatedPoint t - S.stepCenter t = (S.lambda * S.eta) • S.WStar := by
  simp [interpolatedPoint]

/-- The interpolation point is feasible for the linearized update ball. -/
private lemma interpolatedPoint_feasible
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t - S.stepCenter t‖ ≤ S.eta := by
  calc
    ‖S.interpolatedPoint t - S.stepCenter t‖ = ‖(S.lambda * S.eta) • S.WStar‖ := by
      rw [interpolatedPoint_sub_stepCenter]
    _ ≤ S.eta := S.scaled_norm_le_eta S.WStar_bound

/-- The interpolation point also stays in the primal radius-`1 / λ` ball. -/
private lemma interpolatedPoint_bound
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda := by
  have hWeight := S.weight_bound_from_feasible_step t
  have hScaleNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hDecayNonneg : 0 ≤ 1 - S.lambda * S.eta := S.one_sub_lambda_eta_nonneg
  calc
    ‖S.interpolatedPoint t‖
      = ‖(1 - S.lambda * S.eta) • S.W t + (S.lambda * S.eta) • S.WStar‖ := by
          simp [interpolatedPoint, SteepestDescentPathGeometryContext.stepCenter]
    _ ≤ ‖(1 - S.lambda * S.eta) • S.W t‖ + ‖(S.lambda * S.eta) • S.WStar‖ := norm_add_le _ _
    _ = (1 - S.lambda * S.eta) * ‖S.W t‖ + (S.lambda * S.eta) * ‖S.WStar‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hDecayNonneg, Real.norm_of_nonneg hScaleNonneg]
    _ ≤ (1 - S.lambda * S.eta) * (1 / S.lambda) + (S.lambda * S.eta) * (1 / S.lambda) := by
          have hFirst :
              (1 - S.lambda * S.eta) * ‖S.W t‖ ≤
                (1 - S.lambda * S.eta) * (1 / S.lambda) := by
            exact mul_le_mul_of_nonneg_left hWeight hDecayNonneg
          have hSecond :
              (S.lambda * S.eta) * ‖S.WStar‖ ≤
                (S.lambda * S.eta) * (1 / S.lambda) := by
            exact mul_le_mul_of_nonneg_left S.WStar_bound hScaleNonneg
          linarith
    _ = 1 / S.lambda := by
          field_simp [S.lambda_pos.ne']
          ring

/-- Geometry package for the interpolation point used in the one-step proof. -/
private theorem lemma13_interpolatedPoint_geometry
    (S : StarConvexPathGeometryContext V) (t : ℕ) :
    ‖S.interpolatedPoint t‖ ≤ 1 / S.lambda ∧
      (S.C t) (S.W (t + 1) - S.interpolatedPoint t) ≤ 0 ∧
      ‖S.interpolatedPoint t - S.W t‖ ≤ 2 * S.eta ∧
      ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤ 2 * S.eta := by
  have hInterp := interpolatedPoint_bound S t
  have hXFeasible := interpolatedPoint_feasible S t
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step t
  have hWeightCenter : ‖S.W t - S.stepCenter t‖ ≤ S.eta := by
    rw [S.weight_sub_stepCenter t]
    exact S.scaled_norm_le_eta hWeight
  have hOptimal := S.step_optimal t (S.interpolatedPoint t) hXFeasible
  refine ⟨hInterp, ?_, ?_, ?_⟩
  · rw [(S.C t).map_sub]
    exact sub_nonpos.mpr hOptimal
  · calc
      ‖S.interpolatedPoint t - S.W t‖
          = ‖(S.interpolatedPoint t - S.stepCenter t) - (S.W t - S.stepCenter t)‖ := by
              abel_nf
      _ ≤ ‖S.interpolatedPoint t - S.stepCenter t‖ + ‖S.W t - S.stepCenter t‖ := norm_sub_le _ _
      _ ≤ S.eta + S.eta := add_le_add hXFeasible hWeightCenter
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
      _ ≤ S.eta + S.eta := add_le_add (S.step_feasible t) hXFeasible
      _ = 2 * S.eta := by ring

/-- Pathwise one-step star-convex descent with an explicit Nesterov residual. -/
theorem one_step_descent_bound
    (S : StarConvexPathGeometryContext V) :
    ∀ t,
      S.f (S.W (t + 1)) ≤
        S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hLemma13 := lemma13_interpolatedPoint_geometry S t
  rcases hLemma13 with ⟨hInterpWeight, hOptimalDir, hXWeightBound, hNextXBound⟩
  have hWeight : ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step t
  have hNextWeight : ‖S.W (t + 1)‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step (t + 1)
  have hUpdateBound : ‖S.W (t + 1) - S.W t‖ ≤ 2 * S.eta :=
    (S.proposition9_weight_and_update_bounds t).2
  have hGradDecomp :
      S.gradientLinear t (S.W (t + 1) - S.W t) =
        (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
          S.gradientLinear t (S.interpolatedPoint t - S.W t) +
          S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) := by
    have hSplit := grad_split_apply S t (S.W (t + 1) - S.interpolatedPoint t)
    have hDecomp :
        S.W (t + 1) - S.W t =
          (S.W (t + 1) - S.interpolatedPoint t) + (S.interpolatedPoint t - S.W t) := by
      abel_nf
    rw [hDecomp, LinearMap.map_add, hSplit]
    ring
  have hErrorTerm :
      S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) ≤
        2 * S.eta * S.nesterovErrorNorm t := by
    have hErr :
        S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t) ≤
          S.nesterovErrorNorm t * ‖S.W (t + 1) - S.interpolatedPoint t‖ :=
      le_trans (le_abs_self _)
        (S.nesterovError_apply_le t (S.W (t + 1) - S.interpolatedPoint t))
    have hMul :
        S.nesterovErrorNorm t * ‖S.W (t + 1) - S.interpolatedPoint t‖ ≤
          S.nesterovErrorNorm t * (2 * S.eta) := by
      gcongr
      exact S.nesterovErrorNorm_nonneg t
    nlinarith [hErr, hMul, hNextXBound]
  have hSmoothCompare :
      S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) ≤
        S.f (S.interpolatedPoint t) + 2 * S.L * S.eta ^ 2 := by
    have hCompLeft :
        S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) ≤
          S.f (S.interpolatedPoint t) + S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 := by
      simpa [gradientLinear, SteepestDescentPathGeometryContext.grad] using
        (taylor_compare_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
          (f := S.f)
          (grad := S.fGrad)
          (L := S.L)
          (R := 1 / S.lambda)
          S.fderiv_eq
          S.assumption3_fLocalSmoothness.local_lipschitz
          hWeight
          hInterpWeight
          (x := S.W t)
          (y := S.interpolatedPoint t))
    have hQuad :
        S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤ 2 * S.L * S.eta ^ 2 := by
      have hSquare : ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤ (2 * S.eta) ^ 2 := by
        nlinarith [norm_nonneg (S.interpolatedPoint t - S.W t), hXWeightBound]
      have hHalfLNonneg : 0 ≤ S.L / 2 := by
        exact div_nonneg S.assumption3_fLocalSmoothness.nonneg (by norm_num)
      nlinarith [hSquare, hHalfLNonneg]
    have hQuad' :
        S.f (S.interpolatedPoint t) + S.L / 2 * ‖S.interpolatedPoint t - S.W t‖ ^ 2 ≤
          S.f (S.interpolatedPoint t) + 2 * S.L * S.eta ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hQuad (S.f (S.interpolatedPoint t)))
    exact le_trans hCompLeft hQuad'
  have hSmoothStep :
      S.f (S.W (t + 1)) ≤
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
    have hStepRight :
        S.f (S.W (t + 1)) ≤
          S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
      simpa [gradientLinear, SteepestDescentPathGeometryContext.grad] using
        (step_upper_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
          (f := S.f)
          (grad := S.fGrad)
          (L := S.L)
          (R := 1 / S.lambda)
          (α := 1)
          S.fderiv_eq
          S.assumption3_fLocalSmoothness.local_lipschitz
          (by norm_num)
          (x := S.W t)
          (ξ := S.W (t + 1) - S.W t)
          hWeight
          (by simpa using hNextWeight))
    have hQuad :
        S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ 2 * S.L * S.eta ^ 2 := by
      have hSquare : ‖S.W (t + 1) - S.W t‖ ^ 2 ≤ (2 * S.eta) ^ 2 := by
        nlinarith [norm_nonneg (S.W (t + 1) - S.W t), hUpdateBound]
      have hHalfLNonneg : 0 ≤ S.L / 2 := by
        exact div_nonneg S.assumption3_fLocalSmoothness.nonneg (by norm_num)
      nlinarith [hSquare, hHalfLNonneg]
    have hQuad' :
        S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 ≤
          S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hQuad (S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t)))
    exact le_trans hStepRight hQuad'
  calc
    S.f (S.W (t + 1))
      ≤ S.f (S.W t) + S.gradientLinear t (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := hSmoothStep
    _ =
        S.f (S.W t) +
          ((S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
            S.gradientLinear t (S.interpolatedPoint t - S.W t) +
            S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)) +
          2 * S.L * S.eta ^ 2 := by rw [hGradDecomp]
    _ ≤ S.f (S.W t) + S.gradientLinear t (S.interpolatedPoint t - S.W t) + 2 * S.L * S.eta ^ 2 +
          2 * S.eta * S.nesterovErrorNorm t := by
            have hPairErr :
                (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
                  S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)
                  ≤ 2 * S.eta * S.nesterovErrorNorm t := by
              calc
                (S.C t) (S.W (t + 1) - S.interpolatedPoint t) +
                    S.nesterovError t (S.W (t + 1) - S.interpolatedPoint t)
                    ≤ 0 + 2 * S.eta * S.nesterovErrorNorm t := add_le_add hOptimalDir hErrorTerm
                _ = 2 * S.eta * S.nesterovErrorNorm t := by ring
            nlinarith [hPairErr]
    _ ≤ S.f (S.interpolatedPoint t) + 4 * S.L * S.eta ^ 2 + 2 * S.eta * S.nesterovErrorNorm t := by
          linarith [hSmoothCompare]

/-- Pathwise star-convex scalar recurrence. -/
theorem suboptimality_recurrence_step
    (S : StarConvexPathGeometryContext V) :
    ∀ t,
      S.suboptimality (t + 1) ≤
        (1 - S.lambda * S.eta) * S.suboptimality t
          + 4 * S.L * S.eta ^ 2
          + 2 * S.eta * S.nesterovErrorNorm t := by
  intro t
  have hAlphaNonneg : 0 ≤ S.lambda * S.eta := S.lambda_eta_nonneg
  have hStar :=
    star_convex_prop S (S.W t) (S.lambda * S.eta) hAlphaNonneg S.lambda_eta_le_one
  have hX :
      S.f (S.interpolatedPoint t) ≤
        (1 - S.lambda * S.eta) * S.f (S.W t) + (S.lambda * S.eta) * S.f S.WStar := by
    simpa [interpolatedPoint, SteepestDescentPathGeometryContext.stepCenter] using hStar
  have hLocal := S.one_step_descent_bound t
  dsimp [SteepestDescentPathGeometryContext.suboptimality]
  linarith

end PublicTheorems

end StarConvexPathGeometryContext

namespace StochasticStarConvexGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-! Public lemmas/theorems. -/
section PublicTheorems

/-- Pathwise scalar star-convex recurrence. -/
theorem suboptimality_recurrence_step
    (S : StochasticStarConvexGeometryContext Ω V) :
    ∀ t ω,
      S.suboptimality (t + 1) ω ≤
        (1 - S.lambda * S.eta) * S.suboptimality t ω
          + 4 * S.L * S.eta ^ 2
          + 2 * S.eta * S.nesterovErrorNorm t ω := by
  intro t ω
  have h := (S.path ω).suboptimality_recurrence_step t
  simpa [SteepestDescentPathGeometryContext.suboptimality,
    StochasticSteepestDescentGeometryContext.suboptimality] using h

end PublicTheorems

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
