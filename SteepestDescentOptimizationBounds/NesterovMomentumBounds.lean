import SteepestDescentOptimizationBounds.MomentumBounds

open scoped BigOperators
open MeasureTheory

namespace SteepestDescentOptimizationBounds

/-!
Nesterov-residual layer for the realized stochastic steepest-descent model.

Upstream dependencies:

- `MomentumBounds.lean` provides the expected momentum-error bound and the
  scalar recurrence helpers.

Downstream use:

- `StarConvex.lean` and `FrankWolfe.lean` reuse the pathwise residual split.
- the expected-bound files reuse the expected Nesterov-residual bound and the
  momentum-noise prefactor.
-/

noncomputable section

namespace SteepestDescentPathGeometryContext

section PublicDefinitions

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The pathwise minibatch noise `∇f(W_t) - g_{S_t}`. -/
def minibatchNoise (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    StrongDual ℝ V :=
  S.grad t - S.minibatchGradient t

/-- The norm of the pathwise minibatch noise. -/
def minibatchNoiseNorm (S : SteepestDescentPathGeometryContext V) (t : ℕ) : ℝ :=
  ‖S.minibatchNoise t‖

/-- The pathwise momentum error `∇f(W_t) - M_t`. -/
def momentumError (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    StrongDual ℝ V :=
  S.grad t - S.momentum t

/-- The norm of the pathwise momentum error. -/
def momentumErrorNorm (S : SteepestDescentPathGeometryContext V) (t : ℕ) : ℝ :=
  ‖S.momentumError t‖

/-- The pathwise Nesterov residual `∇f(W_t) - C_t`. -/
def nesterovError (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    StrongDual ℝ V :=
  S.grad t - S.C t

/-- The norm of the pathwise Nesterov residual. -/
def nesterovErrorNorm (S : SteepestDescentPathGeometryContext V) (t : ℕ) : ℝ :=
  ‖S.nesterovError t‖

/-- The Corollary-11 momentum-noise prefactor. -/
def momentumNoisePrefactor (S : SteepestDescentPathGeometryContext V) : ℝ :=
  Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta + (1 - S.beta)

end PublicDefinitions

section PublicTheorems

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The vector identity behind the Nesterov split. -/
lemma nesterovError_split
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    S.nesterovError t =
      S.beta • S.momentumError t + (1 - S.beta) • S.minibatchNoise t := by
  rw [SteepestDescentPathGeometryContext.nesterovError, S.C_spec t]
  simp [SteepestDescentPathGeometryContext.momentumError,
    SteepestDescentPathGeometryContext.minibatchNoise,
    sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]

/-- The pathwise Nesterov residual norm is nonnegative. -/
lemma nesterovErrorNorm_nonneg (S : SteepestDescentPathGeometryContext V) (t : ℕ) :
    0 ≤ S.nesterovErrorNorm t :=
  norm_nonneg _

/-- Applying the pathwise Nesterov residual to a vector is bounded by its norm. -/
lemma nesterovError_apply_le
    (S : SteepestDescentPathGeometryContext V) (t : ℕ) (v : V) :
    |S.nesterovError t v| ≤ S.nesterovErrorNorm t * ‖v‖ := by
  simpa [SteepestDescentPathGeometryContext.nesterovErrorNorm] using
    (ContinuousLinearMap.le_opNorm (S.nesterovError t) v)

/-- The Corollary-11 prefactor is nonnegative. -/
lemma momentumNoisePrefactor_nonneg (S : SteepestDescentPathGeometryContext V) :
    0 ≤ S.momentumNoisePrefactor := by
  have hSqrtNonneg : 0 ≤ Real.sqrt ((1 - S.beta) / (1 + S.beta)) :=
    Real.sqrt_nonneg _
  have hTerm1 : 0 ≤ Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta :=
    mul_nonneg hSqrtNonneg S.beta_nonneg
  have hTerm2 : 0 ≤ 1 - S.beta := sub_nonneg.mpr (le_of_lt S.beta_lt_one)
  exact add_nonneg hTerm1 hTerm2

end PublicTheorems

end SteepestDescentPathGeometryContext

namespace StochasticSteepestDescentGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The realized Nesterov residual `∇f(W_t(ω)) - C_t(ω)`. -/
def nesterovError
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  S.grad t ω - S.C t ω

/-- The norm of the realized Nesterov residual. -/
def nesterovErrorNorm
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : ℝ :=
  ‖S.nesterovError t ω‖

/-- The expected Nesterov-residual norm at time `t`. -/
def expectedNesterovError
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, S.nesterovErrorNorm t ω ∂S.μ

/-- The Corollary-11 momentum-noise prefactor. -/
def momentumNoisePrefactor (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta + (1 - S.beta)

end PublicDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem average_nesterovError_bound_of_pointwise
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.expectedNesterovError t ≤
          S.beta ^ (t + 1) * S.expectedMomentumError 0
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.expectedNesterovError t) / (T : ℝ) ≤
        (S.expectedMomentumError 0 * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  intro T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  let k : ℝ :=
    (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
      + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ
  have hSum :
    Finset.sum (Finset.range T) (fun t => S.expectedNesterovError t) ≤
        Finset.sum (Finset.range T) (fun t =>
          S.beta ^ (t + 1) * S.expectedMomentumError 0 + k) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have hPoint := hCor11 t
    have hk : k =
        (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := rfl
    linarith
  have hConst :
      Finset.sum (Finset.range T) (fun _ => k) = (T : ℝ) * k := by
    simp
  have hGeom :
      Finset.sum (Finset.range T) (fun t => S.beta ^ (t + 1) * S.expectedMomentumError 0) =
        shiftedGeometricPrefix S.beta T * S.expectedMomentumError 0 := by
    simp [shiftedGeometricPrefix, Finset.sum_mul]
  have hDiv := div_le_div_of_nonneg_right hSum hT'.le
  calc
    (Finset.sum (Finset.range T) fun t => S.expectedNesterovError t) / (T : ℝ)
      ≤ (Finset.sum (Finset.range T) fun t =>
          S.beta ^ (t + 1) * S.expectedMomentumError 0 + k) / (T : ℝ) :=
        hDiv
    _ = ((shiftedGeometricPrefix S.beta T * S.expectedMomentumError 0)
            + (T : ℝ) * k) / (T : ℝ) := by
            rw [Finset.sum_add_distrib, hGeom, hConst]
    _ = ((shiftedGeometricPrefix S.beta T * S.expectedMomentumError 0) / (T : ℝ)) + k := by
          field_simp [show (T : ℝ) ≠ 0 by positivity]
    _ = (S.expectedMomentumError 0 * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
          simp [k]
          ring

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Pathwise Nesterov split after freezing a sample path. -/
lemma nesterovError_split
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.nesterovError t ω =
      S.beta • S.momentumError t ω + (1 - S.beta) • S.minibatchNoise t ω := by
  exact (S.path ω).nesterovError_split t

/-- The realized Nesterov residual norm is nonnegative. -/
lemma nesterovErrorNorm_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    0 ≤ S.nesterovErrorNorm t ω :=
  norm_nonneg _

/-- Applying the realized Nesterov residual to a vector is bounded by its norm. -/
lemma nesterovError_apply_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) (v : V) :
    |S.nesterovError t ω v| ≤ S.nesterovErrorNorm t ω * ‖v‖ := by
  simpa [StochasticSteepestDescentGeometryContext.nesterovErrorNorm] using
    (ContinuousLinearMap.le_opNorm (S.nesterovError t ω) v)

/-- The Corollary-11 prefactor is nonnegative. -/
lemma momentumNoisePrefactor_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) :
    0 ≤ S.momentumNoisePrefactor := by
  have hSqrtNonneg : 0 ≤ Real.sqrt ((1 - S.beta) / (1 + S.beta)) :=
    Real.sqrt_nonneg _
  have hTerm1 : 0 ≤ Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta :=
    mul_nonneg hSqrtNonneg S.beta_nonneg
  have hTerm2 : 0 ≤ 1 - S.beta := sub_nonneg.mpr (le_of_lt S.beta_lt_one)
  exact add_nonneg hTerm1 hTerm2

/-- Integrability bridge for the realized Nesterov-residual norm. -/
theorem nesterovErrorNorm_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, MeasureTheory.Integrable (fun ω => S.nesterovErrorNorm t ω) S.μ := by
  intro t
  have hMom : Integrable (fun ω => S.momentumErrorNorm t ω) S.μ :=
    S.momentumErrorNorm_integrable t
  have hNoise : Integrable (fun ω => S.minibatchNoiseNorm t ω) S.μ :=
    S.minibatchNoiseNorm_integrable t
  have hUpper :
      Integrable
        (fun ω =>
          S.beta * S.momentumErrorNorm t ω
            + (1 - S.beta) * S.minibatchNoiseNorm t ω) S.μ :=
    (hMom.const_mul S.beta).add (hNoise.const_mul (1 - S.beta))
  have hMeas :
      AEStronglyMeasurable (fun ω => S.nesterovErrorNorm t ω) S.μ := by
    exact
      (((S.grad_stronglyMeasurable t).sub
        ((S.C_measurable t).stronglyMeasurable)).norm.aestronglyMeasurable)
  refine Integrable.mono' hUpper hMeas ?_
  filter_upwards with ω
  have hPoint :
      S.nesterovErrorNorm t ω ≤
        S.beta * S.momentumErrorNorm t ω + (1 - S.beta) * S.minibatchNoiseNorm t ω := by
    calc
      S.nesterovErrorNorm t ω = ‖S.nesterovError t ω‖ := rfl
      _ = ‖S.beta • S.momentumError t ω + (1 - S.beta) • S.minibatchNoise t ω‖ := by
            rw [S.nesterovError_split t ω]
      _ ≤ ‖S.beta • S.momentumError t ω‖ + ‖(1 - S.beta) • S.minibatchNoise t ω‖ :=
            norm_add_le _ _
      _ = S.beta * S.momentumErrorNorm t ω + (1 - S.beta) * S.minibatchNoiseNorm t ω := by
            simp [StochasticSteepestDescentGeometryContext.momentumErrorNorm,
              StochasticSteepestDescentGeometryContext.minibatchNoiseNorm,
              norm_smul, Real.norm_of_nonneg S.beta_nonneg,
              Real.norm_of_nonneg S.one_sub_beta_pos.le]
  have hUpperNonneg :
      0 ≤ S.beta * S.momentumErrorNorm t ω + (1 - S.beta) * S.minibatchNoiseNorm t ω := by
    have hMomNonneg : 0 ≤ S.beta * S.momentumErrorNorm t ω := by
      exact mul_nonneg S.beta_nonneg (norm_nonneg _)
    have hNoiseNonneg : 0 ≤ (1 - S.beta) * S.minibatchNoiseNorm t ω := by
      exact mul_nonneg S.one_sub_beta_pos.le (norm_nonneg _)
    linarith
  simpa [Real.norm_of_nonneg (S.nesterovErrorNorm_nonneg t ω),
    Real.norm_of_nonneg hUpperNonneg] using hPoint

/-- Derived expected Nesterov-residual bound. -/
theorem nesterov_expectedErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedNesterovError t ≤
        S.beta ^ (t + 1) * S.expectedMomentumError 0
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  intro t
  let baseNoise : ℝ := Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ
  have hLower : Integrable (fun ω => S.nesterovErrorNorm t ω) S.μ :=
    S.nesterovErrorNorm_integrable t
  have hMomScaled :
      Integrable (fun ω => S.beta * S.momentumErrorNorm t ω) S.μ :=
    (S.momentumErrorNorm_integrable t).const_mul S.beta
  have hNoiseScaled :
      Integrable (fun ω => (1 - S.beta) * S.minibatchNoiseNorm t ω) S.μ :=
    (S.minibatchNoiseNorm_integrable t).const_mul (1 - S.beta)
  have hUpper :
      Integrable
        (fun ω =>
          S.beta * S.momentumErrorNorm t ω
            + (1 - S.beta) * S.minibatchNoiseNorm t ω) S.μ :=
    hMomScaled.add hNoiseScaled
  have hStep :
      S.expectedNesterovError t ≤
        S.beta * S.expectedMomentumError t + (1 - S.beta) * S.expectedMinibatchNoise t := by
    calc
      S.expectedNesterovError t
          = ∫ ω, S.nesterovErrorNorm t ω ∂S.μ := rfl
      _ ≤ ∫ ω,
            (S.beta * S.momentumErrorNorm t ω
              + (1 - S.beta) * S.minibatchNoiseNorm t ω) ∂S.μ := by
            refine MeasureTheory.integral_mono_ae hLower hUpper ?_
            filter_upwards with ω
            calc
              S.nesterovErrorNorm t ω = ‖S.nesterovError t ω‖ := rfl
              _ = ‖S.beta • S.momentumError t ω + (1 - S.beta) • S.minibatchNoise t ω‖ := by
                    rw [S.nesterovError_split t ω]
              _ ≤ ‖S.beta • S.momentumError t ω‖ + ‖(1 - S.beta) • S.minibatchNoise t ω‖ :=
                    norm_add_le _ _
              _ = S.beta * S.momentumErrorNorm t ω + (1 - S.beta) * S.minibatchNoiseNorm t ω := by
                    simp [StochasticSteepestDescentGeometryContext.momentumErrorNorm,
                      StochasticSteepestDescentGeometryContext.minibatchNoiseNorm,
                      norm_smul, Real.norm_of_nonneg S.beta_nonneg,
                      Real.norm_of_nonneg S.one_sub_beta_pos.le]
      _ = ∫ ω, S.beta * S.momentumErrorNorm t ω ∂S.μ
            + ∫ ω, (1 - S.beta) * S.minibatchNoiseNorm t ω ∂S.μ := by
              exact MeasureTheory.integral_add hMomScaled hNoiseScaled
      _ = S.beta * S.expectedMomentumError t + (1 - S.beta) * S.expectedMinibatchNoise t := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
            simp [StochasticSteepestDescentGeometryContext.expectedMomentumError,
              StochasticSteepestDescentGeometryContext.expectedMinibatchNoise]
  have hCor10 := S.Corollary10PointwiseMomentumErrorBound t
  have hCor10' :
      S.expectedMomentumError t ≤
        S.beta ^ t * S.expectedMomentumError 0
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * baseNoise := by
    have hBase :
        Real.sqrt ((1 - S.beta) / (1 + S.beta)) * baseNoise =
          Real.sqrt ((1 - S.beta) / (1 + S.beta))
            * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
      dsimp [baseNoise]
      ring
    rw [hBase]
    exact hCor10
  have hCor10Scaled :
      S.beta * S.expectedMomentumError t ≤
        S.beta * (
          S.beta ^ t * S.expectedMomentumError 0
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * baseNoise) := by
    exact mul_le_mul_of_nonneg_left hCor10' S.beta_nonneg
  have hNoiseBound :
      (1 - S.beta) * S.expectedMinibatchNoise t ≤ (1 - S.beta) * baseNoise := by
    exact mul_le_mul_of_nonneg_left (S.expectedMinibatchNoise_bound t) S.one_sub_beta_pos.le
  calc
    S.expectedNesterovError t
      ≤ S.beta * S.expectedMomentumError t + (1 - S.beta) * S.expectedMinibatchNoise t := hStep
    _ ≤ S.beta * (
          S.beta ^ t * S.expectedMomentumError 0
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * baseNoise)
          + (1 - S.beta) * baseNoise := by
            linarith
    _ = S.beta ^ (t + 1) * S.expectedMomentumError 0
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
            dsimp [baseNoise, StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            ring

/--
Expected Nesterov-residual bound derived from the momentum recursion and the
expected minibatch-noise bound.
-/
theorem Corollary11PointwiseNesterovErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedNesterovError t ≤
        S.beta ^ (t + 1) * S.expectedMomentumError 0
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  exact S.nesterov_expectedErrorBound

/-- Averaged expected Nesterov-residual bound over a finite horizon. -/
theorem corollary11_average_nesterovError_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.expectedNesterovError t) / (T : ℝ) ≤
        (S.expectedMomentumError 0 * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  exact average_nesterovError_bound_of_pointwise S (Corollary11PointwiseNesterovErrorBound S)

end PublicTheorems

end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
