import SteepestDescentOptimizationBounds.MomentumBounds

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/--
The vector identity behind Corollary 7 / Corollary 11:

`∇f(W_t) - C_t = β E_t + (1 - β) ξ_{S_t}`.
-/
lemma nesterovVector_eq
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.nesterovError t =
      S.beta • S.momentumError t + (1 - S.beta) • S.minibatchNoise t := by
  rw [S.minibatchNoise_eq_zero t]
  simp [StochasticSteepestDescentGeometryContext.nesterovError,
    StochasticSteepestDescentGeometryContext.C,
    StochasticSteepestDescentGeometryContext.momentumError,
    sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
  abel_nf

/-- Norm form of the Nesterov split used in Corollary 11. -/
theorem nesterovErrorNorm_le
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.nesterovErrorNorm t ≤
        S.beta * S.momentumErrorNorm t + (1 - S.beta) * S.minibatchNoiseNorm t := by
  intro t
  have hOneSubNonneg : 0 ≤ 1 - S.beta := sub_nonneg.mpr (le_of_lt S.beta_lt_one)
  calc
    S.nesterovErrorNorm t = ‖S.nesterovError t‖ := by
      simp [StochasticSteepestDescentGeometryContext.nesterovErrorNorm]
    _ = ‖S.beta • S.momentumError t + (1 - S.beta) • S.minibatchNoise t‖ := by
      rw [S.nesterovVector_eq]
    _ ≤ ‖S.beta • S.momentumError t‖ + ‖(1 - S.beta) • S.minibatchNoise t‖ := norm_add_le _ _
    _ = S.beta * S.momentumErrorNorm t + (1 - S.beta) * S.minibatchNoiseNorm t := by
      simp [StochasticSteepestDescentGeometryContext.momentumErrorNorm,
        StochasticSteepestDescentGeometryContext.minibatchNoiseNorm,
        norm_smul, Real.norm_of_nonneg S.beta_nonneg, Real.norm_of_nonneg hOneSubNonneg]

end StochasticSteepestDescentGeometryContext

section Corollary11

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem average_nesterovError_bound_of_pointwise
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (hCor11 :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta ^ (t + 1) * S.initialGradNorm
            + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
            + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t) / (T : ℝ) ≤
        (S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  intro T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  let k : ℝ :=
    (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
      + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ
  have hSum :
      Finset.sum (Finset.range T) (fun t => S.nesterovErrorNorm t) ≤
        Finset.sum (Finset.range T) (fun t =>
          S.beta ^ (t + 1) * S.initialGradNorm + k) := by
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
      Finset.sum (Finset.range T) (fun t => S.beta ^ (t + 1) * S.initialGradNorm) =
        shiftedGeometricPrefix S.beta T * S.initialGradNorm := by
    simp [shiftedGeometricPrefix, Finset.sum_mul]
  have hDiv := div_le_div_of_nonneg_right hSum hT'.le
  calc
    (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t) / (T : ℝ)
      ≤ (Finset.sum (Finset.range T) fun t =>
          S.beta ^ (t + 1) * S.initialGradNorm + k) / (T : ℝ) :=
        hDiv
    _ = ((shiftedGeometricPrefix S.beta T * S.initialGradNorm)
            + (T : ℝ) * k) / (T : ℝ) := by
            rw [Finset.sum_add_distrib, hGeom, hConst]
    _ = (shiftedGeometricPrefix S.beta T * S.initialGradNorm) / (T : ℝ) + k := by
          field_simp [show (T : ℝ) ≠ 0 by positivity]
    _ = (S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
          simp [k]
          ring

/--
Derives Corollary 11 from the Nesterov split, a Corollary-10-style momentum
bound, and a Lemma-5-style minibatch-noise bound.
-/
private theorem pointwiseNesterovErrorBound_of_momentum_and_minibatch_bounds
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (expectedMomentumError expectedMinibatchNoise : ℕ → ℝ)
    (hNesterovSplit :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta * expectedMomentumError t + (1 - S.beta) * expectedMinibatchNoise t)
    (hMomentum :
      ∀ t,
        expectedMomentumError t ≤
          S.beta ^ t * S.initialGradNorm
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta))
                * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ)
    (hMinibatch :
      ∀ t,
        expectedMinibatchNoise t ≤
          Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ) :
    ∀ t,
      S.nesterovErrorNorm t ≤
        S.beta ^ (t + 1) * S.initialGradNorm
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  intro t
  have hBetaLe : S.beta ≤ 1 := le_of_lt S.beta_lt_one
  set sqrtCoeff : ℝ := Real.sqrt ((1 - S.beta) / (1 + S.beta))
  set baseNoise : ℝ := S.sigma * Real.sqrt S.D / Real.sqrt S.batchSizeℝ
  have hBaseNoiseExpr :
      Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ = baseNoise := by
    simp [baseNoise]
    ring
  have hMomentumNoiseExpr :
      Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ =
        sqrtCoeff * baseNoise := by
    simp [sqrtCoeff, baseNoise]
    ring
  have hMomentum' :
      expectedMomentumError t ≤
        S.beta ^ t * S.initialGradNorm
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + sqrtCoeff * baseNoise := by
    have hMomentumRaw := hMomentum t
    rw [hMomentumNoiseExpr] at hMomentumRaw
    exact hMomentumRaw
  have hMinibatch' : expectedMinibatchNoise t ≤ baseNoise := by
    have hMinibatchRaw := hMinibatch t
    rw [hBaseNoiseExpr] at hMinibatchRaw
    exact hMinibatchRaw
  have hMomentumScaled :
      S.beta * expectedMomentumError t ≤
        S.beta *
          (S.beta ^ t * S.initialGradNorm
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + sqrtCoeff * baseNoise) := by
    exact mul_le_mul_of_nonneg_left hMomentum' S.beta_nonneg
  have hMinibatchScaled :
      (1 - S.beta) * expectedMinibatchNoise t ≤ (1 - S.beta) * baseNoise := by
    exact mul_le_mul_of_nonneg_left hMinibatch' (sub_nonneg.mpr hBetaLe)
  calc
    S.nesterovErrorNorm t
      ≤ S.beta * expectedMomentumError t + (1 - S.beta) * expectedMinibatchNoise t :=
        hNesterovSplit t
    _ ≤ S.beta *
          (S.beta ^ t * S.initialGradNorm
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + sqrtCoeff * baseNoise)
          + (1 - S.beta) * baseNoise := by
            linarith [hMomentumScaled, hMinibatchScaled]
    _ = S.beta ^ (t + 1) * S.initialGradNorm
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (sqrtCoeff * S.beta + (1 - S.beta)) * baseNoise := by
            rw [pow_succ']
            ring
    _ = S.beta ^ (t + 1) * S.initialGradNorm
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
            simp [sqrtCoeff, baseNoise, StochasticSteepestDescentGeometryContext.momentumNoisePrefactor]
            ring

/--
Combines Corollary 10 with a minibatch-noise bound to obtain Corollary 11.
-/
private theorem pointwiseNesterovErrorBound_of_corollary10_and_minibatch_bound
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (expectedMomentumError expectedMinibatchNoise : ℕ → ℝ)
    (hCor10 :
      ∀ t,
        expectedMomentumError t ≤
          S.beta ^ t * S.initialGradNorm
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta))
                * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ)
    (hNesterovSplit :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta * expectedMomentumError t + (1 - S.beta) * expectedMinibatchNoise t)
    (hMinibatch :
      ∀ t,
        expectedMinibatchNoise t ≤ Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ) :
    ∀ t,
      S.nesterovErrorNorm t ≤
        S.beta ^ (t + 1) * S.initialGradNorm
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  exact
    pointwiseNesterovErrorBound_of_momentum_and_minibatch_bounds
      S expectedMomentumError expectedMinibatchNoise hNesterovSplit hCor10 hMinibatch

/- Pointwise Nesterov-error bound on the canonical Nesterov-error sequence. -/
theorem Corollary11PointwiseNesterovErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.nesterovErrorNorm t ≤
        S.beta ^ (t + 1) * S.initialGradNorm
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  have hSplit :
      ∀ t,
        S.nesterovErrorNorm t ≤
          S.beta * S.momentumErrorNorm t + (1 - S.beta) * S.expectedMinibatchNoise t := by
    intro t
    have hNesterov := S.nesterovErrorNorm_le t
    have hScaled :
        (1 - S.beta) * S.minibatchNoiseNorm t ≤
          (1 - S.beta) * S.expectedMinibatchNoise t := by
      exact mul_le_mul_of_nonneg_left
        (S.minibatchNoiseNorm_le_expectedMinibatchNoise t)
        (sub_nonneg.mpr (le_of_lt S.beta_lt_one))
    linarith
  exact
    pointwiseNesterovErrorBound_of_corollary10_and_minibatch_bound
      S S.momentumErrorNorm S.expectedMinibatchNoise
      (Corollary10PointwiseMomentumErrorBound S)
      hSplit
      S.expectedMinibatchNoise_bound

/-- Averaged form of Corollary 11 over `t = 0, …, T - 1`. -/
theorem corollary11_average_nesterovError_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.nesterovErrorNorm t) / (T : ℝ) ≤
        (S.initialGradNorm * shiftedGeometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta ^ 2 / (1 - S.beta)) * S.L * S.eta
          + (S.momentumNoisePrefactor * Real.sqrt S.D * S.sigma) / Real.sqrt S.batchSizeℝ := by
  exact average_nesterovError_bound_of_pointwise
    S
    (Corollary11PointwiseNesterovErrorBound S)

end Corollary11

end

end SteepestDescentOptimizationBounds
