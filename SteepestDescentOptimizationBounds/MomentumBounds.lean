import Mathlib
import SteepestDescentOptimizationBounds.MinibatchNoise
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace SteepestDescentOptimizationBounds

/-!
Momentum-error layer for the realized stochastic steepest-descent model.

Upstream dependencies:

- `MinibatchNoise.lean` supplies the realized minibatch-noise process and its
  expected norm bound.
- `WeightAndUpdateBounds.lean` supplies the pathwise update-size control used in
  the drift estimates.

Downstream use:

- `NesterovMomentumBounds.lean` reuses the expected momentum-residual bound and
  the scalar recurrence helpers.
- the expected-bound files reuse the expected momentum-error estimate.
-/

noncomputable section

section ScalarLemmas

/-- Partial geometric sum `1 + a + ... + a^(n-1)`. -/
def geometricPrefix (a : ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) (fun i => a ^ i)

/-- Shifted geometric sum `q + ... + q^T`. -/
def shiftedGeometricPrefix (q : ℝ) (T : ℕ) : ℝ :=
  Finset.sum (Finset.range T) (fun i => q ^ (i + 1))

/-- Extends `geometricPrefix` by one extra term. -/
lemma one_add_mul_geometricPrefix (a : ℝ) :
    ∀ n : ℕ, 1 + a * geometricPrefix a n = geometricPrefix a (n + 1)
  | n => by
      simpa [geometricPrefix, add_comm] using (geom_sum_succ (x := a) (n := n)).symm

/-- Rewrites the shifted sum as `q` times the unshifted geometric prefix. -/
lemma shifted_geometricPrefix_eq_mul (q : ℝ) (T : ℕ) :
    shiftedGeometricPrefix q T = q * geometricPrefix q T := by
  simp [shiftedGeometricPrefix, geometricPrefix, Finset.mul_sum, pow_succ']

/-- Extends the shifted geometric sum by one extra power. -/
lemma shiftedGeometricPrefix_succ (q : ℝ) (T : ℕ) :
    shiftedGeometricPrefix q (T + 1) = q + q * shiftedGeometricPrefix q T := by
  calc
    shiftedGeometricPrefix q (T + 1) = q * geometricPrefix q (T + 1) :=
      shifted_geometricPrefix_eq_mul q (T + 1)
    _ = q * (1 + q * geometricPrefix q T) := by
      rw [one_add_mul_geometricPrefix]
    _ = q + q * shiftedGeometricPrefix q T := by
      rw [shifted_geometricPrefix_eq_mul]
      ring

/-- Uniform bound on a finite geometric sum when `0 ≤ a < 1`. -/
lemma geometricPrefix_le_inv_sub (a : ℝ) (haNonneg : 0 ≤ a) (haLtOne : a < 1) (T : ℕ) :
    geometricPrefix a T ≤ 1 / (1 - a) := by
  by_cases hZero : a = 0
  · subst hZero
    by_cases hT : T = 0
    · simp [geometricPrefix, hT]
    · simp [geometricPrefix, hT]
  · have hFormula : geometricPrefix a T = (a ^ T - 1) / (a - 1) := by
      simpa [geometricPrefix] using (geom_sum_eq (x := a) (by linarith : a ≠ 1) T)
    have hRewrite : (a ^ T - 1) / (a - 1) = (1 - a ^ T) / (1 - a) := by
      have hNum : a ^ T - 1 = -(1 - a ^ T) := by ring
      have hDen : a - 1 = -(1 - a) := by ring
      rw [hNum, hDen, neg_div_neg_eq]
    have hPowNonneg : 0 ≤ a ^ T := by positivity
    have hNumLe : 1 - a ^ T ≤ 1 := by nlinarith
    have hDenPos : 0 < 1 - a := sub_pos.mpr haLtOne
    rw [hFormula, hRewrite]
    exact div_le_div_of_nonneg_right hNumLe hDenPos.le

/-- Uniform bound on the shifted geometric sum when `0 ≤ q < 1`. -/
lemma shifted_geometricPrefix_le (q : ℝ) (hqNonneg : 0 ≤ q) (hqLtOne : q < 1) (T : ℕ) :
    shiftedGeometricPrefix q T ≤ q / (1 - q) := by
  calc
    shiftedGeometricPrefix q T = q * geometricPrefix q T := shifted_geometricPrefix_eq_mul q T
    _ ≤ q * (1 / (1 - q)) := by
      gcongr
      exact geometricPrefix_le_inv_sub q hqNonneg hqLtOne T
    _ = q / (1 - q) := by
      field_simp [sub_ne_zero.mpr (ne_of_lt hqLtOne)]

/--
Unrolls a scalar recurrence of the form
`u_{t+1} ≤ a u_t + k + d q^(t+1)`.
-/
lemma recurrence_unroll
    {u : ℕ → ℝ} {a k d q : ℝ}
    (haNonneg : 0 ≤ a) (haLeOne : a ≤ 1)
    (hqNonneg : 0 ≤ q) (hkNonneg : 0 ≤ k) (hdNonneg : 0 ≤ d)
    (hRec : ∀ t, u (t + 1) ≤ a * u t + k + d * q ^ (t + 1)) :
    ∀ T,
      u T ≤
        a ^ T * u 0
          + k * geometricPrefix a T
          + d * shiftedGeometricPrefix q T
  | 0 => by
      simp [geometricPrefix, shiftedGeometricPrefix]
  | T + 1 => by
      have hIH := recurrence_unroll haNonneg haLeOne hqNonneg hkNonneg hdNonneg hRec T
      have hQSumNonneg : 0 ≤ shiftedGeometricPrefix q T := by
        simpa [shiftedGeometricPrefix] using
          (Finset.sum_nonneg fun i _ => pow_nonneg hqNonneg _)
      calc
        u (T + 1) ≤ a * u T + k + d * q ^ (T + 1) := hRec T
        _ ≤ a * (a ^ T * u 0 + k * geometricPrefix a T
              + d * shiftedGeometricPrefix q T) + k + d * q ^ (T + 1) := by
                gcongr
        _ = a ^ (T + 1) * u 0
              + k * (1 + a * geometricPrefix a T)
              + (a * (d * shiftedGeometricPrefix q T) + d * q ^ (T + 1)) := by
                ring
        _ ≤ a ^ (T + 1) * u 0
              + k * (1 + a * geometricPrefix a T)
              + (d * shiftedGeometricPrefix q T + d * q ^ (T + 1)) := by
                have hAux : a * (d * shiftedGeometricPrefix q T)
                    ≤ d * shiftedGeometricPrefix q T := by
                  have hDD : 0 ≤ d * shiftedGeometricPrefix q T := by
                    exact mul_nonneg hdNonneg hQSumNonneg
                  nlinarith
                linarith
        _ = a ^ (T + 1) * u 0
              + k * geometricPrefix a (T + 1)
              + d * shiftedGeometricPrefix q (T + 1) := by
                rw [one_add_mul_geometricPrefix]
                simp [shiftedGeometricPrefix, geometricPrefix, Finset.sum_range_succ]
                ring

/--
Averaging helper: if `u t ≤ g t + k` pointwise and the finite sum of `g`
collapses to `main T`, then the time average of `u` is bounded by the average
of `main` plus the constant offset `k`.
-/
lemma average_bound_of_pointwise_const
    {u g : ℕ → ℝ} {main : ℕ → ℝ} {k : ℝ}
    (hPoint : ∀ t, u t ≤ g t + k)
    (hMain : ∀ T, Finset.sum (Finset.range T) g = main T) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) u) / (T : ℝ) ≤ main T / (T : ℝ) + k := by
  intro T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hSum :
      Finset.sum (Finset.range T) u ≤ Finset.sum (Finset.range T) (fun t => g t + k) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    exact hPoint t
  have hConst : Finset.sum (Finset.range T) (fun _ => k) = (T : ℝ) * k := by
    simp
  have hDiv := div_le_div_of_nonneg_right hSum hT'.le
  calc
    (Finset.sum (Finset.range T) u) / (T : ℝ)
      ≤ (Finset.sum (Finset.range T) (fun t => g t + k)) / (T : ℝ) := hDiv
    _ = (main T + (T : ℝ) * k) / (T : ℝ) := by
          rw [Finset.sum_add_distrib, hMain T, hConst]
    _ = main T / (T : ℝ) + k := by
          field_simp [show (T : ℝ) ≠ 0 by positivity]

end ScalarLemmas

namespace StochasticSteepestDescentGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-- The realized momentum error `E_t(ω) = ∇f(W_t(ω)) - M_t(ω)`. -/
def momentumError
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  S.grad t ω - S.momentum t ω

/-- The norm of the realized momentum error. -/
def momentumErrorNorm
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : ℝ :=
  ‖S.momentumError t ω‖

/-- The expected momentum-error norm at time `t`. -/
def expectedMomentumError
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, S.momentumErrorNorm t ω ∂S.μ

/-- The initial expected momentum-error norm. -/
def initialExpectedMomentumError
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.expectedMomentumError 0

end PublicDefinitions

section PrivateDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

private def driftComponent
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℕ → Ω → StrongDual ℝ V
  | 0 => S.momentumError 0
  | t + 1 => fun ω =>
      S.beta • S.driftComponent t ω + S.beta • (S.grad (t + 1) ω - S.grad t ω)

private def momentumNoiseProcess
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℕ → Ω → StrongDual ℝ V
  | 0 => 0
  | t + 1 => fun ω =>
      S.beta • S.momentumNoiseProcess t ω + (1 - S.beta) • S.minibatchNoise (t + 1) ω

private def expectedNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, ‖S.momentumNoiseProcess t ω‖ ∂S.μ

private def flatTimeIndex
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) : ℕ :=
  m / S.batchSize + 1

private def flatSampleSlot
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) : Fin S.batchSize :=
  ⟨m % S.batchSize, Nat.mod_lt _ S.batchSize_pos⟩

private def flatCoeff
    (S : StochasticSteepestDescentGeometryContext Ω V) (t m : ℕ) : ℝ :=
  ((1 - S.beta) * S.beta ^ (t - 1 - m / S.batchSize)) / S.batchSizeℝ

private def flatNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    Ω → StrongDual ℝ V :=
  S.ξ (S.flatTimeIndex m) (S.flatSampleSlot m)

private def flatPastSigma
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    MeasurableSpace Ω :=
  samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample
    (S.flatTimeIndex m) (S.flatSampleSlot m)

private def flatPartialSum
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t k : ℕ) (ω : Ω) : StrongDual ℝ V :=
  weightedPartialSum (S.flatCoeff t) S.flatNoise k ω

end PrivateDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

private theorem grad_increment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    ‖S.grad (t + 1) ω - S.grad t ω‖ ≤ 2 * S.L * S.eta := by
  have hWeight : ‖S.W t ω‖ ≤ S.constraintRadius :=
    (S.proposition9_weight_and_update_bounds t ω).1
  have hWeightNext : ‖S.W (t + 1) ω‖ ≤ S.constraintRadius :=
    (S.proposition9_weight_and_update_bounds (t + 1) ω).1
  have hLocal :
      ‖S.grad (t + 1) ω - S.grad t ω‖ ≤
        S.L * ‖S.W (t + 1) ω - S.W t ω‖ := by
    simpa [StochasticSteepestDescentGeometryContext.grad] using
      (S.assumption3_fLocalSmoothness.bound hWeight hWeightNext)
  calc
    ‖S.grad (t + 1) ω - S.grad t ω‖
      ≤ S.L * ‖S.W (t + 1) ω - S.W t ω‖ := hLocal
    _ ≤ S.L * (2 * S.eta) := by
          gcongr
          exact S.L_pos.le
          exact (S.proposition9_weight_and_update_bounds t ω).2
    _ = 2 * S.L * S.eta := by ring

private theorem momentumError_split_step
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.momentumError (t + 1) ω =
      S.beta • S.momentumError t ω
        + S.beta • (S.grad (t + 1) ω - S.grad t ω)
        + (1 - S.beta) • S.minibatchNoise (t + 1) ω := by
  rw [StochasticSteepestDescentGeometryContext.momentumError,
    StochasticSteepestDescentGeometryContext.momentumError,
    S.momentum_succ]
  simp [StochasticSteepestDescentGeometryContext.minibatchNoise, sub_eq_add_neg,
    add_smul, smul_add, add_assoc, add_left_comm, add_comm]

private theorem flatActualIndex_eq
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    SteepestDescentOptimizationBounds.flatSampleIndex
        (S.flatTimeIndex m) (S.flatSampleSlot m)
      = m + S.batchSize := by
  unfold SteepestDescentOptimizationBounds.flatSampleIndex flatTimeIndex flatSampleSlot
  rw [Nat.add_mul, Nat.one_mul]
  calc
    (m / S.batchSize) * S.batchSize + S.batchSize + (m % S.batchSize)
      = S.batchSize + (m % S.batchSize + S.batchSize * (m / S.batchSize)) := by
          ac_rfl
    _ = S.batchSize + m := by rw [Nat.mod_add_div, Nat.add_comm]
    _ = m + S.batchSize := by ac_rfl

private theorem last_block_div
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    (t * S.batchSize + i) / S.batchSize = t := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ S.batchSize_pos]
  rw [Nat.div_eq_of_lt hi]
  simp

private theorem last_block_mod
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    (t * S.batchSize + i) % S.batchSize = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

private theorem last_block_flatTimeIndex
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    S.flatTimeIndex (t * S.batchSize + i) = t + 1 := by
  simp [flatTimeIndex, S.last_block_div t i hi]

private theorem last_block_flatSampleSlot
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    S.flatSampleSlot (t * S.batchSize + i) = ⟨i, hi⟩ := by
  apply Fin.ext
  simp [flatSampleSlot, S.last_block_mod t i hi]

private theorem flatCoeff_last_block
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    S.flatCoeff (t + 1) (t * S.batchSize + i) = (1 - S.beta) / S.batchSizeℝ := by
  dsimp [flatCoeff]
  rw [S.last_block_div t i hi]
  norm_num

private theorem flatPastSigma_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    S.flatPastSigma m ≤ inferInstanceAs (MeasurableSpace Ω) := by
  simpa [flatPastSigma] using
    S.samplePrefixSigma_le (S.flatTimeIndex m) (S.flatSampleSlot m)

private theorem flatSample_measurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {j m : ℕ} (hj : j < m) :
    Measurable[S.flatPastSigma m]
      (fun ω => S.stochasticGradientSample (S.flatTimeIndex j) (S.flatSampleSlot j) ω) := by
  have hActualLt :
      SteepestDescentOptimizationBounds.flatSampleIndex
          (S.flatTimeIndex j) (S.flatSampleSlot j)
        <
      SteepestDescentOptimizationBounds.flatSampleIndex
          (S.flatTimeIndex m) (S.flatSampleSlot m) := by
    rw [S.flatActualIndex_eq j, S.flatActualIndex_eq m]
    exact Nat.add_lt_add_right hj S.batchSize
  have hMeas :
      Measurable[S.flatPastSigma m]
        (flatSample S.batchSize_pos S.stochasticGradientSample
          (SteepestDescentOptimizationBounds.flatSampleIndex
            (S.flatTimeIndex j) (S.flatSampleSlot j))) := by
    simpa [flatPastSigma] using
      (flatSample_measurable_of_lt
        S.batchSize_pos S.W S.stochasticGradientSample
        (t := S.flatTimeIndex m) (i := S.flatSampleSlot m) hActualLt)
  simpa [flatSample_at_flatSampleIndex
      S.batchSize_pos S.stochasticGradientSample
      (S.flatTimeIndex j) (S.flatSampleSlot j)] using hMeas

private theorem flatNoise_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    StronglyMeasurable (S.flatNoise m) := by
  simpa [flatNoise, StochasticSteepestDescentGeometryContext.ξ] using
    ((S.grad_stronglyMeasurable (S.flatTimeIndex m)).sub
      (S.sample_stronglyMeasurable (S.flatTimeIndex m) (S.flatSampleSlot m)))

private theorem flatNoise_condexp_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    S.μ[S.flatNoise m | S.flatPastSigma m] =ᵐ[S.μ] 0 := by
  simpa [flatNoise, flatPastSigma] using
    (S.ξ_condexp_eq_zero_of_prefix (S.flatTimeIndex m) (S.flatSampleSlot m))

private theorem flatNoise_norm_le_noiseRadius_ae
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    ∀ᵐ ω ∂S.μ, ‖S.flatNoise m ω‖ ≤ S.noiseRadius := by
  simpa [flatNoise] using
    (S.sample_norm_le_noiseRadius_ae (S.flatTimeIndex m) (S.flatSampleSlot m))

private theorem flatNoise_second_moment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    Integrable (fun ω => ‖S.flatNoise m ω‖ ^ 2) S.μ ∧
      ∫ ω, ‖S.flatNoise m ω‖ ^ 2 ∂S.μ ≤ S.sigma ^ 2 := by
  simpa [flatNoise] using
    (S.second_moment_bound (S.flatTimeIndex m) (S.flatSampleSlot m))

private theorem flatNoise_prefixStronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {j m : ℕ} (hj : j < m) :
    StronglyMeasurable[S.flatPastSigma m] (S.flatNoise j) := by
  have hTimeLe : S.flatTimeIndex j ≤ S.flatTimeIndex m := by
    dsimp [flatTimeIndex]
    exact Nat.succ_le_succ (Nat.div_le_div_right (Nat.le_of_lt hj))
  have hGrad :
      StronglyMeasurable[S.flatPastSigma m]
        (fun ω => S.grad (S.flatTimeIndex j) ω) := by
    simpa [flatPastSigma] using
      (S.grad_prefixStronglyMeasurable
        (S.flatTimeIndex m) (S.flatSampleSlot m) (S.flatTimeIndex j) hTimeLe)
  have hSample :
      StronglyMeasurable[S.flatPastSigma m]
        (fun ω => S.stochasticGradientSample (S.flatTimeIndex j) (S.flatSampleSlot j) ω) := by
    exact (S.flatSample_measurable_before hj).stronglyMeasurable
  simpa [flatNoise, StochasticSteepestDescentGeometryContext.ξ] using hGrad.sub hSample

private theorem flatPartialSum_stronglyMeasurable_at
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t m : ℕ) :
    ∀ k, k ≤ m →
      StronglyMeasurable[S.flatPastSigma m]
        (fun ω => weightedPartialSum (S.flatCoeff t) S.flatNoise k ω)
  | 0, hk => by
      simpa [weightedPartialSum] using
        (stronglyMeasurable_const :
          StronglyMeasurable[S.flatPastSigma m]
            (fun _ : Ω => (0 : StrongDual ℝ V)))
  | k + 1, hk => by
      have hklt : k < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hPrev :=
        S.flatPartialSum_stronglyMeasurable_at t m k (Nat.le_of_lt hklt)
      have hCurr :
          StronglyMeasurable[S.flatPastSigma m]
            (fun ω => S.flatCoeff t k • S.flatNoise k ω) := by
        simpa using (S.flatNoise_prefixStronglyMeasurable hklt).const_smul (S.flatCoeff t k)
      convert hPrev.add hCurr using 1
      ext ω
      simp [weightedPartialSum, Finset.sum_range_succ, add_comm]

private theorem flatCoeff_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t m : ℕ) :
    0 ≤ S.flatCoeff t m := by
  have hOneSubNonneg : 0 ≤ 1 - S.beta := sub_nonneg.mpr (le_of_lt S.beta_lt_one)
  have hPowNonneg : 0 ≤ S.beta ^ (t - 1 - m / S.batchSize) := by
    exact pow_nonneg S.beta_nonneg _
  exact div_nonneg (mul_nonneg hOneSubNonneg hPowNonneg) S.batchSizeℝ_pos.le

private theorem flatCoeff_succ_eq_beta_mul
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {t m : ℕ} (hm : m < t * S.batchSize) :
    S.flatCoeff (t + 1) m = S.beta * S.flatCoeff t m := by
  have hDivLt : m / S.batchSize < t := by
    exact (Nat.div_lt_iff_lt_mul S.batchSize_pos).2 hm
  have hExp : t - m / S.batchSize = (t - 1 - m / S.batchSize) + 1 := by
    omega
  dsimp [flatCoeff]
  rw [hExp, pow_succ']
  field_simp [S.batchSizeℝ_ne_zero]

private theorem flatCoeff_sum_eq
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      Finset.sum (Finset.range (t * S.batchSize)) (fun m => S.flatCoeff t m) =
        1 - S.beta ^ t
  | 0 => by simp [flatCoeff]
  | t + 1 => by
      have hSplit :
          Finset.sum (Finset.range ((t + 1) * S.batchSize))
              (fun m => S.flatCoeff (t + 1) m) =
            Finset.sum (Finset.range (t * S.batchSize))
                (fun m => S.flatCoeff (t + 1) m)
              + Finset.sum (Finset.range S.batchSize)
                  (fun i => S.flatCoeff (t + 1) (t * S.batchSize + i)) := by
        rw [Nat.succ_mul, Finset.sum_range_add]
      have hFirst :
          Finset.sum (Finset.range (t * S.batchSize))
              (fun m => S.flatCoeff (t + 1) m) =
            S.beta * Finset.sum (Finset.range (t * S.batchSize))
              (fun m => S.flatCoeff t m) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [S.flatCoeff_succ_eq_beta_mul (Finset.mem_range.mp hm)]
      have hLast :
          Finset.sum (Finset.range S.batchSize)
              (fun i => S.flatCoeff (t + 1) (t * S.batchSize + i)) =
            1 - S.beta := by
        calc
          Finset.sum (Finset.range S.batchSize)
              (fun i => S.flatCoeff (t + 1) (t * S.batchSize + i))
            = Finset.sum (Finset.range S.batchSize)
                (fun _ => (1 - S.beta) / S.batchSizeℝ) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  exact S.flatCoeff_last_block t i (Finset.mem_range.mp hi)
          _ = S.batchSizeℝ * ((1 - S.beta) / S.batchSizeℝ) := by
                simp [StochasticSteepestDescentParameters.batchSizeℝ]
          _ = 1 - S.beta := by
                field_simp [S.batchSizeℝ_ne_zero]
      calc
        Finset.sum (Finset.range ((t + 1) * S.batchSize)) (fun m => S.flatCoeff (t + 1) m)
          = Finset.sum (Finset.range (t * S.batchSize))
                (fun m => S.flatCoeff (t + 1) m)
              + Finset.sum (Finset.range S.batchSize)
                  (fun i => S.flatCoeff (t + 1) (t * S.batchSize + i)) := hSplit
        _ = S.beta * Finset.sum (Finset.range (t * S.batchSize))
              (fun m => S.flatCoeff t m) + (1 - S.beta) := by
                rw [hFirst, hLast]
        _ = S.beta * (1 - S.beta ^ t) + (1 - S.beta) := by
              rw [S.flatCoeff_sum_eq t]
        _ = 1 - S.beta ^ (t + 1) := by
              rw [pow_succ']
              ring

private theorem flatCoeff_sum_le_one
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    Finset.sum (Finset.range (t * S.batchSize)) (fun m => S.flatCoeff t m) ≤ 1 := by
  rw [S.flatCoeff_sum_eq t]
  have hPowNonneg : 0 ≤ S.beta ^ t := by
    exact pow_nonneg S.beta_nonneg _
  linarith

private theorem flatCoeff_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ∀ k, k < t * S.batchSize →
      AEStronglyMeasurable[S.flatPastSigma k]
        (fun ω =>
          S.assumption4_localProxyPotential.mirrorLinear
            (weightedPartialSum (S.flatCoeff t) S.flatNoise k ω)) S.μ
  | k, hk => by
      have hPartial :
          StronglyMeasurable[S.flatPastSigma k]
            (fun ω => weightedPartialSum (S.flatCoeff t) S.flatNoise k ω) :=
        S.flatPartialSum_stronglyMeasurable_at t k k le_rfl
      have hCoeffSumLeOne :
          Finset.sum (Finset.range k) (fun m => S.flatCoeff t m) ≤ 1 := by
        refine
          (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.le_of_lt hk)) ?_).trans (S.flatCoeff_sum_le_one t)
        intro m _ _
        exact S.flatCoeff_nonneg t m
      have hPartialBound :
          ∀ᵐ ω ∂S.μ, ‖weightedPartialSum (S.flatCoeff t) S.flatNoise k ω‖ ≤ S.noiseRadius :=
        weightedPartialSum_norm_le_noiseRadius_ae
          S.assumption4_localProxyPotential
          (μ := S.μ)
          (ξ := S.flatNoise)
          (α := S.flatCoeff t)
          (n := k)
          (coeff_nonneg := by intro i hi; exact S.flatCoeff_nonneg t i)
          (coeff_sum_le_one := hCoeffSumLeOne)
          (sample_norm_le_noiseRadius_ae := by
            intro i hi
            exact S.flatNoise_norm_le_noiseRadius_ae i)
          k le_rfl
      have hMirror :
          AEStronglyMeasurable[S.flatPastSigma k]
            (fun ω => S.mirrorMap (weightedPartialSum (S.flatCoeff t) S.flatNoise k ω)) S.μ :=
        Assumption4_LocalSmoothProxyPotential.mirrorMap_comp_aestronglyMeasurable_of_mem_noiseBall_ae
          (V := V) (Ω := Ω) S.assumption4_localProxyPotential
          (m := S.flatPastSigma k) (μ := S.μ)
          hPartial.aestronglyMeasurable hPartialBound
      exact (strongDualBidual V).continuous.comp_aestronglyMeasurable hMirror

private theorem momentumNoiseProcess_eq_flatPartialSum
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.momentumNoiseProcess t = S.flatPartialSum t (t * S.batchSize)
  | 0 => by
      funext ω
      simp [momentumNoiseProcess, flatPartialSum, weightedPartialSum]
  | t + 1 => by
      funext ω
      have hSplit :
          S.flatPartialSum (t + 1) ((t + 1) * S.batchSize) ω =
            Finset.sum (Finset.range (t * S.batchSize))
                (fun m => S.flatCoeff (t + 1) m • S.flatNoise m ω)
              + Finset.sum (Finset.range S.batchSize)
                  (fun i =>
                    S.flatCoeff (t + 1) (t * S.batchSize + i) •
                      S.flatNoise (t * S.batchSize + i) ω) := by
        simp [flatPartialSum, weightedPartialSum, Nat.succ_mul, Finset.sum_range_add]
      have hFirst :
          Finset.sum (Finset.range (t * S.batchSize))
              (fun m => S.flatCoeff (t + 1) m • S.flatNoise m ω) =
            S.beta • S.flatPartialSum t (t * S.batchSize) ω := by
        rw [flatPartialSum, weightedPartialSum, Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [S.flatCoeff_succ_eq_beta_mul (Finset.mem_range.mp hm), smul_smul]
      have hLast :
          Finset.sum (Finset.range S.batchSize)
              (fun i =>
                S.flatCoeff (t + 1) (t * S.batchSize + i) •
                  S.flatNoise (t * S.batchSize + i) ω) =
            (1 - S.beta) • S.minibatchNoise (t + 1) ω := by
        calc
          Finset.sum (Finset.range S.batchSize)
              (fun i =>
                S.flatCoeff (t + 1) (t * S.batchSize + i) •
                  S.flatNoise (t * S.batchSize + i) ω)
            = Finset.sum (Finset.range S.batchSize)
                (fun i =>
                  (1 - S.beta) •
                    (uniformBatchWeight S.batchSize •
                      (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ ω else 0))) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hiLt : i < S.batchSize := Finset.mem_range.mp hi
                    have hScalar :
                        S.flatCoeff (t + 1) (t * S.batchSize + i) =
                          (1 - S.beta) / S.batchSizeℝ := by
                      exact S.flatCoeff_last_block t i hiLt
                    have hNoise :
                        S.flatNoise (t * S.batchSize + i) ω = S.ξ (t + 1) ⟨i, hiLt⟩ ω := by
                      simp [flatNoise, S.last_block_flatTimeIndex t i hiLt,
                        S.last_block_flatSampleSlot t i hiLt]
                    have hIf :
                        (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ ω else 0) =
                          S.ξ (t + 1) ⟨i, hiLt⟩ ω := by
                      simp [hiLt]
                    rw [hScalar, hNoise, hIf, smul_smul]
                    rw [uniformBatchWeight]
                    congr 1
                    simp [StochasticSteepestDescentParameters.batchSizeℝ, div_eq_mul_inv]
          _ = (1 - S.beta) •
                Finset.sum (Finset.range S.batchSize)
                  (fun i =>
                    uniformBatchWeight S.batchSize •
                      (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ ω else 0)) := by
                    rw [Finset.smul_sum]
          _ = (1 - S.beta) •
                Finset.sum Finset.univ
                  (fun i : Fin S.batchSize =>
                    uniformBatchWeight S.batchSize • S.ξ (t + 1) i ω) := by
                      congr 1
                      symm
                      simpa using
                        (Fin.sum_univ_eq_sum_range (n := S.batchSize)
                          (fun i =>
                            uniformBatchWeight S.batchSize •
                              (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ ω else 0)))
          _ = (1 - S.beta) • S.minibatchNoise (t + 1) ω := by
                rw [S.minibatchNoise_eq_sum_range (t + 1) ω]
      calc
        S.momentumNoiseProcess (t + 1) ω
          = S.beta • S.momentumNoiseProcess t ω
              + (1 - S.beta) • S.minibatchNoise (t + 1) ω := by
                rw [momentumNoiseProcess]
        _ = S.beta • S.flatPartialSum t (t * S.batchSize) ω
              + (1 - S.beta) • S.minibatchNoise (t + 1) ω := by
                rw [S.momentumNoiseProcess_eq_flatPartialSum t]
        _ = S.flatPartialSum (t + 1) ((t + 1) * S.batchSize) ω := by
                rw [hSplit, hFirst, hLast]

private theorem flatWeightedNoise_analysis
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    Integrable (fun ω => ‖S.flatPartialSum t (t * S.batchSize) ω‖) S.μ ∧
      ∫ ω, ‖S.flatPartialSum t (t * S.batchSize) ω‖ ∂S.μ ≤
        Real.sqrt
          (S.D * S.sigma ^ 2
            * Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2)) := by
  letI := S.prob
  refine ⟨?_, ?_⟩
  · exact
      weighted_noise_norm_integrable
        S.assumption4_localProxyPotential
        (μ := S.μ)
        (sigma := S.sigma)
        (ξ := S.flatNoise)
        (α := S.flatCoeff t)
        (n := t * S.batchSize)
        (pastSigma := S.flatPastSigma)
        (pastSigma_le := S.flatPastSigma_le)
        (coeff_nonneg := by intro i hi; exact S.flatCoeff_nonneg t i)
        (coeff_sum_le_one := S.flatCoeff_sum_le_one t)
        (sample_stronglyMeasurable := fun i => S.flatNoise_stronglyMeasurable i)
        (coeff_measurable := by intro i hi; exact S.flatCoeff_measurable t i hi)
        (cond_zero := by intro i hi; exact S.flatNoise_condexp_zero i)
        (sample_norm_le_noiseRadius_ae := by intro i hi; exact S.flatNoise_norm_le_noiseRadius_ae i)
        (second_moment_bound := by intro i hi; exact S.flatNoise_second_moment_bound i)
  · exact
      weighted_noise_first_moment_bound
        S.assumption4_localProxyPotential
        (μ := S.μ)
        (sigma := S.sigma)
        (ξ := S.flatNoise)
        (α := S.flatCoeff t)
        (n := t * S.batchSize)
        (pastSigma := S.flatPastSigma)
        (pastSigma_le := S.flatPastSigma_le)
        (coeff_nonneg := by intro i hi; exact S.flatCoeff_nonneg t i)
        (coeff_sum_le_one := S.flatCoeff_sum_le_one t)
        (sample_stronglyMeasurable := fun i => S.flatNoise_stronglyMeasurable i)
        (coeff_measurable := by intro i hi; exact S.flatCoeff_measurable t i hi)
        (cond_zero := by intro i hi; exact S.flatNoise_condexp_zero i)
        (sample_norm_le_noiseRadius_ae := by intro i hi; exact S.flatNoise_norm_le_noiseRadius_ae i)
        (second_moment_bound := by intro i hi; exact S.flatNoise_second_moment_bound i)

private theorem momentumNoiseProcess_norm_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Integrable (fun ω => ‖S.momentumNoiseProcess t ω‖) S.μ := by
  intro t
  have hInt := (S.flatWeightedNoise_analysis t).1
  refine hInt.congr ?_
  filter_upwards with ω
  rw [S.momentumNoiseProcess_eq_flatPartialSum t]

private theorem flatCoeff_sq_sum_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      Finset.sum (Finset.range (t * S.batchSize))
          (fun m => (S.flatCoeff t m) ^ 2) ≤
        ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ
  | 0 => by
      have hRatioNonneg : 0 ≤ ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ := by
        exact div_nonneg S.one_sub_div_one_add_nonneg S.batchSizeℝ_pos.le
      simpa using hRatioNonneg
  | t + 1 => by
      have hIH := S.flatCoeff_sq_sum_bound t
      have hSplit :
          Finset.sum (Finset.range ((t + 1) * S.batchSize))
              (fun m => (S.flatCoeff (t + 1) m) ^ 2) =
            Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff (t + 1) m) ^ 2)
              + Finset.sum (Finset.range S.batchSize)
                  (fun i => (S.flatCoeff (t + 1) (t * S.batchSize + i)) ^ 2) := by
        rw [Nat.succ_mul, Finset.sum_range_add]
      have hFirst :
          Finset.sum (Finset.range (t * S.batchSize))
              (fun m => (S.flatCoeff (t + 1) m) ^ 2) =
            S.beta ^ 2 *
              Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [S.flatCoeff_succ_eq_beta_mul (Finset.mem_range.mp hm)]
        ring
      have hLast :
          Finset.sum (Finset.range S.batchSize)
              (fun i => (S.flatCoeff (t + 1) (t * S.batchSize + i)) ^ 2) =
            (1 - S.beta) ^ 2 / S.batchSizeℝ := by
        calc
          Finset.sum (Finset.range S.batchSize)
              (fun i => (S.flatCoeff (t + 1) (t * S.batchSize + i)) ^ 2)
            = Finset.sum (Finset.range S.batchSize)
                (fun _ => (((1 - S.beta) / S.batchSizeℝ) ^ 2)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [S.flatCoeff_last_block t i (Finset.mem_range.mp hi)]
          _ = S.batchSizeℝ * (((1 - S.beta) / S.batchSizeℝ) ^ 2) := by
                simp [StochasticSteepestDescentParameters.batchSizeℝ]
          _ = (1 - S.beta) ^ 2 / S.batchSizeℝ := by
                field_simp [S.batchSizeℝ_ne_zero]
      have hMain :
          S.beta ^ 2 *
              Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2)
            + (1 - S.beta) ^ 2 / S.batchSizeℝ
          ≤ S.beta ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)
            + (1 - S.beta) ^ 2 / S.batchSizeℝ := by
        gcongr
      have hOneAddNe : 1 + S.beta ≠ 0 := by linarith [S.beta_nonneg]
      calc
        Finset.sum (Finset.range ((t + 1) * S.batchSize))
            (fun m => (S.flatCoeff (t + 1) m) ^ 2)
          = Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff (t + 1) m) ^ 2)
              + Finset.sum (Finset.range S.batchSize)
                  (fun i => (S.flatCoeff (t + 1) (t * S.batchSize + i)) ^ 2) := hSplit
        _ = S.beta ^ 2 *
              Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2)
              + (1 - S.beta) ^ 2 / S.batchSizeℝ := by
                rw [hFirst, hLast]
        _ ≤ S.beta ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)
              + (1 - S.beta) ^ 2 / S.batchSizeℝ := hMain
        _ = ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ := by
              field_simp [S.batchSizeℝ_ne_zero, hOneAddNe]
              ring

private theorem expectedNoise_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedNoise t ≤
        Real.sqrt ((1 - S.beta) / (1 + S.beta))
          * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  intro t
  have hFirst := (S.flatWeightedNoise_analysis t).2
  have hInside :
      S.D * S.sigma ^ 2 *
          Finset.sum (Finset.range (t * S.batchSize))
            (fun m => (S.flatCoeff t m) ^ 2)
        ≤ S.D * S.sigma ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ) := by
    exact mul_le_mul_of_nonneg_left
      (S.flatCoeff_sq_sum_bound t)
      (mul_nonneg S.D_nonneg (sq_nonneg S.sigma))
  calc
    S.expectedNoise t
      = ∫ ω, ‖S.flatPartialSum t (t * S.batchSize) ω‖ ∂S.μ := by
          simp [expectedNoise, S.momentumNoiseProcess_eq_flatPartialSum]
    _ ≤
        Real.sqrt
          (S.D * S.sigma ^ 2
            * Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2)) := hFirst
    _ ≤ Real.sqrt (S.D * S.sigma ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)) := by
          exact Real.sqrt_le_sqrt hInside
    _ = Real.sqrt (S.D * S.sigma ^ 2) *
          Real.sqrt (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ) := by
            rw [Real.sqrt_mul (mul_nonneg S.D_nonneg (sq_nonneg _))]
    _ = (Real.sqrt S.D * S.sigma) *
          (Real.sqrt ((1 - S.beta) / (1 + S.beta)) / Real.sqrt S.batchSizeℝ) := by
            rw [Real.sqrt_mul S.D_nonneg, Real.sqrt_sq S.sigma_nonneg,
              Real.sqrt_div S.one_sub_div_one_add_nonneg]
    _ = Real.sqrt ((1 - S.beta) / (1 + S.beta))
          * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
            ring

private theorem momentumError_eq_drift_add_noise
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω, S.momentumError t ω = S.driftComponent t ω + S.momentumNoiseProcess t ω
  | 0, ω => by
      simp [driftComponent, momentumNoiseProcess]
  | t + 1, ω => by
      rw [S.momentumError_split_step t ω, S.momentumError_eq_drift_add_noise t ω]
      simp [driftComponent, momentumNoiseProcess, smul_add,
        add_assoc, add_left_comm, add_comm]

private theorem norm_driftComponent_le
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {c : ℝ} (hcNonneg : 0 ≤ c)
    (hInc : ∀ t ω, ‖S.grad (t + 1) ω - S.grad t ω‖ ≤ c) :
    ∀ t ω,
      ‖S.driftComponent t ω‖ ≤
        S.beta ^ t * S.momentumErrorNorm 0 ω + c * shiftedGeometricPrefix S.beta t
  | 0, ω => by
      have hTailNonneg : 0 ≤ c * shiftedGeometricPrefix S.beta 0 := by
        simp [shiftedGeometricPrefix]
      simp [driftComponent, StochasticSteepestDescentGeometryContext.momentumErrorNorm,
        hTailNonneg]
  | t + 1, ω => by
      have hIH := S.norm_driftComponent_le hcNonneg hInc t ω
      have hScaledInc : S.beta * ‖S.grad (t + 1) ω - S.grad t ω‖ ≤ S.beta * c :=
        mul_le_mul_of_nonneg_left (hInc t ω) S.beta_nonneg
      calc
        ‖S.driftComponent (t + 1) ω‖
          = ‖S.beta • S.driftComponent t ω + S.beta • (S.grad (t + 1) ω - S.grad t ω)‖ := by
              simp [driftComponent]
        _ ≤ ‖S.beta • S.driftComponent t ω‖ + ‖S.beta • (S.grad (t + 1) ω - S.grad t ω)‖ :=
              norm_add_le _ _
        _ = S.beta * ‖S.driftComponent t ω‖ + S.beta * ‖S.grad (t + 1) ω - S.grad t ω‖ := by
              simp [norm_smul, Real.norm_of_nonneg S.beta_nonneg]
        _ ≤ S.beta * ‖S.driftComponent t ω‖ + S.beta * c := by
              linarith
        _ ≤ S.beta *
              (S.beta ^ t * S.momentumErrorNorm 0 ω + c * shiftedGeometricPrefix S.beta t)
              + S.beta * c := by
                have hMul := mul_le_mul_of_nonneg_left hIH S.beta_nonneg
                linarith
        _ = S.beta ^ (t + 1) * S.momentumErrorNorm 0 ω
              + c * shiftedGeometricPrefix S.beta (t + 1) := by
              rw [shiftedGeometricPrefix_succ]
              ring

private theorem momentumErrorNorm_le_unrolled
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω,
      S.momentumErrorNorm t ω ≤
        S.beta ^ t * S.momentumErrorNorm 0 ω
          + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
          + ‖S.momentumNoiseProcess t ω‖ := by
  intro t ω
  have hDrift :=
    S.norm_driftComponent_le
      (c := S.L * (2 * S.eta))
      (by
        have hTwoEtaNonneg : 0 ≤ 2 * S.eta := by
          nlinarith [S.eta_pos]
        exact mul_nonneg S.L_pos.le hTwoEtaNonneg)
      (by
        intro s ω
        simpa [mul_assoc, mul_left_comm, mul_comm] using S.grad_increment_bound s ω)
      t ω
  calc
    S.momentumErrorNorm t ω = ‖S.momentumError t ω‖ := rfl
    _ = ‖S.driftComponent t ω + S.momentumNoiseProcess t ω‖ := by
          rw [S.momentumError_eq_drift_add_noise t ω]
    _ ≤ ‖S.driftComponent t ω‖ + ‖S.momentumNoiseProcess t ω‖ := norm_add_le _ _
    _ ≤ S.beta ^ t * S.momentumErrorNorm 0 ω
          + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
          + ‖S.momentumNoiseProcess t ω‖ := by
            linarith

private theorem average_momentumError_bound_of_pointwise
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (hCor10 :
      ∀ t,
        S.expectedMomentumError t ≤
          S.beta ^ t * S.expectedMomentumError 0
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta))
                * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.expectedMomentumError t) / (T : ℝ) ≤
        (S.expectedMomentumError 0 * geometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  let k : ℝ :=
    (2 * S.beta / (1 - S.beta)) * S.L * S.eta
      + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ
  have hPoint :
      ∀ t,
        S.expectedMomentumError t ≤
          (S.beta ^ t * S.expectedMomentumError 0) + k := by
    intro t
    have hk : k =
        (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := rfl
    linarith [hCor10 t]
  have hAvg :=
    average_bound_of_pointwise_const
      (u := S.expectedMomentumError)
      (g := fun t => S.beta ^ t * S.expectedMomentumError 0)
      (main := fun T => geometricPrefix S.beta T * S.expectedMomentumError 0)
      (k := k)
      hPoint
      (by intro T; simp [geometricPrefix, Finset.sum_mul])
  intro T hT
  calc
    (Finset.sum (Finset.range T) fun t => S.expectedMomentumError t) / (T : ℝ)
      ≤ (geometricPrefix S.beta T * S.expectedMomentumError 0) / (T : ℝ) + k := hAvg T hT
    _ = (S.expectedMomentumError 0 * geometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
          simp [k]
          ring

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-- The initial momentum is globally measurable. -/
private lemma momentum_zero_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    Measurable (S.momentum 0) := by
  rcases S.momentum_zero_eq_zero_or_minibatchGradient with hZero | hBatch
  · have hEq : S.momentum 0 = fun _ : Ω => (0 : StrongDual ℝ V) := by
      funext ω
      simp [hZero ω]
    rw [hEq]
    exact measurable_const
  · have hEq : S.momentum 0 = S.minibatchGradient 0 := by
      funext ω
      exact hBatch ω
    rw [hEq]
    exact S.minibatchGradient_measurable 0

/-- The momentum process is measurable at each time. -/
private lemma momentum_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.momentum t) := by
  intro t
  induction t with
  | zero =>
      simpa using S.momentum_zero_measurable
  | succ t ih =>
      have hEq :
          S.momentum (t + 1) =
            fun ω =>
              S.beta • S.momentum t ω + (1 - S.beta) • S.minibatchGradient (t + 1) ω := by
        funext ω
        simpa using S.momentum_succ t ω
      rw [hEq]
      exact (ih.const_smul S.beta).add
        ((S.minibatchGradient_measurable (t + 1)).const_smul (1 - S.beta))

/-- The initialized momentum is integrable under the shared stochastic assumptions. -/
private lemma momentum_zero_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    Integrable (S.momentum 0) S.μ := by
  rcases S.momentum_zero_eq_zero_or_minibatchGradient with hZero | hBatch
  · have hEq : S.momentum 0 = fun _ : Ω => (0 : StrongDual ℝ V) := by
      funext ω
      simp [hZero ω]
    rw [hEq]
    exact
      (MeasureTheory.integrable_zero Ω (StrongDual ℝ V) S.μ :
        Integrable (fun _ : Ω => (0 : StrongDual ℝ V)) S.μ)
  · have hEq : S.momentum 0 = S.minibatchGradient 0 := by
      funext ω
      exact hBatch ω
    rw [hEq]
    exact S.minibatchGradient_integrable 0

/-- The expected momentum-error norm is nonnegative. -/
private lemma expectedMomentumError_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    0 ≤ S.expectedMomentumError t := by
  exact integral_nonneg fun _ => norm_nonneg _

/-- The initial expected momentum-error norm is nonnegative. -/
lemma initialExpectedMomentumError_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    0 ≤ S.initialExpectedMomentumError :=
  S.expectedMomentumError_nonneg 0

/-- The realized momentum-error norm is nonnegative. -/
private lemma momentumErrorNorm_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    0 ≤ S.momentumErrorNorm t ω :=
  norm_nonneg _

/-- The momentum-error norm is integrable under the shared stochastic assumptions. -/
lemma momentumErrorNorm_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Integrable (fun ω => S.momentumErrorNorm t ω) S.μ := by
  intro t
  letI := S.prob
  letI : IsFiniteMeasure S.μ := by
    refine ⟨by simp⟩
  let drift : ℝ := S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
  have hInit :
      Integrable (fun ω => S.momentumErrorNorm 0 ω) S.μ := by
    simpa [StochasticSteepestDescentGeometryContext.momentumErrorNorm,
      StochasticSteepestDescentGeometryContext.momentumError] using
      (((S.grad_integrable 0).sub S.momentum_zero_integrable).norm)
  have hNoise :
      Integrable (fun ω => ‖S.momentumNoiseProcess t ω‖) S.μ :=
    S.momentumNoiseProcess_norm_integrable t
  have hUpper :
      Integrable
        (fun ω =>
          S.beta ^ t * S.momentumErrorNorm 0 ω
            + drift
            + ‖S.momentumNoiseProcess t ω‖) S.μ :=
    ((hInit.const_mul (S.beta ^ t)).add (integrable_const drift)).add hNoise
  have hMeas :
      AEStronglyMeasurable (fun ω => S.momentumErrorNorm t ω) S.μ := by
    exact
      (((S.grad_stronglyMeasurable t).sub
        ((S.momentum_measurable t).stronglyMeasurable)).norm.aestronglyMeasurable)
  refine Integrable.mono' hUpper hMeas ?_
  filter_upwards with ω
  have hPoint := S.momentumErrorNorm_le_unrolled t ω
  have hDriftNonneg : 0 ≤ drift := by
    dsimp [drift]
    have hShiftNonneg : 0 ≤ shiftedGeometricPrefix S.beta t := by
      simpa [shiftedGeometricPrefix] using
        (Finset.sum_nonneg fun i _ => pow_nonneg S.beta_nonneg _)
    have hTwoEtaNonneg : 0 ≤ 2 * S.eta := by
      nlinarith [S.eta_pos]
    exact mul_nonneg (mul_nonneg S.L_pos.le hTwoEtaNonneg) hShiftNonneg
  have hUpperNonneg :
      0 ≤ S.beta ^ t * S.momentumErrorNorm 0 ω + drift + ‖S.momentumNoiseProcess t ω‖ := by
    have hInitNonneg : 0 ≤ S.beta ^ t * S.momentumErrorNorm 0 ω := by
      exact mul_nonneg (pow_nonneg S.beta_nonneg _) (S.momentumErrorNorm_nonneg 0 ω)
    have hNoiseNonneg : 0 ≤ ‖S.momentumNoiseProcess t ω‖ := norm_nonneg _
    linarith
  simpa [Real.norm_of_nonneg (S.momentumErrorNorm_nonneg t ω),
    Real.norm_of_nonneg hUpperNonneg] using hPoint

/-- Proposition-6 / Corollary-10 expected momentum-error bound. -/
private theorem momentum_expectedErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedMomentumError t ≤
        S.beta ^ t * S.expectedMomentumError 0
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta))
              * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  intro T
  letI := S.prob
  letI : IsFiniteMeasure S.μ := by
    refine ⟨by simp⟩
  let drift : ℝ := S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta T
  let upper : Ω → ℝ := fun ω =>
    S.beta ^ T * S.momentumErrorNorm 0 ω + drift + ‖S.momentumNoiseProcess T ω‖
  have hLower : Integrable (fun ω => S.momentumErrorNorm T ω) S.μ :=
    S.momentumErrorNorm_integrable T
  have hInit : Integrable (fun ω => S.momentumErrorNorm 0 ω) S.μ :=
    S.momentumErrorNorm_integrable 0
  have hNoise : Integrable (fun ω => ‖S.momentumNoiseProcess T ω‖) S.μ :=
    S.momentumNoiseProcess_norm_integrable T
  have hUpper : Integrable upper S.μ :=
    ((hInit.const_mul (S.beta ^ T)).add (integrable_const drift)).add hNoise
  have hStep :
      S.expectedMomentumError T ≤
        S.beta ^ T * S.expectedMomentumError 0 + drift + S.expectedNoise T := by
    have hUpperEq : upper = fun ω =>
        S.beta ^ T * S.momentumErrorNorm 0 ω + drift + ‖S.momentumNoiseProcess T ω‖ := rfl
    calc
      S.expectedMomentumError T = ∫ ω, S.momentumErrorNorm T ω ∂S.μ := rfl
      _ ≤ ∫ ω, upper ω ∂S.μ := by
            exact MeasureTheory.integral_mono_ae hLower hUpper
              (Filter.Eventually.of_forall fun ω => S.momentumErrorNorm_le_unrolled T ω)
      _ = ∫ ω, (S.beta ^ T * S.momentumErrorNorm 0 ω + drift) ∂S.μ
            + ∫ ω, ‖S.momentumNoiseProcess T ω‖ ∂S.μ := by
              simpa [upper, add_assoc] using
                (MeasureTheory.integral_add
                  ((hInit.const_mul (S.beta ^ T)).add (integrable_const drift))
                  hNoise :
                    ∫ ω,
                        ((S.beta ^ T * S.momentumErrorNorm 0 ω + drift)
                          + ‖S.momentumNoiseProcess T ω‖) ∂S.μ
                      =
                        ∫ ω, (S.beta ^ T * S.momentumErrorNorm 0 ω + drift) ∂S.μ
                          + ∫ ω, ‖S.momentumNoiseProcess T ω‖ ∂S.μ)
      _ = S.beta ^ T * S.expectedMomentumError 0 + drift + S.expectedNoise T := by
            have hInitInt :
                ∫ ω, S.beta ^ T * S.momentumErrorNorm 0 ω ∂S.μ
                  = S.beta ^ T * S.expectedMomentumError 0 := by
              rw [MeasureTheory.integral_const_mul]
              rfl
            have hDriftInt :
                ∫ _ : Ω, drift ∂S.μ = drift := by
              simp [drift]
            have hNoiseInt :
                ∫ ω, ‖S.momentumNoiseProcess T ω‖ ∂S.μ = S.expectedNoise T := by
              rfl
            rw [MeasureTheory.integral_add (hInit.const_mul (S.beta ^ T)) (integrable_const drift)]
            rw [hInitInt, hDriftInt, hNoiseInt]
  have hDriftCollapse :
      drift ≤ (2 * S.beta / (1 - S.beta)) * S.L * S.eta := by
    dsimp [drift]
    have hGeom : shiftedGeometricPrefix S.beta T ≤ S.beta / (1 - S.beta) :=
      shifted_geometricPrefix_le S.beta S.beta_nonneg S.beta_lt_one T
    have hTwoEtaNonneg : 0 ≤ 2 * S.eta := by
      nlinarith [S.eta_pos]
    have hCoeffNonneg : 0 ≤ S.L * (2 * S.eta) := by
      exact mul_nonneg S.L_pos.le hTwoEtaNonneg
    have hScaled :
        S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta T ≤
          S.L * (2 * S.eta) * (S.beta / (1 - S.beta)) := by
      exact mul_le_mul_of_nonneg_left hGeom hCoeffNonneg
    calc
      S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta T
        ≤ S.L * (2 * S.eta) * (S.beta / (1 - S.beta)) := hScaled
      _ = (2 * S.beta / (1 - S.beta)) * S.L * S.eta := by ring
  calc
    S.expectedMomentumError T
      ≤ S.beta ^ T * S.expectedMomentumError 0 + drift + S.expectedNoise T := hStep
    _ ≤ S.beta ^ T * S.expectedMomentumError 0
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta))
              * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
            linarith [hDriftCollapse, S.expectedNoise_bound T]

/--
Expected momentum-residual bound, with an arbitrary initial residual
`E_0(ω) = ∇f(W_0) - M_0(ω)`.
-/
theorem Corollary10PointwiseMomentumErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedMomentumError t ≤
        S.beta ^ t * S.expectedMomentumError 0
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta))
              * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  exact S.momentum_expectedErrorBound

end PublicTheorems

end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
