import Mathlib
import MlOptBoundsFormalization.MinibatchNoise
import MlOptBoundsFormalization.WeightAndUpdateBounds

open scoped BigOperators

namespace MlOptBoundsFormalization

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-!
Momentum-error layer used upstream of Theorem 14.

This module collects:

1. the vector-valued momentum recursion identities;
2. the scalar geometric-sum lemmas used to unroll the final recurrence;
3. the concrete Proposition-6 momentum-noise process and its bounds;
4. Corollary 10 in pointwise and averaged form.
-/

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

end ScalarLemmas

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

omit [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
  [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)] in
private lemma weightedPartialSum_stronglyMeasurable_global
    {ξ : ℕ → Ω → StrongDual ℝ V} {α : ℕ → ℝ}
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (k : ℕ) :
    StronglyMeasurable (fun ω => weightedPartialSum α ξ (k + 1) ω) := by
  induction k with
  | zero =>
      simpa [weightedPartialSum] using (sample_stronglyMeasurable 0).const_smul (α 0)
  | succ k hk =>
      have hCurr :
          StronglyMeasurable (fun ω => α (k + 1) • ξ (k + 1) ω) := by
        simpa using (sample_stronglyMeasurable (k + 1)).const_smul (α (k + 1))
      convert hk.add hCurr using 1
      ext ω
      simp [weightedPartialSum, Finset.sum_range_succ, add_left_comm, add_comm]

private def flatTimeIndex
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) : ℕ :=
  m / S.batchSize + 1

private def flatSampleIndex
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) : Fin S.batchSize :=
  ⟨m % S.batchSize, Nat.mod_lt _ S.batchSize_pos⟩

private def flatCoeff
    (S : StochasticSteepestDescentGeometryContext Ω V) (t m : ℕ) : ℝ :=
  ((1 - S.beta) * S.beta ^ (t - 1 - m / S.batchSize)) / S.batchSizeℝ

private def flatNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    Ω → StrongDual ℝ V :=
  S.ξ (S.flatTimeIndex m) (S.flatSampleIndex m)

private def flatPartialSum
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t k : ℕ) (ω : Ω) : StrongDual ℝ V :=
  weightedPartialSum (S.flatCoeff t) S.flatNoise k ω

private lemma flatNoise_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    StronglyMeasurable (S.flatNoise m) := by
  simpa [flatNoise, flatTimeIndex, flatSampleIndex] using
    S.sample_stronglyMeasurable (S.flatTimeIndex m) (S.flatSampleIndex m)

private lemma flatNoise_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    Integrable (S.flatNoise m) S.μ := by
  simpa [flatNoise, flatTimeIndex, flatSampleIndex] using
    S.sample_integrable (S.flatTimeIndex m) (S.flatSampleIndex m)

private lemma flatNoise_mean_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    ∫ ω, S.flatNoise m ω ∂S.μ = 0 := by
  simpa [flatNoise, flatTimeIndex, flatSampleIndex] using
    S.sample_mean_zero (S.flatTimeIndex m) (S.flatSampleIndex m)

private lemma flatNoise_second_moment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) (m : ℕ) :
    Integrable (fun ω => ‖S.flatNoise m ω‖ ^ 2) S.μ ∧
      ∫ ω, ‖S.flatNoise m ω‖ ^ 2 ∂S.μ ≤ S.sigma ^ 2 := by
  simpa [flatNoise, flatTimeIndex, flatSampleIndex] using
    S.second_moment_bound (S.flatTimeIndex m) (S.flatSampleIndex m)

private theorem pairIndexed_iIndep
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    iIndepFun (fun p : ℕ × Fin S.batchSize => S.ξ p.1 p.2) S.μ := by
  simpa [StochasticSteepestDescentGeometryContext.batchNoise] using
    (ProbabilityTheory.iIndepFun_uncurry'
      (X := fun t i => S.ξ t i)
      (mX := fun t i => (S.sample_stronglyMeasurable t i).measurable)
      (h1 := S.freshBatch_iIndep)
      (h2 := S.withinBatch_iIndep))

private theorem flatNoise_iIndep
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    iIndepFun S.flatNoise S.μ := by
  let e : ℕ → ℕ × Fin S.batchSize := fun m =>
    (S.flatTimeIndex m, S.flatSampleIndex m)
  have hInj : Function.Injective e := by
    intro a b h
    have hDiv : a / S.batchSize = b / S.batchSize := by
      have hTime : S.flatTimeIndex a = S.flatTimeIndex b := congrArg Prod.fst h
      dsimp [e, flatTimeIndex] at hTime
      exact Nat.add_right_cancel hTime
    have hMod : a % S.batchSize = b % S.batchSize := by
      exact Fin.ext_iff.mp (congrArg Prod.snd h)
    calc
      a = a % S.batchSize + S.batchSize * (a / S.batchSize) := by
            exact (Nat.mod_add_div a S.batchSize).symm
      _ = b % S.batchSize + S.batchSize * (b / S.batchSize) := by rw [hMod, hDiv]
      _ = b := by exact Nat.mod_add_div b S.batchSize
  simpa [flatNoise, flatTimeIndex, flatSampleIndex, e] using
    (pairIndexed_iIndep S).precomp hInj

private lemma flatCoeff_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t m : ℕ) :
    0 ≤ S.flatCoeff t m := by
  have hOneSubNonneg : 0 ≤ 1 - S.beta := sub_nonneg.mpr (le_of_lt S.beta_lt_one)
  have hPowNonneg : 0 ≤ S.beta ^ (t - 1 - m / S.batchSize) := pow_nonneg S.beta_nonneg _
  exact div_nonneg (mul_nonneg hOneSubNonneg hPowNonneg) S.batchSizeℝ_pos.le

private lemma last_block_div
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    (t * S.batchSize + i) / S.batchSize = t := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ S.batchSize_pos]
  rw [Nat.div_eq_of_lt hi]
  simp

private lemma last_block_mod
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t i : ℕ) (hi : i < S.batchSize) :
    (t * S.batchSize + i) % S.batchSize = i := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

private lemma flatCoeff_sum_eq
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
        have hmLt : m < t * S.batchSize := Finset.mem_range.mp hm
        have hDivLt : m / S.batchSize < t := by
          exact (Nat.div_lt_iff_lt_mul S.batchSize_pos).2 hmLt
        have hExp : t - m / S.batchSize = (t - 1 - m / S.batchSize) + 1 := by
          omega
        have hScalar :
            S.flatCoeff (t + 1) m = S.beta * S.flatCoeff t m := by
          dsimp [flatCoeff]
          rw [hExp, pow_succ']
          field_simp [S.batchSizeℝ_ne_zero]
        rw [hScalar]
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
                  have hiLt : i < S.batchSize := Finset.mem_range.mp hi
                  dsimp [flatCoeff]
                  rw [S.last_block_div t i hiLt]
                  norm_num
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

private lemma flatCoeff_sum_le_one
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    Finset.sum (Finset.range (t * S.batchSize)) (fun m => S.flatCoeff t m) ≤ 1 := by
  rw [S.flatCoeff_sum_eq t]
  have hPowNonneg : 0 ≤ S.beta ^ t := pow_nonneg S.beta_nonneg t
  linarith

/-- The concrete recursive momentum-noise process from Proposition 6. -/
def momentumNoiseProcess
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℕ → Ω → StrongDual ℝ V
  | 0 => 0
  | t + 1 => fun ω =>
      S.beta • S.momentumNoiseProcess t ω + (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω

/-- The expected norm of the concrete recursive momentum-noise process. -/
def expectedNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, ‖S.momentumNoiseProcess t ω‖ ∂S.μ

private lemma momentumNoiseProcess_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    S.momentumNoiseProcess 0 = fun _ => 0 := by
  rfl

private lemma momentumNoiseProcess_succ
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.momentumNoiseProcess (t + 1) =
      fun ω =>
        S.beta • S.momentumNoiseProcess t ω + (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω := by
  rfl

private theorem flatFutureCondexpZero
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ∀ k, k + 1 < t * S.batchSize →
      S.μ[S.flatNoise (k + 1)
          | naturalNoiseFiltration (fun m => S.flatNoise_stronglyMeasurable m) k] =ᵐ[S.μ] 0 := by
  /-
  This is the Proposition-6 analogue of the minibatch bridge: the current proof
  uses the stronger Assumption-1 surrogate through per-sample mean zero,
  shifted flattened independence, and the derived future-noise conditional
  expectation zero statement established here.
  -/
  intro k hk
  simpa using
    centered_noise_condexp_natural_ae_eq_zero
      (μ := S.μ)
      (ξ := S.flatNoise)
      (hξ := fun m => S.flatNoise_stronglyMeasurable m)
      (hIndep := S.flatNoise_iIndep)
      (Nat.lt_succ_self k)
      (S.flatNoise_mean_zero (k + 1))

private theorem momentumNoiseProcess_eq_flatPartialSum
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.momentumNoiseProcess t = S.flatPartialSum t (t * S.batchSize)
  | 0 => by
      funext ω
      simp [momentumNoiseProcess_zero, flatPartialSum, weightedPartialSum]
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
        have hmLt : m < t * S.batchSize := Finset.mem_range.mp hm
        have hDivLt : m / S.batchSize < t := by
          exact (Nat.div_lt_iff_lt_mul S.batchSize_pos).2 hmLt
        have hExp : t - m / S.batchSize = (t - 1 - m / S.batchSize) + 1 := by
          omega
        have hScalar : S.flatCoeff (t + 1) m = S.beta * S.flatCoeff t m := by
          dsimp [flatCoeff]
          rw [hExp, pow_succ']
          field_simp [S.batchSizeℝ_ne_zero]
        rw [hScalar, smul_smul]
      have hLast :
          Finset.sum (Finset.range S.batchSize)
              (fun i =>
                S.flatCoeff (t + 1) (t * S.batchSize + i) •
                  S.flatNoise (t * S.batchSize + i) ω) =
            (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω := by
        calc
          Finset.sum (Finset.range S.batchSize)
              (fun i =>
                S.flatCoeff (t + 1) (t * S.batchSize + i) •
                  S.flatNoise (t * S.batchSize + i) ω)
            = Finset.sum (Finset.range S.batchSize)
                (fun i =>
                  (1 - S.beta) •
                    (uniformBatchWeight S.batchSize •
                      (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ else 0) ω)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    have hiLt : i < S.batchSize := Finset.mem_range.mp hi
                    have hAlpha :
                        S.flatCoeff (t + 1) (t * S.batchSize + i) =
                          (1 - S.beta) / S.batchSizeℝ := by
                      dsimp [flatCoeff]
                      rw [S.last_block_div t i hiLt]
                      norm_num
                    have hIndex : S.flatSampleIndex (t * S.batchSize + i) = ⟨i, hiLt⟩ := by
                      apply Fin.ext
                      simp [flatSampleIndex, S.last_block_mod t i hiLt]
                    have hNoise :
                        S.flatNoise (t * S.batchSize + i) = S.ξ (t + 1) ⟨i, hiLt⟩ := by
                      simp [flatNoise, flatTimeIndex, S.last_block_div t i hiLt, hIndex]
                    have hIf :
                        (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ else 0) =
                          S.ξ (t + 1) ⟨i, hiLt⟩ := by
                      simp [hiLt]
                    rw [hAlpha, hNoise, hIf, smul_smul]
                    rw [uniformBatchWeight]
                    congr 1
                    simp [StochasticSteepestDescentParameters.batchSizeℝ, div_eq_mul_inv]
          _ = (1 - S.beta) •
                Finset.sum (Finset.range S.batchSize)
                  (fun i =>
                    uniformBatchWeight S.batchSize •
                      (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ else 0) ω) := by
                    rw [Finset.smul_sum]
          _ = (1 - S.beta) •
                Finset.sum Finset.univ
                  (fun i : Fin S.batchSize => uniformBatchWeight S.batchSize • S.ξ (t + 1) i ω) := by
                    congr 1
                    symm
                    simpa using
                      (Fin.sum_univ_eq_sum_range (n := S.batchSize)
                        (fun i =>
                          uniformBatchWeight S.batchSize •
                            (if hi : i < S.batchSize then S.ξ (t + 1) ⟨i, hi⟩ else 0) ω))
          _ = (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω := by
                simp [StochasticSteepestDescentGeometryContext.minibatchNoiseProcess]
      calc
        S.momentumNoiseProcess (t + 1) ω
          = S.beta • S.momentumNoiseProcess t ω
              + (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω := by
                rw [S.momentumNoiseProcess_succ]
        _ = S.beta • S.flatPartialSum t (t * S.batchSize) ω
              + (1 - S.beta) • S.minibatchNoiseProcess (t + 1) ω := by
                rw [S.momentumNoiseProcess_eq_flatPartialSum t]
        _ = S.flatPartialSum (t + 1) ((t + 1) * S.batchSize) ω := by
                rw [hSplit, hFirst, hLast]

theorem momentumNoiseProcess_mean_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, ∫ ω, S.momentumNoiseProcess t ω ∂S.μ = 0 := by
  intro t
  calc
    ∫ ω, S.momentumNoiseProcess t ω ∂S.μ
      = ∫ ω, S.flatPartialSum t (t * S.batchSize) ω ∂S.μ := by
          simp [S.momentumNoiseProcess_eq_flatPartialSum]
    _ = 0 := weightedPartialSum_mean_zero
          (sample_integrable := by intro m hm; exact S.flatNoise_integrable m)
          (sample_mean_zero := by intro m hm; exact S.flatNoise_mean_zero m)

private theorem flatCoeff_sq_sum_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      Finset.sum (Finset.range (t * S.batchSize))
          (fun m => (S.flatCoeff t m) ^ 2) ≤
        ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ
  | 0 => by
      have hRatioNonneg : 0 ≤ ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ := by
        have hOneAddPos : 0 < 1 + S.beta := by linarith [S.beta_nonneg]
        exact div_nonneg
          (div_nonneg (sub_nonneg.mpr (le_of_lt S.beta_lt_one)) hOneAddPos.le)
          S.batchSizeℝ_pos.le
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
            S.beta ^ 2
              * Finset.sum (Finset.range (t * S.batchSize))
                  (fun m => (S.flatCoeff t m) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        have hmLt : m < t * S.batchSize := Finset.mem_range.mp hm
        have hDivLt : m / S.batchSize < t := by
          exact (Nat.div_lt_iff_lt_mul S.batchSize_pos).2 hmLt
        have hExp : t - m / S.batchSize = (t - 1 - m / S.batchSize) + 1 := by
          omega
        have hScalar : S.flatCoeff (t + 1) m = S.beta * S.flatCoeff t m := by
          dsimp [flatCoeff]
          rw [hExp, pow_succ']
          field_simp [S.batchSizeℝ_ne_zero]
        rw [hScalar]
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
                  have hiLt : i < S.batchSize := Finset.mem_range.mp hi
                  dsimp [flatCoeff]
                  rw [S.last_block_div t i hiLt]
                  norm_num
          _ = S.batchSizeℝ * (((1 - S.beta) / S.batchSizeℝ) ^ 2) := by
                simp [StochasticSteepestDescentParameters.batchSizeℝ]
          _ = (1 - S.beta) ^ 2 / S.batchSizeℝ := by
                field_simp [S.batchSizeℝ_ne_zero]
      have hMain :
          S.beta ^ 2
              * Finset.sum (Finset.range (t * S.batchSize))
                  (fun m => (S.flatCoeff t m) ^ 2)
            + (1 - S.beta) ^ 2 / S.batchSizeℝ
          ≤
            S.beta ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)
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
        _ = S.beta ^ 2
              * Finset.sum (Finset.range (t * S.batchSize))
                  (fun m => (S.flatCoeff t m) ^ 2)
              + (1 - S.beta) ^ 2 / S.batchSizeℝ := by
                rw [hFirst, hLast]
        _ ≤ S.beta ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)
              + (1 - S.beta) ^ 2 / S.batchSizeℝ := hMain
        _ = ((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ := by
              field_simp [S.batchSizeℝ_ne_zero, hOneAddNe]
              ring

theorem expectedNoise_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedNoise t ≤
        Real.sqrt ((1 - S.beta) / (1 + S.beta))
          * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  intro t
  letI : IsProbabilityMeasure S.μ := S.prob
  have hFirst :=
    weighted_noise_first_moment_bound
      S.pairing
      S.assumption4_localProxyPotential
      (μ := S.μ)
      (sigma := S.sigma)
      (ξ := S.flatNoise)
      (α := S.flatCoeff t)
      (n := t * S.batchSize)
      (coeff_nonneg := by intro m hm; exact S.flatCoeff_nonneg t m)
      (coeff_sum_le_one := S.flatCoeff_sum_le_one t)
      (sample_stronglyMeasurable := fun m => S.flatNoise_stronglyMeasurable m)
      (sample_integrable := by intro m hm; exact S.flatNoise_integrable m)
      (sample_mean_zero := by intro m hm; exact S.flatNoise_mean_zero m)
      (future_condexp_zero := S.flatFutureCondexpZero t)
      (sample_norm_le_noiseRadius_ae := by
        intro m hm
        exact S.sample_norm_le_noiseRadius_ae (S.flatTimeIndex m) (S.flatSampleIndex m))
      (second_moment_bound := by intro m hm; exact S.flatNoise_second_moment_bound m)
  have hDSigmaNonneg : 0 ≤ S.D * S.sigma ^ 2 := by
    exact mul_nonneg S.D_nonneg (sq_nonneg _)
  have hCoeffSq := S.flatCoeff_sq_sum_bound t
  have hRatioNonneg : 0 ≤ (1 - S.beta) / (1 + S.beta) := by
    have hDenPos : 0 < 1 + S.beta := by linarith [S.beta_nonneg]
    exact div_nonneg (sub_nonneg.mpr (le_of_lt S.beta_lt_one)) hDenPos.le
  have hMainBound :
      S.expectedNoise t ≤
        Real.sqrt
          (S.D * S.sigma ^ 2
            * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)) := by
    have hInside :
        S.D * S.sigma ^ 2
            * Finset.sum (Finset.range (t * S.batchSize))
                (fun m => (S.flatCoeff t m) ^ 2)
          ≤ S.D * S.sigma ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ) := by
      gcongr
    calc
      S.expectedNoise t
        = ∫ ω, ‖S.flatPartialSum t (t * S.batchSize) ω‖ ∂S.μ := by
            simp [expectedNoise, S.momentumNoiseProcess_eq_flatPartialSum]
      _ ≤
          Real.sqrt
            (S.D * S.sigma ^ 2
              * Finset.sum (Finset.range (t * S.batchSize))
                  (fun m => (S.flatCoeff t m) ^ 2)) := hFirst
      _ ≤
          Real.sqrt
            (S.D * S.sigma ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)) :=
          Real.sqrt_le_sqrt hInside
  calc
    S.expectedNoise t
      ≤ Real.sqrt (S.D * S.sigma ^ 2 * (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ)) :=
        hMainBound
    _ = Real.sqrt (S.D * S.sigma ^ 2) *
          Real.sqrt (((1 - S.beta) / (1 + S.beta)) / S.batchSizeℝ) := by
            rw [Real.sqrt_mul hDSigmaNonneg]
    _ = (Real.sqrt S.D * S.sigma)
          * (Real.sqrt ((1 - S.beta) / (1 + S.beta)) / Real.sqrt S.batchSizeℝ) := by
            rw [Real.sqrt_mul S.D_nonneg, Real.sqrt_sq S.sigma_nonneg, Real.sqrt_div hRatioNonneg]
    _ = Real.sqrt ((1 - S.beta) / (1 + S.beta))
          * Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
            ring

/-- At time `0`, the momentum error is exactly the initial gradient. -/
lemma momentumError_zero (S : StochasticSteepestDescentGeometryContext Ω V) :
    S.momentumError 0 = S.grad 0 := by
  simp [StochasticSteepestDescentGeometryContext.momentumError,
    StochasticSteepestDescentGeometryContext.grad, S.momentum_zero]

/--
One-step momentum-error recursion:

`E_{t+1} = β E_t + β(∇f(W_{t+1}) - ∇f(W_t)) + (1 - β) ξ_{S_{t+1}}`.
-/
lemma momentumError_succ (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.momentumError (t + 1) =
      S.beta • S.momentumError t
        + S.beta • (S.grad (t + 1) - S.grad t)
        + (1 - S.beta) • S.minibatchNoise (t + 1) := by
  calc
    S.momentumError (t + 1)
      = S.grad (t + 1) - (S.beta • S.momentum t + (1 - S.beta) • S.grad (t + 1)) := by
          simp [StochasticSteepestDescentGeometryContext.momentumError,
            StochasticSteepestDescentGeometryContext.grad, S.momentum_succ]
    _ =
        S.beta • (S.grad t - S.momentum t)
          + S.beta • (S.grad (t + 1) - S.grad t)
          + (1 - S.beta) • (0 : StrongDual ℝ V) := by
            simp [sub_eq_add_neg, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
            abel_nf
    _ =
        S.beta • S.momentumError t
          + S.beta • (S.grad (t + 1) - S.grad t)
          + (1 - S.beta) • S.minibatchNoise (t + 1) := by
            rw [S.minibatchNoise_eq_zero (t + 1)]
            simp [StochasticSteepestDescentGeometryContext.momentumError]

/-- The true momentum error splits as drift plus noise. -/
theorem momentumError_eq_drift_add_noise
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, S.momentumError t = S.driftComponent t + S.noiseComponent t
  | 0 => by
      simp [momentumError_zero, StochasticSteepestDescentGeometryContext.driftComponent,
        StochasticSteepestDescentGeometryContext.noiseComponent,
        StochasticSteepestDescentGeometryContext.grad]
  | t + 1 => by
      rw [S.momentumError_succ, S.momentumError_eq_drift_add_noise t]
      simp [StochasticSteepestDescentGeometryContext.driftComponent,
        StochasticSteepestDescentGeometryContext.noiseComponent,
        StochasticSteepestDescentGeometryContext.grad, smul_add,
        add_assoc, add_left_comm, add_comm]

/-- Norm version of `E_t = E_t^drift + E_t^noise`. -/
theorem norm_momentumError_le_drift_add_noise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ‖S.momentumError t‖ ≤ ‖S.driftComponent t‖ + ‖S.noiseComponent t‖ := by
  rw [S.momentumError_eq_drift_add_noise t]
  exact norm_add_le _ _

/-- Helper identity for the shifted geometric prefix used in the drift bound. -/
lemma shiftedGeometricPrefix_succ (q : ℝ) (t : ℕ) :
    shiftedGeometricPrefix q (t + 1) = q + q * shiftedGeometricPrefix q t := by
  calc
    shiftedGeometricPrefix q (t + 1) = q * geometricPrefix q (t + 1) :=
      shifted_geometricPrefix_eq_mul q _
    _ = q * (1 + q * geometricPrefix q t) := by
      rw [one_add_mul_geometricPrefix]
    _ = q + q * shiftedGeometricPrefix q t := by
      rw [shifted_geometricPrefix_eq_mul]
      ring

/--
If each gradient increment is bounded by a constant `c`, then the drift term
obeys the geometric bound used in Proposition 6 / Corollary 10.
-/
theorem norm_driftComponent_le
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {c : ℝ} (hcNonneg : 0 ≤ c)
    (hInc : ∀ t, ‖S.grad (t + 1) - S.grad t‖ ≤ c) :
    ∀ t,
      ‖S.driftComponent t‖ ≤
        S.beta ^ t * S.initialGradNorm + c * shiftedGeometricPrefix S.beta t
  | 0 => by
      simp [StochasticSteepestDescentGeometryContext.driftComponent, shiftedGeometricPrefix,
        StochasticSteepestDescentGeometryContext.initialGradNorm,
        StochasticSteepestDescentGeometryContext.grad]
  | t + 1 => by
      have hIH := norm_driftComponent_le S hcNonneg hInc t
      have hScale :
          ‖S.beta • S.driftComponent t‖ + ‖S.beta • (S.grad (t + 1) - S.grad t)‖
            ≤ S.beta * ‖S.driftComponent t‖ + S.beta * c := by
        have hScaledInc : S.beta * ‖S.grad (t + 1) - S.grad t‖ ≤ S.beta * c :=
          mul_le_mul_of_nonneg_left (hInc t) S.beta_nonneg
        rw [norm_smul, norm_smul]
        simp [Real.norm_of_nonneg S.beta_nonneg]
        linarith
      calc
        ‖S.driftComponent (t + 1)‖
          = ‖S.beta • S.driftComponent t + S.beta • (S.grad (t + 1) - S.grad t)‖ := by
              simp [StochasticSteepestDescentGeometryContext.driftComponent]
        _ ≤ ‖S.beta • S.driftComponent t‖ + ‖S.beta • (S.grad (t + 1) - S.grad t)‖ :=
              norm_add_le _ _
        _ ≤ S.beta * ‖S.driftComponent t‖ + S.beta * c := hScale
        _ ≤ S.beta * (S.beta ^ t * S.initialGradNorm + c * shiftedGeometricPrefix S.beta t)
              + S.beta * c := by
                have hMul := mul_le_mul_of_nonneg_left hIH S.beta_nonneg
                linarith
        _ = S.beta ^ (t + 1) * S.initialGradNorm + c * shiftedGeometricPrefix S.beta (t + 1) := by
              rw [shiftedGeometricPrefix_succ]
              ring

/-- The deterministic recursive noise component vanishes identically. -/
theorem noiseComponent_eq_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, S.noiseComponent t = 0
  | 0 => by
      simp [StochasticSteepestDescentGeometryContext.noiseComponent]
  | t + 1 => by
      simp [StochasticSteepestDescentGeometryContext.noiseComponent,
        noiseComponent_eq_zero S t, S.minibatchNoise_eq_zero (t + 1)]

/-- Direct geometry-level comparison between the deterministic noise term and the Proposition-6 expectation. -/
theorem noiseComponentNorm_le_expectedNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, S.noiseComponentNorm t ≤ S.expectedNoise t := by
  intro t
  have hNonneg : 0 ≤ S.expectedNoise t := by
    exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  simpa [StochasticSteepestDescentGeometryContext.noiseComponentNorm,
    S.noiseComponent_eq_zero t] using hNonneg

end StochasticSteepestDescentGeometryContext

section SmoothnessBridges

variable {V VDual : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]

/--
Assumption 3 implies a uniform bound on consecutive gradient increments as soon
as the corresponding iterate updates are uniformly bounded.
-/
theorem grad_increment_bound_of_local_smoothness_and_update_bound
    {R L δ : ℝ} {fGrad : V → VDual}
    (hLSmooth : LocalLipschitzOnClosedBallUnderNormPair fGrad R L)
    {W : ℕ → V} {gradSeq : ℕ → VDual}
    (hGrad : ∀ t, gradSeq t = fGrad (W t))
    (hRadius : ∀ t, ‖W t‖ ≤ R)
    (hUpdate : ∀ t, ‖W (t + 1) - W t‖ ≤ δ) :
    ∀ t, ‖gradSeq (t + 1) - gradSeq t‖ ≤ L * δ := by
  intro t
  rw [hGrad (t + 1), hGrad t]
  calc
    ‖fGrad (W (t + 1)) - fGrad (W t)‖ ≤ L * ‖W (t + 1) - W t‖ :=
      hLSmooth.bound (hRadius t) (hRadius (t + 1))
    _ ≤ L * δ := by
          exact mul_le_mul_of_nonneg_left (hUpdate t) hLSmooth.nonneg

end SmoothnessBridges

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Assumption 3 plus Proposition 9 imply the canonical `2Lη` gradient-increment bound. -/
theorem grad_increment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, ‖S.grad (t + 1) - S.grad t‖ ≤ 2 * S.L * S.eta := by
  have hUpdate : ∀ t, ‖S.W (t + 1) - S.W t‖ ≤ 2 * S.eta := by
    intro t
    exact (S.proposition9_weight_and_update_bounds t).2
  have hRadius : ∀ t, ‖S.W t‖ ≤ 1 / S.lambda := S.weight_bound_from_feasible_step
  have hGradInc :
      ∀ t,
        ‖S.grad (t + 1) - S.grad t‖ ≤ S.L * (2 * S.eta) :=
    MlOptBoundsFormalization.grad_increment_bound_of_local_smoothness_and_update_bound
      S.assumption3_fLocalSmoothness.local_lipschitz
      (fun _ => rfl)
      hRadius
      hUpdate
  intro t
  simpa [mul_assoc, mul_left_comm, mul_comm] using hGradInc t

end StochasticSteepestDescentGeometryContext

section Corollary10

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem average_momentumError_bound_of_pointwise
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (momentumError : ℕ → ℝ)
    (hCor10 :
      ∀ t,
        momentumError t ≤
          S.beta ^ t * S.initialGradNorm
            + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
            + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
                / Real.sqrt S.batchSizeℝ) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => momentumError t) / (T : ℝ) ≤
        (S.initialGradNorm * geometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
  intro T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  let k : ℝ :=
    (2 * S.beta / (1 - S.beta)) * S.L * S.eta
      + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
          / Real.sqrt S.batchSizeℝ
  have hSum :
      Finset.sum (Finset.range T) (fun t => momentumError t) ≤
        Finset.sum (Finset.range T) (fun t =>
          S.beta ^ t * S.initialGradNorm + k) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have hPoint := hCor10 t
    have hk : k =
        (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := rfl
    linarith
  have hConst :
      Finset.sum (Finset.range T) (fun _ => k) = (T : ℝ) * k := by
    simp
  have hGeom :
      Finset.sum (Finset.range T) (fun t => S.beta ^ t * S.initialGradNorm) =
        geometricPrefix S.beta T * S.initialGradNorm := by
    simp [geometricPrefix, Finset.sum_mul]
  have hDiv := div_le_div_of_nonneg_right hSum hT'.le
  calc
    (Finset.sum (Finset.range T) fun t => momentumError t) / (T : ℝ)
      ≤ (Finset.sum (Finset.range T) fun t =>
          S.beta ^ t * S.initialGradNorm + k) / (T : ℝ) := hDiv
    _ = ((geometricPrefix S.beta T * S.initialGradNorm)
            + (T : ℝ) * k) / (T : ℝ) := by
            rw [Finset.sum_add_distrib, hGeom, hConst]
    _ = (geometricPrefix S.beta T * S.initialGradNorm) / (T : ℝ) + k := by
          field_simp [show (T : ℝ) ≠ 0 by positivity]
    _ = (S.initialGradNorm * geometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
          simp [k]
          ring

/--
Bounds the drift part of the momentum error once the update size is uniformly
bounded by a fixed step radius.
-/
theorem momentum_drift_bound_from_step_bound
    {beta L stepBound initialGradNorm : ℝ}
    (hBetaNonneg : 0 ≤ beta) (hBetaLt : beta < 1)
    (hLNonneg : 0 ≤ L) (hStepNonneg : 0 ≤ stepBound)
    {driftError : ℕ → ℝ}
    (hDriftGeom :
      ∀ t,
        driftError t ≤
          beta ^ t * initialGradNorm + L * stepBound * shiftedGeometricPrefix beta t) :
    ∀ t,
      driftError t ≤
        beta ^ t * initialGradNorm + (beta / (1 - beta)) * L * stepBound := by
  intro t
  have hGeom :
      shiftedGeometricPrefix beta t ≤ beta / (1 - beta) :=
    shifted_geometricPrefix_le beta hBetaNonneg hBetaLt t
  have hScaled :
      L * stepBound * shiftedGeometricPrefix beta t ≤
        L * stepBound * (beta / (1 - beta)) := by
    have hCoeffNonneg : 0 ≤ L * stepBound := mul_nonneg hLNonneg hStepNonneg
    gcongr
  calc
    driftError t
      ≤ beta ^ t * initialGradNorm + L * stepBound * shiftedGeometricPrefix beta t := hDriftGeom t
    _ ≤ beta ^ t * initialGradNorm + L * stepBound * (beta / (1 - beta)) := by
          linarith
    _ = beta ^ t * initialGradNorm + (beta / (1 - beta)) * L * stepBound := by
          ring

/--
Direct unrolling-style pointwise control on the canonical momentum error.
-/
private theorem momentumErrorNorm_le_unrolled
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.momentumErrorNorm t ≤
        S.beta ^ t * S.initialGradNorm
          + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
          + S.expectedNoise t := by
  have hDrift :
      ∀ t,
        ‖S.driftComponent t‖ ≤
          S.beta ^ t * S.initialGradNorm + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t := by
    have hTwoEtaNonneg : 0 ≤ 2 * S.eta := by
      nlinarith [S.eta_pos]
    have hcNonneg : 0 ≤ S.L * (2 * S.eta) := by
      exact mul_nonneg S.assumption3_fLocalSmoothness.nonneg hTwoEtaNonneg
    have hGradInc' :
        ∀ t, ‖S.grad (t + 1) - S.grad t‖ ≤ S.L * (2 * S.eta) := by
      intro t
      simpa [mul_assoc, mul_left_comm, mul_comm] using S.grad_increment_bound t
    exact S.norm_driftComponent_le hcNonneg hGradInc'
  intro t
  calc
    S.momentumErrorNorm t ≤ ‖S.driftComponent t‖ + ‖S.noiseComponent t‖ := by
      simpa [StochasticSteepestDescentGeometryContext.momentumErrorNorm] using
        S.norm_momentumError_le_drift_add_noise t
    _ ≤ ‖S.driftComponent t‖ + S.expectedNoise t := by
      gcongr
      exact S.noiseComponentNorm_le_expectedNoise t
    _ ≤ S.beta ^ t * S.initialGradNorm
          + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
          + S.expectedNoise t := by
            linarith [hDrift t]

/-- Pointwise momentum-error bound on the canonical momentum-error sequence. -/
theorem Corollary10PointwiseMomentumErrorBound
    (S : StochasticSteepestDescentGeometryContext Ω V)
    : ∀ t,
      S.momentumErrorNorm t ≤
        S.beta ^ t * S.initialGradNorm
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
  have hStepNonneg : 0 ≤ 2 * S.eta := by
    nlinarith [S.eta_pos]
  have hDriftCollapsed :
      ∀ t,
        S.beta ^ t * S.initialGradNorm + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
          ≤
            S.beta ^ t * S.initialGradNorm
              + (2 * S.beta / (1 - S.beta)) * S.L * S.eta := by
    intro t
    have h :=
      momentum_drift_bound_from_step_bound
        S.beta_nonneg S.beta_lt_one S.assumption3_fLocalSmoothness.nonneg hStepNonneg
        (driftError := fun t =>
          S.beta ^ t * S.initialGradNorm + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t)
        (by intro t; exact le_rfl) t
    calc
      S.beta ^ t * S.initialGradNorm + S.L * (2 * S.eta) * shiftedGeometricPrefix S.beta t
        ≤ S.beta ^ t * S.initialGradNorm + (S.beta / (1 - S.beta)) * S.L * (2 * S.eta) := h
      _ = S.beta ^ t * S.initialGradNorm + (2 * S.beta / (1 - S.beta)) * S.L * S.eta := by
            ring
  intro t
  have hUnrolled := momentumErrorNorm_le_unrolled S t
  have hDrift := hDriftCollapsed t
  have hNoise := S.expectedNoise_bound t
  linarith

/-- Averaged form of Corollary 10 over `t = 0, …, T - 1`. -/
theorem corollary10_average_momentumError_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.momentumErrorNorm t) / (T : ℝ) ≤
        (S.initialGradNorm * geometricPrefix S.beta T) / (T : ℝ)
          + (2 * S.beta / (1 - S.beta)) * S.L * S.eta
          + Real.sqrt ((1 - S.beta) / (1 + S.beta)) * Real.sqrt S.D * S.sigma
              / Real.sqrt S.batchSizeℝ := by
  exact average_momentumError_bound_of_pointwise
    S
    S.momentumErrorNorm
    (Corollary10PointwiseMomentumErrorBound S)

end Corollary10

end

end MlOptBoundsFormalization
