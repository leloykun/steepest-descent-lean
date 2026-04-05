import Mathlib
import SteepestDescentOptimizationBounds.StochasticProcessSupport
import SteepestDescentOptimizationBounds.DescentLemma

/-!
Minibatch-noise layer for the realized stochastic steepest-descent model.

Upstream dependencies:

- `StochasticProcessSupport.lean` provides the realized stochastic-gradient
  samples, the prefix conditional-expectation lemmas, and the local smooth
  proxy potential.

Downstream use:

- `MomentumBounds.lean` reuses the generic weighted-noise lemmas for the
  flattened momentum-noise process.
- `NesterovMomentumBounds.lean` uses the public minibatch-noise definitions and
  the expected minibatch-noise bound.
-/

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

open MeasureTheory
open ProbabilityTheory

noncomputable section

section PrivateHelpers

private lemma uniformBatchWeight_nonneg {b : ℕ} : 0 ≤ uniformBatchWeight b := by
  unfold uniformBatchWeight
  positivity

private lemma uniformBatchWeight_sum_eq_one {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b) = 1 := by
  have hbnz : (b : ℝ) ≠ 0 := by positivity
  calc
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b)
      = (b : ℝ) * uniformBatchWeight b := by simp [uniformBatchWeight]
    _ = (b : ℝ) * (1 / (b : ℝ)) := by simp [uniformBatchWeight]
    _ = 1 := by field_simp [hbnz]

private lemma uniformBatchWeight_sum_le_one {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b) ≤ 1 := by
  simp [uniformBatchWeight_sum_eq_one hb]

private lemma uniformBatchWeight_sq_sum_eq {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b ^ 2) = 1 / (b : ℝ) := by
  have hbnz : (b : ℝ) ≠ 0 := by positivity
  calc
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b ^ 2)
      = (b : ℝ) * uniformBatchWeight b ^ 2 := by simp [uniformBatchWeight]
    _ = (b : ℝ) * (1 / (b : ℝ)) ^ 2 := by simp [uniformBatchWeight]
    _ = 1 / (b : ℝ) := by field_simp [hbnz]

private lemma norm_sum_range_smul_le_of_nonneg_of_sum_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {α : ℕ → ℝ} {x : ℕ → E} {R : ℝ}
    (hα_nonneg : ∀ i < n, 0 ≤ α i)
    (hα_sum : Finset.sum (Finset.range n) α ≤ 1)
    (hx : ∀ i < n, ‖x i‖ ≤ R)
    (hR_nonneg : 0 ≤ R) :
    ‖Finset.sum (Finset.range n) (fun i => α i • x i)‖ ≤ R := by
  calc
    ‖Finset.sum (Finset.range n) (fun i => α i • x i)‖
      ≤ Finset.sum (Finset.range n) (fun i => ‖α i • x i‖) := norm_sum_le _ _
    _ = Finset.sum (Finset.range n) (fun i => α i * ‖x i‖) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (hα_nonneg i (Finset.mem_range.mp hi))]
    _ ≤ Finset.sum (Finset.range n) (fun i => α i * R) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact
            mul_le_mul_of_nonneg_left
              (hx i (Finset.mem_range.mp hi))
              (hα_nonneg i (Finset.mem_range.mp hi))
    _ = (Finset.sum (Finset.range n) α) * R := by
          rw [Finset.sum_mul]
    _ ≤ 1 * R := by
          exact mul_le_mul_of_nonneg_right hα_sum hR_nonneg
    _ = R := by ring

private lemma norm_sum_range_smul_le_of_nonneg_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α : ℕ → ℝ} {x : ℕ → E} {R : ℝ}
    (hk : k ≤ n)
    (hα_nonneg : ∀ i < n, 0 ≤ α i)
    (hα_sum : Finset.sum (Finset.range n) α ≤ 1)
    (hx : ∀ i < n, ‖x i‖ ≤ R)
    (hR_nonneg : 0 ≤ R) :
    ‖Finset.sum (Finset.range k) (fun i => α i • x i)‖ ≤ R := by
  have hα_nonneg_k : ∀ i < k, 0 ≤ α i := by
    intro i hi
    exact hα_nonneg i (lt_of_lt_of_le hi hk)
  have hα_sum_k : Finset.sum (Finset.range k) α ≤ 1 := by
    have hSubset : Finset.range k ⊆ Finset.range n := by
      intro i hi
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    have hLe :
        Finset.sum (Finset.range k) α ≤ Finset.sum (Finset.range n) α := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hSubset ?_
      intro i hiN _hiK
      exact hα_nonneg i (Finset.mem_range.mp hiN)
    linarith
  have hx_k : ∀ i < k, ‖x i‖ ≤ R := by
    intro i hi
    exact hx i (lt_of_lt_of_le hi hk)
  exact norm_sum_range_smul_le_of_nonneg_of_sum_le_one hα_nonneg_k hα_sum_k hx_k hR_nonneg

namespace Assumption4_LocalSmoothProxyPotential

private lemma potential_nonneg_of_mem_noiseRadius
    {V VDual : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    {pairing : ContinuousDualPairingContext VDual V}
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) (x : VDual)
    (hx : ‖x‖ ≤ P.noiseRadius) :
    0 ≤ P.potential x := by
  have h := P.norm_sq_le_two_potential_on_ball x hx
  nlinarith [sq_nonneg ‖x‖]

private lemma mirrorMap_norm_le_of_mem_noiseRadius
    {V VDual : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    {pairing : ContinuousDualPairingContext VDual V}
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) (x : VDual)
    (hx : ‖x‖ ≤ P.noiseRadius) :
    ‖P.mirrorMap x‖ ≤ P.D * ‖x‖ := by
  have h :=
    P.mirrorMap_local_lipschitz.bound
      (show ‖(0 : VDual)‖ ≤ P.noiseRadius by simpa using P.noiseRadius_nonneg)
      hx
  simpa [P.mirrorMap_zero] using h

end Assumption4_LocalSmoothProxyPotential

end PrivateHelpers

section GenericWeightedNoise

variable {Ω V VDual : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
variable [MeasurableSpace VDual] [BorelSpace VDual]
variable [SecondCountableTopology VDual] [CompleteSpace VDual]

omit [MeasurableSpace Ω] [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
/--
If a scalar-valued cross term is obtained by applying an `m`-measurable
continuous linear functional to a vector-valued noise term whose conditional
expectation given `m` vanishes, then the cross term has zero expectation.
-/
theorem integral_clm_apply_eq_zero_of_condexp_zero
    {m m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    (hm : m ≤ m0)
    [IsFiniteMeasure μ]
    {L : Ω → VDual →L[ℝ] ℝ} {ξ : Ω → VDual}
    (hL : AEStronglyMeasurable[m] L μ)
    (hLξ : Integrable (fun ω => L ω (ξ ω)) μ)
    (hξ : Integrable ξ μ)
    (hCondZero : μ[ξ | m] =ᵐ[μ] 0) :
    ∫ ω, L ω (ξ ω) ∂μ = 0 := by
  let B : (VDual →L[ℝ] ℝ) →L[ℝ] VDual →L[ℝ] ℝ :=
    ContinuousLinearMap.flip
      (ContinuousLinearMap.apply ℝ ℝ : VDual →L[ℝ] (VDual →L[ℝ] ℝ) →L[ℝ] ℝ)
  have hPull :
      μ[fun ω ↦ L ω (ξ ω) | m] =ᵐ[μ] fun ω ↦ L ω (μ[ξ | m] ω) := by
    simpa [B] using
      (MeasureTheory.condExp_bilin_of_aestronglyMeasurable_left
        (μ := μ) (m := m) B hL (by simpa [B] using hLξ) hξ)
  have hCondCrossZero : μ[fun ω ↦ L ω (ξ ω) | m] =ᵐ[μ] 0 := by
    refine hPull.trans ?_
    filter_upwards [hCondZero] with ω hω
    simp [hω]
  calc
    ∫ ω, L ω (ξ ω) ∂μ = ∫ ω, (μ[fun ω ↦ L ω (ξ ω) | m]) ω ∂μ := by
      symm
      have hSet :
          ∫ ω in Set.univ, (μ[fun ω ↦ L ω (ξ ω) | m]) ω ∂μ =
            ∫ ω in Set.univ, L ω (ξ ω) ∂μ := by
        exact
          MeasureTheory.setIntegral_condExp
            (m := m) (m₀ := m0) (μ := μ) (f := fun ω ↦ L ω (ξ ω))
            hm hLξ MeasurableSet.univ
      simpa using hSet
    _ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae hCondCrossZero
    _ = 0 := by simp

/--
On a probability space, the first moment of `‖X‖` is bounded by the square root
of its second moment.
-/
theorem integral_norm_le_sqrt_second_moment
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E}
    (hSq : Integrable (fun ω => ‖f ω‖ ^ 2) μ) :
    ∫ ω, ‖f ω‖ ∂μ ≤ Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  let g : Ω → ℝ := fun ω => ‖f ω‖
  have hgAesm : AEStronglyMeasurable g μ := by
    have hSqAesm : AEStronglyMeasurable (fun ω => ‖f ω‖ ^ 2) μ := hSq.aestronglyMeasurable
    have hSqrtAesm :
        AEStronglyMeasurable (fun ω => Real.sqrt (‖f ω‖ ^ 2)) μ :=
      hSqAesm.aemeasurable.sqrt.aestronglyMeasurable
    refine AEStronglyMeasurable.congr hSqrtAesm ?_
    filter_upwards with ω
    simp [g]
  have hgMemLp : MemLp g 2 μ := by
    refine (memLp_two_iff_integrable_sq hgAesm).2 ?_
    simpa [g] using hSq
  have hNormMemLp : MemLp (fun ω => ‖f ω‖) (ENNReal.ofReal 2) μ := by
    simpa [g] using hgMemLp
  have hOneMemLp : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_const 1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ)
  have hHolder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun ω => norm_nonneg (f ω))
      (Filter.Eventually.of_forall fun _ => show (0 : ℝ) ≤ 1 by norm_num)
      hNormMemLp hOneMemLp
  calc
    ∫ ω, ‖f ω‖ ∂μ = ∫ ω, g ω * 1 ∂μ := by simp [g]
    _ ≤
        (∫ ω, g ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          * (∫ ω, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
    _ = (∫ ω, ‖f ω‖ ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by simp [g]
    _ = Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by rw [Real.sqrt_eq_rpow]

/-- Weighted partial sum used in the generic Lemma-5-style noise bounds. -/
def weightedPartialSum
    (α : ℕ → ℝ) (ξ : ℕ → Ω → VDual) (k : ℕ) (ω : Ω) : VDual :=
  Finset.sum (Finset.range k) (fun i => α i • ξ i ω)

omit [MeasurableSpace Ω] [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weightedPartialSum_norm_le_noiseRadius_of_mem
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ}
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    {ω : Ω}
    (sample_norm_le_noiseRadius : ∀ i < n, ‖ξ i ω‖ ≤ B.noiseRadius) :
    ∀ k, k ≤ n → ‖weightedPartialSum α ξ k ω‖ ≤ B.noiseRadius := by
  intro k hk
  exact
    norm_sum_range_smul_le_of_nonneg_prefix
      hk coeff_nonneg coeff_sum_le_one sample_norm_le_noiseRadius B.noiseRadius_nonneg

omit [MeasurableSpace Ω] [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weighted_smooth_step
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ}
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1) :
    ∀ k, k < n →
      ∀ ω,
      (∀ i, i < n → ‖ξ i ω‖ ≤ B.noiseRadius) →
        B.potential (weightedPartialSum α ξ (k + 1) ω) ≤
          B.potential (weightedPartialSum α ξ k ω)
            + α k
                * P.toLinear
                    (B.mirrorMap (weightedPartialSum α ξ k ω))
                    (ξ k ω)
            + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 := by
  intro k hk ω hξ
  let x : VDual := weightedPartialSum α ξ k ω
  have hx :
      ‖x‖ ≤ B.noiseRadius := by
    exact weightedPartialSum_norm_le_noiseRadius_of_mem P B coeff_nonneg coeff_sum_le_one
      (fun i hi => hξ i hi) k (Nat.le_of_lt hk)
  have hNext :
      ‖x + α k • ξ k ω‖ ≤ B.noiseRadius := by
    have hNext' :=
      weightedPartialSum_norm_le_noiseRadius_of_mem P B coeff_nonneg coeff_sum_le_one
        (fun i hi => hξ i hi) (k + 1) (Nat.succ_le_of_lt hk)
    simpa [weightedPartialSum, x, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      using hNext'
  have h :=
    step_upper_of_LSmoothOnClosedBallUnderPair
      P
      (f := B.potential)
      (grad := B.mirrorMap)
      (L := B.D)
      (R := B.noiseRadius)
      (α := α k)
      B.potential_fderiv_eq
      B.mirrorMap_local_lipschitz
      (coeff_nonneg k hk)
      hx
      hNext
  simpa [weightedPartialSum, x, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    using h

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem sample_norm_le_noiseRadius_all_ae
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} {ξ : ℕ → Ω → VDual} {n : ℕ}
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius) :
    ∀ᵐ ω ∂μ, ∀ i, i < n → ‖ξ i ω‖ ≤ B.noiseRadius := by
  induction' n with n ih
  · exact Filter.Eventually.of_forall (by
      intro ω i hi
      exact (Nat.not_lt_zero _ hi).elim)
  · have hPrev :
        ∀ᵐ ω ∂μ, ∀ i, i < n → ‖ξ i ω‖ ≤ B.noiseRadius := by
      refine ih ?_
      intro i hi
      exact sample_norm_le_noiseRadius_ae i (Nat.lt_trans hi (Nat.lt_succ_self n))
    have hLast : ∀ᵐ ω ∂μ, ‖ξ n ω‖ ≤ B.noiseRadius :=
      sample_norm_le_noiseRadius_ae n (Nat.lt_succ_self n)
    filter_upwards [hPrev, hLast] with ω hPrevω hLastω
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | rfl
    · exact hPrevω i hi'
    · exact hLastω

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weightedPartialSum_norm_le_noiseRadius_ae
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ}
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius) :
    ∀ k, k ≤ n → ∀ᵐ ω ∂μ, ‖weightedPartialSum α ξ k ω‖ ≤ B.noiseRadius := by
  intro k hk
  have hAll :=
    sample_norm_le_noiseRadius_all_ae
      (P := P) (B := B) (μ := μ) (ξ := ξ) (n := n) sample_norm_le_noiseRadius_ae
  filter_upwards [hAll] with ω hω
  exact
    weightedPartialSum_norm_le_noiseRadius_of_mem
      P B coeff_nonneg coeff_sum_le_one
      (fun i hi => hω i hi) k hk

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weighted_smooth_step_ae
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ}
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius) :
    ∀ k, k < n → ∀ᵐ ω ∂μ,
      B.potential (weightedPartialSum α ξ (k + 1) ω) ≤
        B.potential (weightedPartialSum α ξ k ω)
          + α k
              * P.toLinear
                  (B.mirrorMap (weightedPartialSum α ξ k ω))
                  (ξ k ω)
          + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 := by
  intro k hk
  have hAll :=
    sample_norm_le_noiseRadius_all_ae
      (P := P) (B := B) (μ := μ) (ξ := ξ) (n := n) sample_norm_le_noiseRadius_ae
  filter_upwards [hAll] with ω hω
  exact weighted_smooth_step P B coeff_nonneg coeff_sum_le_one k hk ω hω

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weighted_partialSum_stronglyMeasurable_any
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ}
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i)) :
    ∀ k, StronglyMeasurable (fun ω => weightedPartialSum α ξ k ω)
  | 0 => by
      simpa [weightedPartialSum] using
        (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω => (0 : VDual)))
  | k + 1 => by
      have hk : StronglyMeasurable (fun ω => weightedPartialSum α ξ k ω) :=
        weighted_partialSum_stronglyMeasurable_any sample_stronglyMeasurable k
      have hCurr :
          StronglyMeasurable (fun ω => α k • ξ k ω) := by
        simpa using (sample_stronglyMeasurable k).const_smul (α k)
      convert hk.add hCurr using 1
      ext ω
      simp [weightedPartialSum, Finset.sum_range_succ, add_comm]

omit [NormedSpace ℝ VDual] [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem integrable_norm_mul_of_sq_integrable
    {μ : Measure Ω} {f g : Ω → VDual}
    (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g)
    (hf_sq : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hg_sq : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖f ω‖ * ‖g ω‖) μ := by
  have hMeas :
      AEStronglyMeasurable (fun ω => ‖f ω‖ * ‖g ω‖) μ := by
    exact (hf.norm.mul hg.norm).aestronglyMeasurable
  have hDom :
      Integrable (fun ω => ((‖f ω‖ ^ 2 + ‖g ω‖ ^ 2) / 2)) μ := by
    simpa [div_eq_mul_inv, Pi.add_apply, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
      using (hf_sq.add hg_sq).const_mul (1 / 2 : ℝ)
  refine Integrable.mono' hDom hMeas ?_
  filter_upwards with ω
  have hYoung : ‖f ω‖ * ‖g ω‖ ≤ (‖f ω‖ ^ 2 + ‖g ω‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖f ω‖ - ‖g ω‖)]
  have hLeftNonneg : 0 ≤ ‖f ω‖ * ‖g ω‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hRightNonneg : 0 ≤ (‖f ω‖ ^ 2 + ‖g ω‖ ^ 2) / 2 := by
    positivity
  simpa [Real.norm_of_nonneg hLeftNonneg, Real.norm_of_nonneg hRightNonneg] using hYoung

omit [NormedSpace ℝ VDual] [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem integrable_norm_of_sq_integrable
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → VDual}
    (hf : StronglyMeasurable f)
    (hf_sq : Integrable (fun ω => ‖f ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖f ω‖) μ := by
  have hConst : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  refine Integrable.mono' ((hf_sq.add hConst).const_mul (1 / 2 : ℝ))
    hf.norm.aestronglyMeasurable ?_
  filter_upwards with ω
  have hYoung : ‖f ω‖ ≤ (‖f ω‖ ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (‖f ω‖ - 1)]
  have hRightNonneg : 0 ≤ (‖f ω‖ ^ 2 + 1) / 2 := by positivity
  simpa [div_eq_mul_inv, mul_comm, Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg hRightNonneg] using hYoung

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weighted_partialSum_sq_integrable
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {k : ℕ}
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (potential_integrable :
      Integrable (fun ω => B.potential (weightedPartialSum α ξ k ω)) μ)
    (partial_norm_le_noiseRadius_ae :
      ∀ᵐ ω ∂μ, ‖weightedPartialSum α ξ k ω‖ ≤ B.noiseRadius) :
    Integrable (fun ω => ‖weightedPartialSum α ξ k ω‖ ^ 2) μ := by
  have hScaled :
      Integrable (fun ω => (2 : ℝ) * B.potential (weightedPartialSum α ξ k ω)) μ := by
    simpa using potential_integrable.const_mul (2 : ℝ)
  have hMeas :
      AEStronglyMeasurable (fun ω => ‖weightedPartialSum α ξ k ω‖ ^ 2) μ := by
    have hNormMeas :
        Measurable (fun ω => ‖weightedPartialSum α ξ k ω‖) :=
      (weighted_partialSum_stronglyMeasurable_any sample_stronglyMeasurable k).norm.measurable
    exact (hNormMeas.pow_const 2).aestronglyMeasurable
  refine Integrable.mono' hScaled hMeas ?_
  filter_upwards [partial_norm_le_noiseRadius_ae] with ω hω
  have hSqLe :=
    B.norm_sq_le_two_potential_on_ball (weightedPartialSum α ξ k ω) hω
  have hLeftNonneg : 0 ≤ ‖weightedPartialSum α ξ k ω‖ ^ 2 := sq_nonneg _
  have hRightNonneg : 0 ≤ 2 * B.potential (weightedPartialSum α ξ k ω) := by
    nlinarith [hSqLe]
  simpa [Real.norm_of_nonneg hLeftNonneg, Real.norm_of_nonneg hRightNonneg] using hSqLe

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] [CompleteSpace VDual] in
private theorem weighted_linearized_cross_integrable
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {k : ℕ}
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (partial_sq_integrable :
      Integrable (fun ω => ‖weightedPartialSum α ξ k ω‖ ^ 2) μ)
    (sample_sq_integrable :
      Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (partial_norm_le_noiseRadius_ae :
      ∀ᵐ ω ∂μ, ‖weightedPartialSum α ξ k ω‖ ≤ B.noiseRadius) :
    Integrable
      (fun ω =>
        P.toLinear
          (B.mirrorMap (weightedPartialSum α ξ k ω))
          (ξ k ω)) μ := by
  let Pflip : (VDual →L[ℝ] ℝ) →L[ℝ] VDual →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)
  have hPartial :
      StronglyMeasurable (fun ω => weightedPartialSum α ξ k ω) :=
    weighted_partialSum_stronglyMeasurable_any sample_stronglyMeasurable k
  have hMirror :
      StronglyMeasurable
        (fun ω => B.mirrorMap (weightedPartialSum α ξ k ω)) :=
    B.mirrorMap_continuous.comp_stronglyMeasurable hPartial
  let coeffFun : Ω → VDual →L[ℝ] ℝ := fun ω =>
    P.toLinear (B.mirrorMap (weightedPartialSum α ξ k ω))
  have hCoeff :
      AEStronglyMeasurable coeffFun μ :=
    (P.toLinear.continuous.comp_stronglyMeasurable hMirror).aestronglyMeasurable
  have hXi : AEStronglyMeasurable (ξ k) μ :=
    (sample_stronglyMeasurable k).aestronglyMeasurable
  have hMeas :
      AEStronglyMeasurable (fun ω => coeffFun ω (ξ k ω)) μ := by
    simpa [Pflip, coeffFun] using Pflip.aestronglyMeasurable_comp₂ hCoeff hXi
  have hProd :
      Integrable
        (fun ω => ‖weightedPartialSum α ξ k ω‖ * ‖ξ k ω‖) μ :=
    integrable_norm_mul_of_sq_integrable
      hPartial (sample_stronglyMeasurable k) partial_sq_integrable sample_sq_integrable
  have hDom :
      Integrable
        (fun ω => B.D * (‖weightedPartialSum α ξ k ω‖ * ‖ξ k ω‖)) μ :=
    hProd.const_mul B.D
  refine Integrable.mono' hDom hMeas ?_
  filter_upwards [partial_norm_le_noiseRadius_ae] with ω hω
  have hMirrorBound :
      ‖B.mirrorMap (weightedPartialSum α ξ k ω)‖ ≤
        B.D * ‖weightedPartialSum α ξ k ω‖ :=
    B.mirrorMap_norm_le_of_mem_noiseRadius (weightedPartialSum α ξ k ω) hω
  calc
    ‖coeffFun ω (ξ k ω)‖
      ≤ ‖coeffFun ω‖ * ‖ξ k ω‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖B.mirrorMap (weightedPartialSum α ξ k ω)‖ * ‖ξ k ω‖ := by
          gcongr
          exact P.opNorm_le _
    _ ≤ (B.D * ‖weightedPartialSum α ξ k ω‖) * ‖ξ k ω‖ := by
          gcongr
    _ = B.D * (‖weightedPartialSum α ξ k ω‖ * ‖ξ k ω‖) := by ring

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
private theorem weighted_cross_term_zero_at
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n k : ℕ}
    (pastSigma : ℕ → MeasurableSpace Ω)
    (pastSigma_le : ∀ i, pastSigma i ≤ inferInstanceAs (MeasurableSpace Ω))
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (sample_integrable : ∀ i, i < n → Integrable (ξ i) μ)
    (coeff_measurable :
      ∀ i, i < n →
        AEStronglyMeasurable[pastSigma i]
          (fun ω => P.toLinear (B.mirrorMap (weightedPartialSum α ξ i ω))) μ)
    (cond_zero :
      ∀ i, i < n → μ[ξ i | pastSigma i] =ᵐ[μ] 0)
    (partial_sq_integrable :
      Integrable (fun ω => ‖weightedPartialSum α ξ k ω‖ ^ 2) μ)
    (sample_sq_integrable :
      Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (partial_norm_le_noiseRadius_ae :
      ∀ᵐ ω ∂μ, ‖weightedPartialSum α ξ k ω‖ ≤ B.noiseRadius)
    (hk : k < n) :
    Integrable
        (fun ω =>
          α k
            * P.toLinear
                (B.mirrorMap (weightedPartialSum α ξ k ω))
                (ξ k ω)) μ ∧
      ∫ ω,
          α k
            * P.toLinear
                (B.mirrorMap (weightedPartialSum α ξ k ω))
                (ξ k ω) ∂μ = 0 := by
  have hInt :
      Integrable
        (fun ω =>
          P.toLinear
            (B.mirrorMap (weightedPartialSum α ξ k ω))
            (ξ k ω)) μ := by
    simpa using
      weighted_linearized_cross_integrable P B
        sample_stronglyMeasurable partial_sq_integrable sample_sq_integrable
        partial_norm_le_noiseRadius_ae
  have hZero :
      ∫ ω,
          P.toLinear
            (B.mirrorMap (weightedPartialSum α ξ k ω))
            (ξ k ω) ∂μ = 0 :=
    integral_clm_apply_eq_zero_of_condexp_zero
      (μ := μ)
      (m := pastSigma k)
      (pastSigma_le k)
      (hL := coeff_measurable k hk)
      (hLξ := hInt)
      (hξ := sample_integrable k hk)
      (hCondZero := cond_zero k hk)
  refine ⟨hInt.const_mul (α k), ?_⟩
  calc
    ∫ ω,
        α k
          * P.toLinear
              (B.mirrorMap (weightedPartialSum α ξ k ω))
              (ξ k ω) ∂μ
      = α k
          * ∫ ω,
              P.toLinear
                (B.mirrorMap (weightedPartialSum α ξ k ω))
                (ξ k ω) ∂μ := by
                  rw [MeasureTheory.integral_const_mul]
    _ = 0 := by simp [hZero]

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
private theorem weighted_partial_potential_sq_integrable_and_bound
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ} {sigma : ℝ}
    (pastSigma : ℕ → MeasurableSpace Ω)
    (pastSigma_le : ∀ i, pastSigma i ≤ inferInstanceAs (MeasurableSpace Ω))
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (sample_integrable : ∀ i, i < n → Integrable (ξ i) μ)
    (coeff_measurable :
      ∀ i, i < n →
        AEStronglyMeasurable[pastSigma i]
          (fun ω => P.toLinear (B.mirrorMap (weightedPartialSum α ξ i ω))) μ)
    (cond_zero :
      ∀ i, i < n → μ[ξ i | pastSigma i] =ᵐ[μ] 0)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius)
    (second_moment_bound :
      ∀ i, i < n →
        Integrable (fun ω => ‖ξ i ω‖ ^ 2) μ ∧
          ∫ ω, ‖ξ i ω‖ ^ 2 ∂μ ≤ sigma ^ 2) :
    ∀ k, k ≤ n →
      Integrable (fun ω => B.potential (weightedPartialSum α ξ k ω)) μ ∧
      Integrable (fun ω => ‖weightedPartialSum α ξ k ω‖ ^ 2) μ ∧
      ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ ≤
        (B.D / 2) * sigma ^ 2 * Finset.sum (Finset.range k) (fun i => (α i) ^ 2) := by
  intro k hk
  induction' k with k ih
  · refine ⟨?_, ?_, ?_⟩
    · have hZeroReal : Integrable (fun _ : Ω => (0 : ℝ)) μ := by simp
      convert hZeroReal using 1
      ext ω
      simp [weightedPartialSum, B.potential_zero]
    · have hZeroReal : Integrable (fun _ : Ω => (0 : ℝ)) μ := by simp
      convert hZeroReal using 1
      ext ω
      simp [weightedPartialSum]
    · simp [weightedPartialSum, B.potential_zero]
  · have hk' : k < n := Nat.lt_of_succ_le hk
    rcases ih (Nat.le_of_lt hk') with ⟨hPrevPotInt, hPrevSqInt, hPrevBound⟩
    have hVarInt := (second_moment_bound k hk').1
    have hVarBound := (second_moment_bound k hk').2
    have hPrevBall :=
      weightedPartialSum_norm_le_noiseRadius_ae
        P B coeff_nonneg coeff_sum_le_one sample_norm_le_noiseRadius_ae k (Nat.le_of_lt hk')
    have hNextBall :=
      weightedPartialSum_norm_le_noiseRadius_ae
        P B coeff_nonneg coeff_sum_le_one sample_norm_le_noiseRadius_ae
        (k + 1) (Nat.succ_le_of_lt hk')
    have hCross :=
      weighted_cross_term_zero_at
        P B pastSigma pastSigma_le sample_stronglyMeasurable sample_integrable
        coeff_measurable cond_zero hPrevSqInt hVarInt hPrevBall hk'
    have hCrossInt := hCross.1
    have hCrossZero := hCross.2
    have hSmooth :
        ∀ᵐ ω ∂μ,
          B.potential (weightedPartialSum α ξ (k + 1) ω) ≤
            B.potential (weightedPartialSum α ξ k ω)
              + α k
                  * P.toLinear
                      (B.mirrorMap (weightedPartialSum α ξ k ω))
                      (ξ k ω)
              + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 := by
      exact
        weighted_smooth_step_ae
          P B coeff_nonneg coeff_sum_le_one sample_norm_le_noiseRadius_ae k hk'
    have hScaleNonneg : 0 ≤ (B.D / 2) * (α k) ^ 2 := by
      have hDhalf : 0 ≤ B.D / 2 := by nlinarith [B.D_nonneg]
      exact mul_nonneg hDhalf (sq_nonneg _)
    let f : Ω → ℝ := fun ω => B.potential (weightedPartialSum α ξ k ω)
    let g : Ω → ℝ := fun ω =>
      α k * P.toLinear (B.mirrorMap (weightedPartialSum α ξ k ω)) (ξ k ω)
    let h : Ω → ℝ := fun ω => ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2
    have hf : Integrable f μ := by simpa [f] using hPrevPotInt
    have hg : Integrable g μ := by simpa [g] using hCrossInt
    have hh : Integrable h μ := by
      simpa [h] using hVarInt.const_mul ((B.D / 2) * (α k) ^ 2)
    have hAbsRhsInt :
        Integrable
          (fun ω =>
            B.potential (weightedPartialSum α ξ k ω)
              + ‖α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω)‖
              + ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2) μ := by
      simpa [f, g, h, add_assoc] using hf.add (hg.norm.add hh)
    have hNextMeas :
        AEStronglyMeasurable
          (fun ω => B.potential (weightedPartialSum α ξ (k + 1) ω)) μ := by
      exact B.potential_continuous.comp_aestronglyMeasurable
        ((weighted_partialSum_stronglyMeasurable_any sample_stronglyMeasurable (k + 1)).aestronglyMeasurable)
    have hNextPotInt :
        Integrable (fun ω => B.potential (weightedPartialSum α ξ (k + 1) ω)) μ := by
      refine Integrable.mono' hAbsRhsInt hNextMeas ?_
      filter_upwards [hSmooth, hPrevBall, hNextBall] with ω hω hPrevω hNextω
      have hPotNonnegNext :
          0 ≤ B.potential (weightedPartialSum α ξ (k + 1) ω) :=
        B.potential_nonneg_of_mem_noiseRadius (weightedPartialSum α ξ (k + 1) ω) hNextω
      have hPotNonneg :
          0 ≤ B.potential (weightedPartialSum α ξ k ω) :=
        B.potential_nonneg_of_mem_noiseRadius (weightedPartialSum α ξ k ω) hPrevω
      have hVarNonneg :
          0 ≤ ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 := by
        exact mul_nonneg hScaleNonneg (sq_nonneg _)
      have hDom :
          B.potential (weightedPartialSum α ξ (k + 1) ω) ≤
            B.potential (weightedPartialSum α ξ k ω)
              + ‖α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω)‖
              + ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 := by
        have hAbs :
            α k
              * P.toLinear (B.mirrorMap (weightedPartialSum α ξ k ω)) (ξ k ω)
            ≤ ‖α k
                * P.toLinear (B.mirrorMap (weightedPartialSum α ξ k ω)) (ξ k ω)‖ := by
          exact le_abs_self _
        linarith
      have hRhsNonneg :
          0 ≤
            B.potential (weightedPartialSum α ξ k ω)
              + ‖α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω)‖
              + ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 := by
        positivity
      simpa [Real.norm_of_nonneg hPotNonnegNext, Real.norm_of_nonneg hRhsNonneg] using hDom
    have hNextSqInt :
        Integrable (fun ω => ‖weightedPartialSum α ξ (k + 1) ω‖ ^ 2) μ :=
      weighted_partialSum_sq_integrable
        P B sample_stronglyMeasurable hNextPotInt hNextBall
    have hRhsInt :
        Integrable
          (fun ω =>
            B.potential (weightedPartialSum α ξ k ω)
              + α k
                  * P.toLinear
                      (B.mirrorMap (weightedPartialSum α ξ k ω))
                      (ξ k ω)
              + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2) μ := by
      simpa [f, g, h, add_assoc] using hf.add (hg.add hh)
    have hMono :
        ∫ ω, B.potential (weightedPartialSum α ξ (k + 1) ω) ∂μ ≤
          ∫ ω,
            B.potential (weightedPartialSum α ξ k ω)
              + α k
                  * P.toLinear
                      (B.mirrorMap (weightedPartialSum α ξ k ω))
                      (ξ k ω)
              + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 ∂μ := by
      exact integral_mono_ae hNextPotInt hRhsInt hSmooth
    have hSplitIntegral :
        ∫ ω,
            B.potential (weightedPartialSum α ξ k ω)
              + α k
                  * P.toLinear
                      (B.mirrorMap (weightedPartialSum α ξ k ω))
                      (ξ k ω)
              + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 ∂μ
          =
            ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ
              + ∫ ω,
                  α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω) ∂μ
              + ∫ ω, ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 ∂μ := by
      have hAdd1 :
          ∫ ω, (f + g + h) ω ∂μ =
            ∫ ω, (f + g) ω ∂μ + ∫ ω, h ω ∂μ := by
        simpa [Pi.add_apply] using
          (integral_add (hf.add hg) hh : ∫ ω, ((f + g) + h) ω ∂μ = _)
      have hAdd2 :
          ∫ ω, (f + g) ω ∂μ =
            ∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ := by
        simpa [Pi.add_apply] using
          (integral_add hf hg : ∫ ω, (f + g) ω ∂μ = _)
      calc
        ∫ ω,
            B.potential (weightedPartialSum α ξ k ω)
              + α k
                  * P.toLinear
                      (B.mirrorMap (weightedPartialSum α ξ k ω))
                      (ξ k ω)
              + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 ∂μ
          = ∫ ω, (f + g + h) ω ∂μ := by simp [f, g, h, add_assoc]
        _ = ∫ ω, (f + g) ω ∂μ + ∫ ω, h ω ∂μ := hAdd1
        _ = (∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ) + ∫ ω, h ω ∂μ := by rw [hAdd2]
        _ = ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ
              + ∫ ω,
                  α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω) ∂μ
              + ∫ ω, ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 ∂μ := by
                simp [f, g, h]
    have hVarIntegral :
        ∫ ω, ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 ∂μ =
          (B.D / 2) * (α k) ^ 2 * ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ := by
      rw [integral_const_mul]
    have hNextBound :
        ∫ ω, B.potential (weightedPartialSum α ξ (k + 1) ω) ∂μ ≤
          (B.D / 2) * sigma ^ 2 * Finset.sum (Finset.range (k + 1)) (fun i => (α i) ^ 2) := by
      calc
        ∫ ω, B.potential (weightedPartialSum α ξ (k + 1) ω) ∂μ
          ≤ ∫ ω,
              B.potential (weightedPartialSum α ξ k ω)
                + α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω)
                + (B.D / 2) * (α k) ^ 2 * ‖ξ k ω‖ ^ 2 ∂μ := hMono
        _ = ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ
              + ∫ ω,
                  α k
                    * P.toLinear
                        (B.mirrorMap (weightedPartialSum α ξ k ω))
                        (ξ k ω) ∂μ
              + ∫ ω, ((B.D / 2) * (α k) ^ 2) * ‖ξ k ω‖ ^ 2 ∂μ := hSplitIntegral
        _ = ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ
              + 0
              + (B.D / 2) * (α k) ^ 2 * ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ := by
                rw [hCrossZero, hVarIntegral]
        _ ≤ ∫ ω, B.potential (weightedPartialSum α ξ k ω) ∂μ
              + 0
              + (B.D / 2) * (α k) ^ 2 * sigma ^ 2 := by
                gcongr
        _ ≤ (B.D / 2) * sigma ^ 2 * Finset.sum (Finset.range k) (fun i => (α i) ^ 2)
              + 0
              + (B.D / 2) * (α k) ^ 2 * sigma ^ 2 := by
                gcongr
        _ = (B.D / 2) * sigma ^ 2 * Finset.sum (Finset.range (k + 1)) (fun i => (α i) ^ 2) := by
              rw [Finset.sum_range_succ]
              ring
    exact ⟨hNextPotInt, hNextSqInt, hNextBound⟩

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
/-- Square-integrability of a weighted centered-noise sum on the noise ball. -/
theorem weighted_noise_sq_integrable
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ} {sigma : ℝ}
    (pastSigma : ℕ → MeasurableSpace Ω)
    (pastSigma_le : ∀ i, pastSigma i ≤ inferInstanceAs (MeasurableSpace Ω))
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (sample_integrable : ∀ i, i < n → Integrable (ξ i) μ)
    (coeff_measurable :
      ∀ i, i < n →
        AEStronglyMeasurable[pastSigma i]
          (fun ω => P.toLinear (B.mirrorMap (weightedPartialSum α ξ i ω))) μ)
    (cond_zero :
      ∀ i, i < n → μ[ξ i | pastSigma i] =ᵐ[μ] 0)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius)
    (second_moment_bound :
      ∀ i, i < n →
        Integrable (fun ω => ‖ξ i ω‖ ^ 2) μ ∧
          ∫ ω, ‖ξ i ω‖ ^ 2 ∂μ ≤ sigma ^ 2) :
    Integrable (fun ω => ‖weightedPartialSum α ξ n ω‖ ^ 2) μ := by
  exact
    (weighted_partial_potential_sq_integrable_and_bound
      P B pastSigma pastSigma_le coeff_nonneg coeff_sum_le_one sample_stronglyMeasurable
      sample_integrable coeff_measurable cond_zero sample_norm_le_noiseRadius_ae
      second_moment_bound n le_rfl).2.1

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
/-- First-moment integrability of a weighted centered-noise sum. -/
theorem weighted_noise_norm_integrable
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ} {sigma : ℝ}
    (pastSigma : ℕ → MeasurableSpace Ω)
    (pastSigma_le : ∀ i, pastSigma i ≤ inferInstanceAs (MeasurableSpace Ω))
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (sample_integrable : ∀ i, i < n → Integrable (ξ i) μ)
    (coeff_measurable :
      ∀ i, i < n →
        AEStronglyMeasurable[pastSigma i]
          (fun ω => P.toLinear (B.mirrorMap (weightedPartialSum α ξ i ω))) μ)
    (cond_zero :
      ∀ i, i < n → μ[ξ i | pastSigma i] =ᵐ[μ] 0)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius)
    (second_moment_bound :
      ∀ i, i < n →
        Integrable (fun ω => ‖ξ i ω‖ ^ 2) μ ∧
          ∫ ω, ‖ξ i ω‖ ^ 2 ∂μ ≤ sigma ^ 2) :
    Integrable (fun ω => ‖weightedPartialSum α ξ n ω‖) μ := by
  exact
    integrable_norm_of_sq_integrable
      (weighted_partialSum_stronglyMeasurable_any sample_stronglyMeasurable n)
      (weighted_noise_sq_integrable
        P B pastSigma pastSigma_le coeff_nonneg coeff_sum_le_one sample_stronglyMeasurable
        sample_integrable coeff_measurable cond_zero sample_norm_le_noiseRadius_ae
        second_moment_bound)

omit [MeasurableSpace VDual] [BorelSpace VDual]
  [SecondCountableTopology VDual] in
/-- First-moment bound for a weighted sum of centered noises on the noise ball. -/
theorem weighted_noise_first_moment_bound
    (P : ContinuousDualPairingContext VDual V)
    (B : Assumption4_LocalSmoothProxyPotential V VDual P)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ω → VDual} {α : ℕ → ℝ} {n : ℕ} {sigma : ℝ}
    (pastSigma : ℕ → MeasurableSpace Ω)
    (pastSigma_le : ∀ i, pastSigma i ≤ inferInstanceAs (MeasurableSpace Ω))
    (coeff_nonneg : ∀ i < n, 0 ≤ α i)
    (coeff_sum_le_one : Finset.sum (Finset.range n) α ≤ 1)
    (sample_stronglyMeasurable : ∀ i, StronglyMeasurable (ξ i))
    (sample_integrable : ∀ i, i < n → Integrable (ξ i) μ)
    (coeff_measurable :
      ∀ i, i < n →
        AEStronglyMeasurable[pastSigma i]
          (fun ω => P.toLinear (B.mirrorMap (weightedPartialSum α ξ i ω))) μ)
    (cond_zero :
      ∀ i, i < n → μ[ξ i | pastSigma i] =ᵐ[μ] 0)
    (sample_norm_le_noiseRadius_ae :
      ∀ i, i < n → ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ B.noiseRadius)
    (second_moment_bound :
      ∀ i, i < n →
        Integrable (fun ω => ‖ξ i ω‖ ^ 2) μ ∧
          ∫ ω, ‖ξ i ω‖ ^ 2 ∂μ ≤ sigma ^ 2) :
    ∫ ω, ‖weightedPartialSum α ξ n ω‖ ∂μ ≤
      Real.sqrt (B.D * sigma ^ 2 * Finset.sum (Finset.range n) (fun i => (α i) ^ 2)) := by
  let hAll :=
    weighted_partial_potential_sq_integrable_and_bound
      P B pastSigma pastSigma_le coeff_nonneg coeff_sum_le_one sample_stronglyMeasurable
      sample_integrable coeff_measurable cond_zero sample_norm_le_noiseRadius_ae
      second_moment_bound
  have hSqInt :
      Integrable (fun ω => ‖weightedPartialSum α ξ n ω‖ ^ 2) μ :=
    (hAll n le_rfl).2.1
  have hFirst :=
    integral_norm_le_sqrt_second_moment
      (μ := μ) (f := fun ω => weightedPartialSum α ξ n ω) hSqInt
  have hSecond :
      ∫ ω, ‖weightedPartialSum α ξ n ω‖ ^ 2 ∂μ ≤
        B.D * sigma ^ 2 * Finset.sum (Finset.range n) (fun i => (α i) ^ 2) := by
    have hFinal := hAll n le_rfl
    have hFinalPotInt := hFinal.1
    have hFinalBound := hFinal.2.2
    have hFinalBall :=
      weightedPartialSum_norm_le_noiseRadius_ae
        P B coeff_nonneg coeff_sum_le_one sample_norm_le_noiseRadius_ae n le_rfl
    have hScaled :
        Integrable (fun ω => 2 * B.potential (weightedPartialSum α ξ n ω)) μ := by
      simpa using hFinalPotInt.const_mul 2
    have hMono :
        ∫ ω, ‖weightedPartialSum α ξ n ω‖ ^ 2 ∂μ ≤
          ∫ ω, 2 * B.potential (weightedPartialSum α ξ n ω) ∂μ := by
      refine integral_mono_ae hFinal.2.1 hScaled ?_
      filter_upwards [hFinalBall] with ω hω
      exact B.norm_sq_le_two_potential_on_ball (weightedPartialSum α ξ n ω) hω
    calc
      ∫ ω, ‖weightedPartialSum α ξ n ω‖ ^ 2 ∂μ
        ≤ ∫ ω, 2 * B.potential (weightedPartialSum α ξ n ω) ∂μ := hMono
      _ = 2 * ∫ ω, B.potential (weightedPartialSum α ξ n ω) ∂μ := by
            rw [integral_const_mul]
      _ ≤ 2 * ((B.D / 2) * sigma ^ 2 * Finset.sum (Finset.range n) (fun i => (α i) ^ 2)) := by
            gcongr
      _ = B.D * sigma ^ 2 * Finset.sum (Finset.range n) (fun i => (α i) ^ 2) := by ring
  calc
    ∫ ω, ‖weightedPartialSum α ξ n ω‖ ∂μ
      ≤ Real.sqrt (∫ ω, ‖weightedPartialSum α ξ n ω‖ ^ 2 ∂μ) := hFirst
    _ ≤ Real.sqrt (B.D * sigma ^ 2 * Finset.sum (Finset.range n) (fun i => (α i) ^ 2)) := by
          exact Real.sqrt_le_sqrt hSecond

end GenericWeightedNoise

namespace StochasticSteepestDescentGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The realized minibatch-average noise `∇f(W_t(ω)) - g_{S_t}(ω)`. -/
def minibatchNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  S.grad t ω - S.minibatchGradient t ω

/-- The norm of the realized minibatch noise. -/
def minibatchNoiseNorm
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : ℝ :=
  ‖S.minibatchNoise t ω‖

/-- The expected minibatch-noise norm used downstream in Corollaries 10 and 11. -/
def expectedMinibatchNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, S.minibatchNoiseNorm t ω ∂S.μ

end PublicDefinitions

section PrivateDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private def fixedTimeNoise
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ℕ → Ω → StrongDual ℝ V :=
  fun i ω =>
    if hi : i < S.batchSize then S.ξ t ⟨i, hi⟩ ω else 0

private def fixedTimePastSigma
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ℕ → MeasurableSpace Ω :=
  fun i =>
    if hi : i < S.batchSize then
      samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t ⟨i, hi⟩
    else inferInstance

end PrivateDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

private theorem fixedTimeNoise_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) :
    StronglyMeasurable (S.fixedTimeNoise t i) := by
  by_cases hi : i < S.batchSize
  · unfold fixedTimeNoise
    simp [hi, StochasticSteepestDescentGeometryContext.ξ]
    simpa using
      (S.grad_stronglyMeasurable t).sub
        (S.sample_stronglyMeasurable t ⟨i, hi⟩)
  · unfold fixedTimeNoise
    simp [hi]
    exact (stronglyMeasurable_const : StronglyMeasurable (fun _ : Ω => (0 : StrongDual ℝ V)))

private theorem fixedTimeNoise_eq_xi
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    S.fixedTimeNoise t i = S.ξ t ⟨i, hi⟩ := by
  funext ω
  simp [fixedTimeNoise, hi]

private theorem fixedTimePastSigma_eq
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    S.fixedTimePastSigma t i =
      samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t ⟨i, hi⟩ := by
  simp [fixedTimePastSigma, hi]

private theorem fixedTimeNoise_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    Integrable (S.fixedTimeNoise t i) S.μ := by
  simpa [S.fixedTimeNoise_eq_xi t i hi] using
    (S.grad_integrable t).sub (S.sample_integrable t ⟨i, hi⟩)

private theorem fixedTimeNoise_condexp_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    S.μ[S.fixedTimeNoise t i | S.fixedTimePastSigma t i] =ᵐ[S.μ] 0 := by
  simpa [S.fixedTimeNoise_eq_xi t i hi, S.fixedTimePastSigma_eq t i hi] using
    (S.ξ_condexp_eq_zero_of_prefix t ⟨i, hi⟩)

private theorem fixedTimeNoise_norm_le_noiseRadius_ae
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    ∀ᵐ ω ∂S.μ, ‖S.fixedTimeNoise t i ω‖ ≤ S.noiseRadius := by
  simpa [S.fixedTimeNoise_eq_xi t i hi] using S.sample_norm_le_noiseRadius_ae t ⟨i, hi⟩

private theorem fixedTimeNoise_second_moment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) (t i : ℕ) (hi : i < S.batchSize) :
    Integrable (fun ω => ‖S.fixedTimeNoise t i ω‖ ^ 2) S.μ ∧
      ∫ ω, ‖S.fixedTimeNoise t i ω‖ ^ 2 ∂S.μ ≤ S.sigma ^ 2 := by
  simpa [S.fixedTimeNoise_eq_xi t i hi] using S.second_moment_bound t ⟨i, hi⟩

private theorem fixedTimeSample_measurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {t j i : ℕ}
    (hji : j < i) (hi : i < S.batchSize) :
    Measurable[S.fixedTimePastSigma t i]
      (fun ω => S.stochasticGradientSample t ⟨j, lt_trans hji hi⟩ ω) := by
  have hFlat :
      Measurable[S.fixedTimePastSigma t i]
        (flatSample S.batchSize_pos S.stochasticGradientSample
          (flatSampleIndex t ⟨j, lt_trans hji hi⟩)) := by
    have hlt : flatSampleIndex t ⟨j, lt_trans hji hi⟩ < flatSampleIndex t ⟨i, hi⟩ := by
      simpa [flatSampleIndex] using Nat.add_lt_add_left hji (t * S.batchSize)
    simpa [fixedTimePastSigma, hi] using
      (flatSample_measurable_of_lt
        S.batchSize_pos S.W S.stochasticGradientSample (t := t) (i := ⟨i, hi⟩) hlt)
  simpa [flatSample_at_flatSampleIndex
      S.batchSize_pos S.stochasticGradientSample t ⟨j, lt_trans hji hi⟩] using hFlat

private theorem fixedTimePastSigma_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ∀ i, S.fixedTimePastSigma t i ≤ inferInstanceAs (MeasurableSpace Ω) := by
  intro i
  by_cases hi : i < S.batchSize
  · simpa [fixedTimePastSigma, hi] using S.samplePrefixSigma_le t ⟨i, hi⟩
  · simp [fixedTimePastSigma, hi]

private theorem fixedTimePartialSum_stronglyMeasurable_at
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) {α : ℕ → ℝ} :
    ∀ i, i < S.batchSize →
      ∀ k, k ≤ i →
        StronglyMeasurable[S.fixedTimePastSigma t i]
          (fun ω => weightedPartialSum α (S.fixedTimeNoise t) k ω)
  | i, hi, 0, hk => by
      simpa [weightedPartialSum] using
        (stronglyMeasurable_const :
          StronglyMeasurable[S.fixedTimePastSigma t i] (fun _ : Ω => (0 : StrongDual ℝ V)))
  | i, hi, k + 1, hk => by
      have hklt : k < i := by omega
      have hPrev :=
        fixedTimePartialSum_stronglyMeasurable_at (S := S) (t := t) (α := α)
          i hi k (Nat.le_of_lt hklt)
      have hGrad :
          StronglyMeasurable[S.fixedTimePastSigma t i]
            (fun ω => S.grad t ω) := by
        simpa [fixedTimePastSigma, hi] using
          (S.grad_prefixStronglyMeasurable t ⟨i, hi⟩ t le_rfl)
      have hSample :
          StronglyMeasurable[S.fixedTimePastSigma t i]
            (fun ω => S.stochasticGradientSample t ⟨k, Nat.lt_trans hklt hi⟩ ω) := by
        exact
          ((S.fixedTimeSample_measurable_before
            (t := t) (j := k) (i := i) hklt hi)).stronglyMeasurable
      have hCurr :
          StronglyMeasurable[S.fixedTimePastSigma t i]
            (fun ω => α k • S.fixedTimeNoise t k ω) := by
        have hkSample : k < S.batchSize := Nat.lt_trans hklt hi
        have : StronglyMeasurable[S.fixedTimePastSigma t i]
            (fun ω => S.fixedTimeNoise t k ω) := by
          have hSub :
              StronglyMeasurable[S.fixedTimePastSigma t i]
                (fun ω => S.grad t ω - S.stochasticGradientSample t ⟨k, Nat.lt_trans hklt hi⟩ ω) :=
            hGrad.sub hSample
          simpa [fixedTimeNoise, hkSample, StochasticSteepestDescentGeometryContext.ξ] using hSub
        simpa using this.const_smul (α k)
      convert hPrev.add hCurr using 1
      ext ω
      simp [weightedPartialSum, Finset.sum_range_succ, add_comm]

private theorem fixedTimeCoeff_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) {α : ℕ → ℝ} :
    ∀ k, k < S.batchSize →
      AEStronglyMeasurable[S.fixedTimePastSigma t k]
        (fun ω =>
          S.pairing.toLinear (S.mirrorMap (weightedPartialSum α (S.fixedTimeNoise t) k ω))) S.μ
  | k, hk => by
    have hPartial :
        StronglyMeasurable[S.fixedTimePastSigma t k]
          (fun ω => weightedPartialSum α (S.fixedTimeNoise t) k ω) :=
      fixedTimePartialSum_stronglyMeasurable_at (S := S) (t := t) (α := α) k hk k le_rfl
    have hMirror :
        StronglyMeasurable[S.fixedTimePastSigma t k]
          (fun ω => S.mirrorMap (weightedPartialSum α (S.fixedTimeNoise t) k ω)) :=
      S.mirrorMap_continuous.comp_stronglyMeasurable hPartial
    exact
      (S.pairing.toLinear.continuous.comp_stronglyMeasurable hMirror).aestronglyMeasurable

private theorem minibatchNoise_eq_weightedPartialSum
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ∀ ω,
      S.minibatchNoise t ω =
        weightedPartialSum
          (fun _ => uniformBatchWeight S.batchSize)
          (S.fixedTimeNoise t)
          S.batchSize ω := by
  intro ω
  have hGradAvg :
      (∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize • S.grad t ω) = S.grad t ω := by
    calc
      (∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize • S.grad t ω)
        = (∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize) • S.grad t ω := by
            rw [Finset.sum_smul]
      _ = (1 : ℝ) • S.grad t ω := by
            rw [show (∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize) = 1 by
              simpa [uniformBatchWeight] using uniformBatchWeight_sum_eq_one S.batchSize_pos]
      _ = S.grad t ω := by simp
  calc
    S.minibatchNoise t ω
      = (∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize • S.grad t ω)
          - ∑ i : Fin S.batchSize, uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω := by
            simp [StochasticSteepestDescentGeometryContext.minibatchNoise,
              StochasticSteepestDescentGeometryContext.minibatchGradient_spec, hGradAvg]
    _ = Finset.sum Finset.univ
          (fun i : Fin S.batchSize =>
            uniformBatchWeight S.batchSize • S.ξ t i ω) := by
              simp [StochasticSteepestDescentGeometryContext.ξ, smul_sub, Finset.sum_sub_distrib]
    _ = Finset.sum (Finset.range S.batchSize)
          (fun i =>
            uniformBatchWeight S.batchSize •
              (if hi : i < S.batchSize then S.ξ t ⟨i, hi⟩ ω else 0)) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (n := S.batchSize)
                  (fun i =>
                    uniformBatchWeight S.batchSize •
                      (if hi : i < S.batchSize then S.ξ t ⟨i, hi⟩ ω else 0)))
    _ = weightedPartialSum
          (fun _ => uniformBatchWeight S.batchSize)
          (S.fixedTimeNoise t) S.batchSize ω := by
            simp [weightedPartialSum, fixedTimeNoise]

private theorem fixedTimeWeightedNoise_analysis
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    Integrable
        (fun ω =>
          ‖weightedPartialSum
              (fun _ => uniformBatchWeight S.batchSize)
              (S.fixedTimeNoise t)
              S.batchSize ω‖) S.μ ∧
      ∫ ω,
          ‖weightedPartialSum
              (fun _ => uniformBatchWeight S.batchSize)
              (S.fixedTimeNoise t)
              S.batchSize ω‖ ∂S.μ
        ≤
          Real.sqrt
            (S.D * S.sigma ^ 2
              * Finset.sum (Finset.range S.batchSize)
                  (fun _ => (uniformBatchWeight S.batchSize) ^ 2)) := by
  letI := S.prob
  refine ⟨?_, ?_⟩
  · exact
      weighted_noise_norm_integrable
        S.pairing S.assumption4_localProxyPotential
        (μ := S.μ)
        (sigma := S.sigma)
        (ξ := S.fixedTimeNoise t)
        (α := fun _ => uniformBatchWeight S.batchSize)
        (n := S.batchSize)
        (pastSigma := S.fixedTimePastSigma t)
        (pastSigma_le := S.fixedTimePastSigma_le t)
        (coeff_nonneg := by intro i hi; exact uniformBatchWeight_nonneg)
        (coeff_sum_le_one := by simpa using uniformBatchWeight_sum_le_one S.batchSize_pos)
        (sample_stronglyMeasurable := fun i => S.fixedTimeNoise_stronglyMeasurable t i)
        (sample_integrable := by intro i hi; exact S.fixedTimeNoise_integrable t i hi)
        (coeff_measurable := by intro i hi; exact S.fixedTimeCoeff_measurable t i hi)
        (cond_zero := by intro i hi; exact S.fixedTimeNoise_condexp_zero t i hi)
        (sample_norm_le_noiseRadius_ae := by intro i hi; exact S.fixedTimeNoise_norm_le_noiseRadius_ae t i hi)
        (second_moment_bound := by intro i hi; exact S.fixedTimeNoise_second_moment_bound t i hi)
  · exact
      weighted_noise_first_moment_bound
        S.pairing S.assumption4_localProxyPotential
        (μ := S.μ)
        (sigma := S.sigma)
        (ξ := S.fixedTimeNoise t)
        (α := fun _ => uniformBatchWeight S.batchSize)
        (n := S.batchSize)
        (pastSigma := S.fixedTimePastSigma t)
        (pastSigma_le := S.fixedTimePastSigma_le t)
        (coeff_nonneg := by intro i hi; exact uniformBatchWeight_nonneg)
        (coeff_sum_le_one := by simpa using uniformBatchWeight_sum_le_one S.batchSize_pos)
        (sample_stronglyMeasurable := fun i => S.fixedTimeNoise_stronglyMeasurable t i)
        (sample_integrable := by intro i hi; exact S.fixedTimeNoise_integrable t i hi)
        (coeff_measurable := by intro i hi; exact S.fixedTimeCoeff_measurable t i hi)
        (cond_zero := by intro i hi; exact S.fixedTimeNoise_condexp_zero t i hi)
        (sample_norm_le_noiseRadius_ae := by intro i hi; exact S.fixedTimeNoise_norm_le_noiseRadius_ae t i hi)
        (second_moment_bound := by intro i hi; exact S.fixedTimeNoise_second_moment_bound t i hi)

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The realized minibatch gradient is integrable at each time. -/
lemma minibatchGradient_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Integrable (S.minibatchGradient t) S.μ := by
  intro t
  have hEq :
      S.minibatchGradient t =
        fun ω =>
          Finset.sum Finset.univ
            (fun i : Fin S.batchSize =>
              uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω) := by
    funext ω
    exact S.minibatchGradient_spec t ω
  simpa [hEq] using
    (MeasureTheory.integrable_finset_sum Finset.univ fun i _ =>
      MeasureTheory.Integrable.smul
        (uniformBatchWeight S.batchSize) (S.sample_integrable t i)
    )

/-- The realized minibatch-noise norm is nonnegative. -/
lemma minibatchNoiseNorm_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    0 ≤ S.minibatchNoiseNorm t ω :=
  norm_nonneg _

/--
Rewrites the realized minibatch noise as the uniform average of the per-sample
noise terms in the current batch.
-/
theorem minibatchNoise_eq_sum_range
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    S.minibatchNoise t ω =
      Finset.sum Finset.univ
        (fun i : Fin S.batchSize =>
          uniformBatchWeight S.batchSize • S.ξ t i ω) := by
  have hConst :
      weightedPartialSum
          (fun _ => uniformBatchWeight S.batchSize)
          (S.fixedTimeNoise t)
          S.batchSize ω =
        Finset.sum Finset.univ
          (fun i : Fin S.batchSize =>
            uniformBatchWeight S.batchSize • S.ξ t i ω) := by
    calc
      weightedPartialSum
          (fun _ => uniformBatchWeight S.batchSize)
          (S.fixedTimeNoise t)
          S.batchSize ω
        = Finset.sum (Finset.range S.batchSize)
            (fun i =>
              uniformBatchWeight S.batchSize •
                (if hi : i < S.batchSize then S.ξ t ⟨i, hi⟩ ω else 0)) := by
            simp [weightedPartialSum, fixedTimeNoise]
      _ = Finset.sum Finset.univ
            (fun i : Fin S.batchSize =>
              uniformBatchWeight S.batchSize • S.ξ t i ω) := by
            symm
            simpa using
              (Fin.sum_univ_eq_sum_range (n := S.batchSize)
                (fun i =>
                  uniformBatchWeight S.batchSize •
                    (if hi : i < S.batchSize then S.ξ t ⟨i, hi⟩ ω else 0)))
  calc
    S.minibatchNoise t ω
      = weightedPartialSum
          (fun _ => uniformBatchWeight S.batchSize)
          (S.fixedTimeNoise t)
          S.batchSize ω := S.minibatchNoise_eq_weightedPartialSum t ω
    _ = Finset.sum Finset.univ
          (fun i : Fin S.batchSize =>
            uniformBatchWeight S.batchSize • S.ξ t i ω) := hConst

/-- The minibatch-noise norm is integrable under Assumptions 1, 2, and 4. -/
theorem minibatchNoiseNorm_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Integrable (fun ω => S.minibatchNoiseNorm t ω) S.μ := by
  intro t
  have hInt := (S.fixedTimeWeightedNoise_analysis t).1
  refine hInt.congr ?_
  filter_upwards with ω
  simp [StochasticSteepestDescentGeometryContext.minibatchNoiseNorm,
    S.minibatchNoise_eq_weightedPartialSum t ω]

/-- Uniform-minibatch expected norm bound for the realized minibatch noise. -/
theorem minibatch_expectedNormBound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t,
      S.expectedMinibatchNoise t ≤ Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
  intro t
  have hBound := (S.fixedTimeWeightedNoise_analysis t).2
  have hSqWeights :
      Finset.sum (Finset.range S.batchSize)
        (fun i => (uniformBatchWeight S.batchSize) ^ 2)
        = 1 / S.batchSizeℝ := by
    simpa [StochasticSteepestDescentParameters.batchSizeℝ] using
      uniformBatchWeight_sq_sum_eq S.batchSize_pos
  calc
    S.expectedMinibatchNoise t
      = ∫ ω, ‖weightedPartialSum
            (fun _ => uniformBatchWeight S.batchSize)
            (S.fixedTimeNoise t) S.batchSize ω‖ ∂S.μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            simp [StochasticSteepestDescentGeometryContext.minibatchNoiseNorm,
              S.minibatchNoise_eq_weightedPartialSum t ω]
    _ ≤ Real.sqrt
          (S.D * S.sigma ^ 2
            * Finset.sum (Finset.range S.batchSize)
                (fun i => (uniformBatchWeight S.batchSize) ^ 2)) := hBound
    _ = Real.sqrt (S.D * S.sigma ^ 2 * (1 / S.batchSizeℝ)) := by rw [hSqWeights]
    _ = Real.sqrt S.D * S.sigma / Real.sqrt S.batchSizeℝ := by
          have hRatioNonneg : 0 ≤ 1 / S.batchSizeℝ := by
            exact one_div_nonneg.mpr S.batchSizeℝ_pos.le
          have hReassoc :
              S.D * S.sigma ^ 2 * (1 / S.batchSizeℝ) =
                S.D * (S.sigma ^ 2 * (1 / S.batchSizeℝ)) := by ring
          have hInner :
              Real.sqrt (S.sigma ^ 2 * (1 / S.batchSizeℝ)) =
                Real.sqrt (S.sigma ^ 2) * Real.sqrt (1 / S.batchSizeℝ) := by
            simpa using (Real.sqrt_mul (sq_nonneg S.sigma) (1 / S.batchSizeℝ))
          have hSqrtInv :
              Real.sqrt (1 / S.batchSizeℝ) = 1 / Real.sqrt S.batchSizeℝ := by
            rw [one_div, Real.sqrt_inv, one_div]
          rw [hReassoc, Real.sqrt_mul S.D_nonneg]
          rw [hInner]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg S.sigma_nonneg]
          rw [hSqrtInv]
          ring

end PublicTheorems

end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
