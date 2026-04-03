import SteepestDescentScalingLaws.Commons

/-!
Frank-Wolfe expected gap scaling laws, fixed-batch family.

Upstream: `SteepestDescentScalingLaws.Commons` and the Frank-Wolfe expected-gap
bounds in `SteepestDescentOptimizationBounds`.
Downstream: the README summaries and the fixed-batch FW expected-gap section of
the blueprint.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

namespace StochasticFrankWolfeGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
FW Expected Gap Scaling Laws Theorem 2: Fixed-Batch Large-Horizon Proxy
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

def fixedBatchFwGapLeadDriftConst
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  4 * S.L / S.lambda

def fixedBatchFwGapLeadNoiseConst
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  (Real.sqrt 2 / S.lambda) * Real.sqrt S.D * S.sigma

def fixedBatchFwGapLeadInitConst
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  2 * S.initialGradNorm / S.lambda

def fixedBatchFrankWolfeGapLeadingProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η N β batchSize : ℝ) : ℝ :=
  S.suboptimality 0 * batchSize / (S.lambda * η * N)
    + S.fixedBatchFwGapLeadInitConst * batchSize / (N * (1 - β))
    + S.fixedBatchFwGapLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
    + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η

def IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η N β batchSize : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.fixedBatchFrankWolfeGapLeadingProxy η N β batchSize
      ≤ S.fixedBatchFrankWolfeGapLeadingProxy η' N β batchSize

def IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (batchSize : ℝ) (betaStar etaStar : ℝ → ℝ) : Prop :=
  ∃ N0, 0 < N0 ∧
    ∀ N ≥ N0,
      0 < betaStar N ∧ betaStar N < 1 ∧
      S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer
        (etaStar N) N (betaStar N) batchSize

def fixedBatchFrankWolfeGapReducedLeadingProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  2 * Real.sqrt
      ((S.suboptimality 0 / S.lambda)
        * S.fixedBatchFwGapLeadDriftConst * batchSize / (N * (1 - β)))
    + S.fixedBatchFwGapLeadInitConst * batchSize / (N * (1 - β))
    + S.fixedBatchFwGapLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)

def IsFixedBatchFrankWolfeGapReducedLeadingProxyMomentumMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧
    ∀ β' > 0, β' < 1 →
      S.fixedBatchFrankWolfeGapReducedLeadingProxy N β batchSize
        ≤ S.fixedBatchFrankWolfeGapReducedLeadingProxy N β' batchSize

def IsEventuallyInteriorMomentumMinimizerFamilyFixedBatchFrankWolfeGapReducedLeadingProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (batchSize : ℝ) (betaStar : ℝ → ℝ) : Prop :=
  ∃ N0, 0 < N0 ∧
    ∀ N ≥ N0,
      S.IsFixedBatchFrankWolfeGapReducedLeadingProxyMomentumMinimizer
        N (betaStar N) batchSize

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

private def fwGapLeadBiasCoeff
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  S.suboptimality 0 / S.lambda

private def etaStarFixedBatchClosedForm
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  Real.sqrt
    (S.fwGapLeadBiasCoeff * batchSize * (1 - β)
      / (S.fixedBatchFwGapLeadDriftConst * N))

private def deltaScale (N batchSize : ℝ) : ℝ :=
  Real.sqrt (batchSize / N)

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

private theorem fixedBatchFwGapLeadDriftConst_pos
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    0 < S.fixedBatchFwGapLeadDriftConst := by
  unfold fixedBatchFwGapLeadDriftConst
  exact div_pos (mul_pos (by norm_num) S.L_pos) S.lambda_pos

private theorem fwGapLeadBiasCoeff_pos
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (hGap : 0 < S.suboptimality 0) :
    0 < S.fwGapLeadBiasCoeff := by
  unfold fwGapLeadBiasCoeff
  exact div_pos hGap S.lambda_pos

private theorem etaStarFixedBatchClosedForm_sq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1) :
    (S.etaStarFixedBatchClosedForm N β batchSize) ^ 2
      = S.fwGapLeadBiasCoeff * batchSize * (1 - β)
          / (S.fixedBatchFwGapLeadDriftConst * N) := by
  unfold etaStarFixedBatchClosedForm
  simpa using
    (Real.sq_sqrt
      (show 0 ≤ S.fwGapLeadBiasCoeff * batchSize * (1 - β)
          / (S.fixedBatchFwGapLeadDriftConst * N) by
        exact div_nonneg
          (mul_nonneg
            (mul_nonneg (S.fwGapLeadBiasCoeff_pos hGap).le hBatch.le)
            (sub_nonneg.mpr hβ1.le))
          (mul_nonneg S.fixedBatchFwGapLeadDriftConst_pos.le hN.le)))

private axiom closedForm_fixedBatch_isMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer
      (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize

private axiom closedForm_fixedBatch_lt_of_ne
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize η : ℝ}
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : 0 < η)
    (hNe : η ≠ S.etaStarFixedBatchClosedForm N β batchSize) :
    S.fixedBatchFrankWolfeGapLeadingProxy (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize
      < S.fixedBatchFrankWolfeGapLeadingProxy η N β batchSize

private axiom etaStarFixedBatch_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar = S.etaStarFixedBatchClosedForm N β batchSize

private theorem fixedBatchClosedFormFamily_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.suboptimality 0)
    {betaStar etaStar : ℝ → ℝ}
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ N0, 0 < N0 ∧
      ∀ N ≥ N0,
        etaStar N = S.etaStarFixedBatchClosedForm N (betaStar N) batchSize := by
  rcases hMin with ⟨N0, hN0, hMin⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  rcases hMin N hN with ⟨hβ0, hβ1, hEta⟩
  exact S.etaStarFixedBatch_eq hGap (lt_of_lt_of_le hN0 hN) hBatch hβ0 hβ1 hEta

private theorem deltaScale_pos {N batchSize : ℝ}
    (hN : 0 < N) (hBatch : 0 < batchSize) :
    0 < deltaScale N batchSize := by
  unfold deltaScale
  exact Real.sqrt_pos.2 (div_pos hBatch hN)

private theorem deltaScale_sq {N batchSize : ℝ}
    (hN : 0 < N) (hBatch : 0 < batchSize) :
    (deltaScale N batchSize) ^ 2 = batchSize / N := by
  unfold deltaScale
  simpa using (Real.sq_sqrt (div_nonneg hBatch.le hN.le))

private axiom fixedBatchFrankWolfeGapTokenBudgetScalingBounds
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fixedBatchFwGapLeadNoiseConst)
    {betaStar : ℝ → ℝ}
    (hBetaMin :
      S.IsEventuallyInteriorMomentumMinimizerFamilyFixedBatchFrankWolfeGapReducedLeadingProxy
        batchSize betaStar)
    {etaStar : ℝ → ℝ}
    (hEtaMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * Real.sqrt (batchSize / N) ≤ 1 - betaStar N ∧
        1 - betaStar N ≤ cBetaUpper * Real.sqrt (batchSize / N) ∧
        cEtaLower * Real.rpow (batchSize / N) (3 / 4 : ℝ) ≤ etaStar N ∧
        etaStar N ≤ cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ)

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

theorem fWExpectedGapSLTheorem2_1_etaMinimizerEqClosedForm
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar = Real.sqrt
      (S.fwGapLeadBiasCoeff * batchSize * (1 - β)
        / (S.fixedBatchFwGapLeadDriftConst * N)) := by
  simpa [etaStarFixedBatchClosedForm] using
    S.etaStarFixedBatch_eq hGap hN hBatch hβ0 hβ1 hMin

theorem fWExpectedGapSLTheorem2_2_tokenBudgetScaling
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fixedBatchFwGapLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hBetaMin :
      S.IsEventuallyInteriorMomentumMinimizerFamilyFixedBatchFrankWolfeGapReducedLeadingProxy
        batchSize betaStar)
    (hEtaMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * Real.sqrt (batchSize / N) ≤ 1 - betaStar N ∧
        1 - betaStar N ≤ cBetaUpper * Real.sqrt (batchSize / N) ∧
        cEtaLower * Real.rpow (batchSize / N) (3 / 4 : ℝ) ≤ etaStar N ∧
        etaStar N ≤ cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
  exact S.fixedBatchFrankWolfeGapTokenBudgetScalingBounds hBatch hGap hNoise hBetaMin hEtaMin

theorem fWExpectedGapSLTheorem2_FixedBatchLargeHorizonProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fixedBatchFwGapLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hBetaMin :
      S.IsEventuallyInteriorMomentumMinimizerFamilyFixedBatchFrankWolfeGapReducedLeadingProxy
        batchSize betaStar)
    (hEtaMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0 T0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧ 0 < T0 ∧
      (∀ N ≥ N0,
        cBetaLower * Real.sqrt (batchSize / N) ≤ 1 - betaStar N ∧
        1 - betaStar N ≤ cBetaUpper * Real.sqrt (batchSize / N) ∧
        cEtaLower * Real.rpow (batchSize / N) (3 / 4 : ℝ) ≤ etaStar N ∧
        etaStar N ≤ cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ)) ∧
      (∀ T ≥ T0,
        cBetaLower / Real.rpow T (1 / 2 : ℝ) ≤ 1 - betaStar (batchSize * T) ∧
        1 - betaStar (batchSize * T) ≤ cBetaUpper / Real.rpow T (1 / 2 : ℝ) ∧
        cEtaLower / Real.rpow T (3 / 4 : ℝ) ≤ etaStar (batchSize * T) ∧
        etaStar (batchSize * T) ≤ cEtaUpper / Real.rpow T (3 / 4 : ℝ)) := by
  rcases S.fWExpectedGapSLTheorem2_2_tokenBudgetScaling hBatch hGap hNoise hBetaMin hEtaMin with
    ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0,
      hcBetaLower, hcBetaUpper, hcEtaLower, hcEtaUpper, hN0, hNForm⟩
  refine ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0, max 1 (N0 / batchSize),
    hcBetaLower, hcBetaUpper, hcEtaLower, hcEtaUpper, hN0, ?_, hNForm, ?_⟩
  · have hOne : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le hOne (le_max_left _ _)
  intro T hT
  have hTpos : 0 < T := by
    have hT0pos : 0 < max 1 (N0 / batchSize) := by
      have hOne : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le hOne (le_max_left _ _)
    exact lt_of_lt_of_le hT0pos hT
  have hN : N0 ≤ batchSize * T := by
    have hDiv : N0 / batchSize ≤ T := le_trans (le_max_right _ _) hT
    have hMul : N0 ≤ T * batchSize := (div_le_iff₀ hBatch).mp hDiv
    simpa [mul_comm] using hMul
  rcases hNForm (batchSize * T) hN with ⟨hβLower, hβUpper, hηLower, hηUpper⟩
  have hBaseEq : batchSize / (batchSize * T) = T⁻¹ := by
    field_simp [hBatch.ne', hTpos.ne']
  rw [hBaseEq] at hβLower hβUpper hηLower hηUpper
  have hBetaScale :
      Real.sqrt (T⁻¹ : ℝ) = 1 / Real.rpow T (1 / 2 : ℝ) := by
    rw [Real.sqrt_inv]
    simp [Real.sqrt_eq_rpow, one_div]
  have hEtaScale :
      Real.rpow (T⁻¹ : ℝ) (3 / 4 : ℝ) = 1 / Real.rpow T (3 / 4 : ℝ) := by
    simpa [one_div] using (Real.inv_rpow hTpos.le (3 / 4 : ℝ))
  constructor
  · simpa [hBetaScale, div_eq_mul_inv] using hβLower
  constructor
  · simpa [hBetaScale, div_eq_mul_inv] using hβUpper
  constructor
  · calc
      cEtaLower / Real.rpow T (3 / 4 : ℝ)
          = cEtaLower * Real.rpow (T⁻¹ : ℝ) (3 / 4 : ℝ) := by
              rw [hEtaScale]
              ring
      _ ≤ etaStar (batchSize * T) := hηLower
  · calc
      etaStar (batchSize * T) ≤ cEtaUpper * Real.rpow (T⁻¹ : ℝ) (3 / 4 : ℝ) := hηUpper
      _ = cEtaUpper / Real.rpow T (3 / 4 : ℝ) := by
            rw [hEtaScale]
            ring

end StochasticFrankWolfeGeometryContext

end

end SteepestDescentOptimizationBounds
