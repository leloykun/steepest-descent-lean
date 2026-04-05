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
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
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
  2 * S.initialExpectedMomentumError / S.lambda

def fixedBatchFwGapInitialGap
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  S.toStochasticSteepestDescentGeometryContext.initialSuboptimality

def fixedBatchFrankWolfeGapLeadingProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η N β batchSize : ℝ) : ℝ :=
  S.fixedBatchFwGapInitialGap * batchSize / (S.lambda * η * N)
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
      ((S.fixedBatchFwGapInitialGap / S.lambda)
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
  S.fixedBatchFwGapInitialGap / S.lambda

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
    (hGap : 0 < S.fixedBatchFwGapInitialGap) :
    0 < S.fwGapLeadBiasCoeff := by
  unfold fwGapLeadBiasCoeff
  exact div_pos hGap S.lambda_pos

private theorem etaStarFixedBatchClosedForm_sq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
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

private theorem fixedBatchLeading_rel
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1) :
    S.fwGapLeadBiasCoeff * batchSize / N
      = (S.fixedBatchFwGapLeadDriftConst / (1 - β))
          * (S.etaStarFixedBatchClosedForm N β batchSize) ^ 2 := by
  have hSq := S.etaStarFixedBatchClosedForm_sq hGap hN hBatch hβ1
  have hβne : 1 - β ≠ 0 := sub_ne_zero.mpr (ne_of_lt hβ1).symm
  have hTmp :
    (S.fixedBatchFwGapLeadDriftConst / (1 - β))
        * (S.etaStarFixedBatchClosedForm N β batchSize) ^ 2
        = S.fwGapLeadBiasCoeff * batchSize / N := by
    rw [hSq]
    field_simp [hN.ne', hβne, S.fixedBatchFwGapLeadDriftConst_pos.ne']
  exact hTmp.symm

private theorem closedForm_fixedBatch_isMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer
      (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize := by
  refine ⟨?_, ?_⟩
  · unfold etaStarFixedBatchClosedForm
    exact Real.sqrt_pos.2 (by
      exact div_pos
        (mul_pos
          (mul_pos (S.fwGapLeadBiasCoeff_pos hGap) hBatch)
          (sub_pos.mpr hβ1))
        (mul_pos S.fixedBatchFwGapLeadDriftConst_pos hN))
  · intro η hη
    have hRel :=
      S.fixedBatchLeading_rel hGap hN hBatch hβ1
    have hEtaStarPos :
        0 < S.etaStarFixedBatchClosedForm N β batchSize := by
      unfold etaStarFixedBatchClosedForm
      exact Real.sqrt_pos.2 (by
        exact div_pos
          (mul_pos
            (mul_pos (S.fwGapLeadBiasCoeff_pos hGap) hBatch)
            (sub_pos.mpr hβ1))
          (mul_pos S.fixedBatchFwGapLeadDriftConst_pos hN))
    have hCoeffPos :
        0 < S.fixedBatchFwGapLeadDriftConst / (1 - β) := by
      exact div_pos S.fixedBatchFwGapLeadDriftConst_pos (sub_pos.mpr hβ1)
    have hLower :
        2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize)
          ≤ S.fwGapLeadBiasCoeff * batchSize / N / η
              + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
      have hDecomp :=
        reciprocal_linear_eq_min_add_sq hη hRel
      have hTerm :
          0 ≤
            (S.fixedBatchFwGapLeadDriftConst / (1 - β))
              * (η - S.etaStarFixedBatchClosedForm N β batchSize) ^ 2 / η := by
        positivity
      rw [hDecomp]
      linarith
    have hLower' := hLower
    unfold fwGapLeadBiasCoeff at hLower'
    have hEtaStarValue :=
      reciprocal_linear_value_at_closed_form hEtaStarPos hRel
    unfold fwGapLeadBiasCoeff at hEtaStarValue
    have hLowerExact :
        2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize)
          ≤ S.fixedBatchFwGapInitialGap * batchSize / (S.lambda * η * N)
              + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hLower'
    have hEtaStarValueExact :
        S.fixedBatchFwGapInitialGap * batchSize
            / (S.lambda * S.etaStarFixedBatchClosedForm N β batchSize * N)
          + (S.fixedBatchFwGapLeadDriftConst / (1 - β))
              * (S.etaStarFixedBatchClosedForm N β batchSize)
        = 2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEtaStarValue
    have hLead :
        S.fixedBatchFwGapInitialGap * batchSize
            / (S.lambda * S.etaStarFixedBatchClosedForm N β batchSize * N)
          + (S.fixedBatchFwGapLeadDriftConst / (1 - β))
              * (S.etaStarFixedBatchClosedForm N β batchSize)
        ≤ S.fixedBatchFwGapInitialGap * batchSize / (S.lambda * η * N)
            + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
      linarith [hLowerExact, hEtaStarValueExact]
    let common : ℝ :=
      S.fixedBatchFwGapLeadInitConst * batchSize / (N * (1 - β))
        + S.fixedBatchFwGapLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
    have hTotal := add_le_add_left hLead common
    simpa [common, fixedBatchFrankWolfeGapLeadingProxy, add_assoc, add_left_comm, add_comm]
      using hTotal

private theorem closedForm_fixedBatch_lt_of_ne
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize η : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hη : 0 < η)
    (hNe : η ≠ S.etaStarFixedBatchClosedForm N β batchSize) :
    S.fixedBatchFrankWolfeGapLeadingProxy (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize
      < S.fixedBatchFrankWolfeGapLeadingProxy η N β batchSize := by
  have hRel :=
    S.fixedBatchLeading_rel hGap hN hBatch hβ1
  have hEtaStarPos :
      0 < S.etaStarFixedBatchClosedForm N β batchSize :=
    (S.closedForm_fixedBatch_isMinimizer hGap hN hBatch hβ1).1
  have hStrict :
      2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
          * (S.etaStarFixedBatchClosedForm N β batchSize)
        < S.fwGapLeadBiasCoeff * batchSize / N / η
            + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
    have hCore := reciprocal_linear_lt_of_ne
      (div_pos S.fixedBatchFwGapLeadDriftConst_pos (sub_pos.mpr hβ1))
      hη hRel hNe
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hCore
  have hEq :
      S.fwGapLeadBiasCoeff * batchSize / N / (S.etaStarFixedBatchClosedForm N β batchSize)
        + (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize)
      = 2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
          * (S.etaStarFixedBatchClosedForm N β batchSize) := by
    exact reciprocal_linear_value_at_closed_form hEtaStarPos hRel
  have hStrict' := hStrict
  have hEq' := hEq
  unfold fwGapLeadBiasCoeff at hStrict' hEq'
  have hStrictExact :
      2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
          * (S.etaStarFixedBatchClosedForm N β batchSize)
        < S.fixedBatchFwGapInitialGap * batchSize / (S.lambda * η * N)
            + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hStrict'
  have hEqExact :
      S.fixedBatchFwGapInitialGap * batchSize
          / (S.lambda * S.etaStarFixedBatchClosedForm N β batchSize * N)
        + (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize)
      = 2 * (S.fixedBatchFwGapLeadDriftConst / (1 - β))
          * (S.etaStarFixedBatchClosedForm N β batchSize) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEq'
  have hLead :
      S.fixedBatchFwGapInitialGap * batchSize
          / (S.lambda * S.etaStarFixedBatchClosedForm N β batchSize * N)
        + (S.fixedBatchFwGapLeadDriftConst / (1 - β))
            * (S.etaStarFixedBatchClosedForm N β batchSize)
      < S.fixedBatchFwGapInitialGap * batchSize / (S.lambda * η * N)
          + (S.fixedBatchFwGapLeadDriftConst / (1 - β)) * η := by
    linarith [hStrictExact, hEqExact]
  let common : ℝ :=
    S.fixedBatchFwGapLeadInitConst * batchSize / (N * (1 - β))
      + S.fixedBatchFwGapLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
  have hTotal := add_lt_add_left hLead common
  simpa [common, fixedBatchFrankWolfeGapLeadingProxy, add_assoc, add_left_comm, add_comm]
    using hTotal

private theorem etaStarFixedBatch_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar = S.etaStarFixedBatchClosedForm N β batchSize := by
  by_contra hNe
  have hLt := S.closedForm_fixedBatch_lt_of_ne hGap hN hBatch hβ1 hMin.1 hNe
  have hClosedMin := S.closedForm_fixedBatch_isMinimizer hGap hN hBatch hβ1
  have hLe := hMin.2 (S.etaStarFixedBatchClosedForm N β batchSize) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedBatchClosedFormFamily_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    {betaStar etaStar : ℝ → ℝ}
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ N0, 0 < N0 ∧
      ∀ N ≥ N0,
        etaStar N = S.etaStarFixedBatchClosedForm N (betaStar N) batchSize := by
  rcases hMin with ⟨N0, hN0, hMin⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  rcases hMin N hN with ⟨_, hβ1, hEta⟩
  exact S.etaStarFixedBatch_eq hGap (lt_of_lt_of_le hN0 hN) hBatch hβ1 hEta

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

private theorem fixedBatchFrankWolfeGapTokenBudgetScalingBounds
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
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
        etaStar N ≤ cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
  rcases hBetaMin with ⟨N0Beta, hN0Beta, hBetaMin⟩
  rcases S.fixedBatchClosedFormFamily_eq hBatch hGap hEtaMin with
    ⟨N0Eta, hN0Eta, hEtaEqFamily⟩
  let Δ : ℝ := S.fwGapLeadBiasCoeff
  let A : ℝ := S.fixedBatchFwGapLeadDriftConst
  let C : ℝ := S.fixedBatchFwGapLeadInitConst
  let Z : ℝ := S.fixedBatchFwGapLeadNoiseConst
  let K : ℝ := 2 * Real.sqrt (Δ * A) + C + Z / Real.sqrt batchSize
  let cRootLower : ℝ := 2 * Real.sqrt (Δ * A) / K
  let cRootUpper : ℝ := K * Real.sqrt batchSize / Z
  let cBetaLower : ℝ := cRootLower ^ 2
  let cBetaUpper : ℝ := cRootUpper ^ 2
  let cEtaLower : ℝ := Real.sqrt (Δ / A) * cRootLower
  let cEtaUpper : ℝ := Real.sqrt (Δ / A) * cRootUpper
  let N0 : ℝ := max 1 (max (batchSize + 1) (max N0Beta N0Eta))
  have hΔpos : 0 < Δ := S.fwGapLeadBiasCoeff_pos hGap
  have hApos : 0 < A := S.fixedBatchFwGapLeadDriftConst_pos
  have hCnonneg : 0 ≤ C := by
    dsimp [C, fixedBatchFwGapLeadInitConst]
    exact div_nonneg (mul_nonneg (by norm_num) S.initialExpectedMomentumError_nonneg) S.lambda_pos.le
  have hSqrtBatchPos : 0 < Real.sqrt batchSize := Real.sqrt_pos.2 hBatch
  have hKpos : 0 < K := by
    dsimp [K]
    have hMain : 0 < 2 * Real.sqrt (Δ * A) := by
      refine mul_pos (by norm_num) ?_
      exact Real.sqrt_pos.2 (mul_pos hΔpos hApos)
    have hNoiseTerm : 0 < Z / Real.sqrt batchSize := div_pos hNoise hSqrtBatchPos
    linarith
  have hN0BetaLe : N0Beta ≤ N0 := by
    unfold N0
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hN0EtaLe : N0Eta ≤ N0 := by
    unfold N0
    exact le_trans (le_max_right N0Beta N0Eta) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hBatchOneLe : batchSize + 1 ≤ N0 := by
    unfold N0
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0,
    by positivity, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  · intro N hN
    have hNpos : 0 < N := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)) hN
    let d : ℝ := deltaScale N batchSize
    let r : ℝ := Real.sqrt d
    let δ : ℝ := 1 - betaStar N
    have hdPos : 0 < d := deltaScale_pos hNpos hBatch
    have hrPos : 0 < r := Real.sqrt_pos.2 hdPos
    have hBatchLtN : batchSize < N := by
      have hBatchPlus : batchSize + 1 ≤ N := le_trans hBatchOneLe hN
      linarith
    have hdLtOne : d < 1 := by
      have hQuotLtOne : batchSize / N < 1 := by
        exact (div_lt_one hNpos).2 hBatchLtN
      have hSqLtOne : d ^ 2 < 1 := by
        calc
          d ^ 2 = batchSize / N := by
            simpa [d] using deltaScale_sq hNpos hBatch
          _ < 1 := hQuotLtOne
      by_contra hdNotLt
      have hOneLe : 1 ≤ d := le_of_not_gt hdNotLt
      have hSqGeOne : 1 ≤ d ^ 2 := by
        nlinarith [hdPos, hOneLe]
      linarith
    have hdLeOne : d ≤ 1 := le_of_lt hdLtOne
    have hBetaCandPos : 0 < 1 - d := sub_pos.mpr hdLtOne
    have hBetaCandLt1 : 1 - d < 1 := by linarith [hdPos]
    rcases hBetaMin N (le_trans hN0BetaLe hN) with ⟨hβ0, hβ1, hMinOn⟩
    have hMinVal :
        S.fixedBatchFrankWolfeGapReducedLeadingProxy N (betaStar N) batchSize
          ≤ S.fixedBatchFrankWolfeGapReducedLeadingProxy N (1 - d) batchSize :=
      hMinOn (1 - d) hBetaCandPos hBetaCandLt1
    have hDeltaSq : d ^ 2 = batchSize / N := by
      simpa [d] using deltaScale_sq hNpos hBatch
    have hCandidateLe :
        S.fixedBatchFrankWolfeGapReducedLeadingProxy N (1 - d) batchSize ≤ K * r := by
      have hRatio : batchSize / (N * d) = d := by
        calc
          batchSize / (N * d) = (batchSize / N) / d := by
            field_simp [hNpos.ne', hdPos.ne']
          _ = (d * d) / d := by rw [← hDeltaSq, pow_two]
          _ = d := by field_simp [hdPos.ne']
      have hTerm1Ratio :
          Δ * A * batchSize / (N * d) = Δ * A * d := by
        calc
          Δ * A * batchSize / (N * d) = (Δ * A) * (batchSize / (N * d)) := by
            field_simp [hNpos.ne', hdPos.ne']
          _ = (Δ * A) * d := by rw [hRatio]
          _ = Δ * A * d := by ring
      have hTerm2Ratio :
          C * batchSize / (N * d) = C * d := by
        calc
          C * batchSize / (N * d) = C * (batchSize / (N * d)) := by
            field_simp [hNpos.ne', hdPos.ne']
          _ = C * d := by rw [hRatio]
      have hTerm1 :
          2 * Real.sqrt (Δ * A * batchSize / (N * d))
            = 2 * Real.sqrt (Δ * A) * r := by
        calc
          2 * Real.sqrt (Δ * A * batchSize / (N * d))
            = 2 * Real.sqrt (Δ * A * d) := by rw [hTerm1Ratio]
          _ = 2 * (Real.sqrt (Δ * A) * Real.sqrt d) := by
                rw [show Δ * A * d = (Δ * A) * d by ring]
                rw [Real.sqrt_mul (mul_nonneg hΔpos.le hApos.le)]
          _ = 2 * Real.sqrt (Δ * A) * r := by simp [r, mul_left_comm, mul_comm]
      have hTerm2 :
          C * batchSize / (N * d) ≤ C * r := by
        have hdLeSqrt : d ≤ r := le_sqrt_of_nonneg_of_le_one hdPos.le hdLeOne
        rw [hTerm2Ratio]
        exact mul_le_mul_of_nonneg_left hdLeSqrt hCnonneg
      have hTerm3 :
          Z * Real.sqrt (d / batchSize) = (Z / Real.sqrt batchSize) * r := by
        have hSqrtDiv :
            Real.sqrt (d / batchSize) = Real.sqrt d / Real.sqrt batchSize := by
          rw [Real.sqrt_div hdPos.le batchSize]
        calc
          Z * Real.sqrt (d / batchSize)
            = Z * (Real.sqrt d / Real.sqrt batchSize) := by rw [hSqrtDiv]
          _ = (Z / Real.sqrt batchSize) * r := by
                rw [show Real.sqrt d = r by rfl]
                field_simp [hSqrtBatchPos.ne']
      calc
        S.fixedBatchFrankWolfeGapReducedLeadingProxy N (1 - d) batchSize
          = 2 * Real.sqrt (Δ * A * batchSize / (N * d))
              + C * batchSize / (N * d)
              + Z * Real.sqrt (d / batchSize) := by
                simp [StochasticFrankWolfeGeometryContext.fixedBatchFrankWolfeGapReducedLeadingProxy,
                  fwGapLeadBiasCoeff, Δ, A, C, Z, d, sub_eq_add_neg]
          _ ≤ 2 * Real.sqrt (Δ * A) * r + C * r + (Z / Real.sqrt batchSize) * r := by
                rw [hTerm1, hTerm3]
                gcongr
          _ = K * r := by
                dsimp [K]
                ring
    have hProxyUpper :
        S.fixedBatchFrankWolfeGapReducedLeadingProxy N (betaStar N) batchSize ≤ K * r :=
      le_trans hMinVal hCandidateLe
    have hDeltaPos : 0 < δ := sub_pos.mpr hβ1
    have hRootLower :
        cRootLower * r ≤ Real.sqrt δ := by
      have hTerm1Le :
          2 * Real.sqrt (Δ * A * batchSize / (N * δ))
            ≤ S.fixedBatchFrankWolfeGapReducedLeadingProxy N (betaStar N) batchSize := by
        unfold StochasticFrankWolfeGeometryContext.fixedBatchFrankWolfeGapReducedLeadingProxy
        have hInitNonneg : 0 ≤ C * batchSize / (N * δ) := by
          have : 0 ≤ N * δ := mul_nonneg hNpos.le hDeltaPos.le
          positivity
        have hNoiseNonneg : 0 ≤ Z * Real.sqrt (δ / batchSize) := by positivity
        dsimp [Δ, A, C, Z, fwGapLeadBiasCoeff] at *
        linarith
      have hBound :
          2 * Real.sqrt (Δ * A * batchSize / (N * δ)) ≤ K * r :=
        le_trans hTerm1Le hProxyUpper
      have hRatio :
          batchSize / (N * δ) = d ^ 2 / δ := by
        calc
          batchSize / (N * δ) = (batchSize / N) / δ := by
            field_simp [hNpos.ne', hDeltaPos.ne']
          _ = d ^ 2 / δ := by rw [← hDeltaSq]
      have hTerm1Ratio :
          Δ * A * batchSize / (N * δ) = Δ * A * (d ^ 2 / δ) := by
        calc
          Δ * A * batchSize / (N * δ) = (Δ * A) * (batchSize / (N * δ)) := by
            field_simp [hNpos.ne', hDeltaPos.ne']
          _ = (Δ * A) * (d ^ 2 / δ) := by rw [hRatio]
          _ = Δ * A * (d ^ 2 / δ) := by ring
      have hRewrite :
          2 * Real.sqrt (Δ * A * batchSize / (N * δ))
            = (2 * Real.sqrt (Δ * A)) * d / Real.sqrt δ := by
        calc
          2 * Real.sqrt (Δ * A * batchSize / (N * δ))
            = 2 * Real.sqrt ((Δ * A) * (d ^ 2 / δ)) := by rw [hTerm1Ratio]
          _ = 2 * (Real.sqrt (Δ * A) * Real.sqrt (d ^ 2 / δ)) := by
                rw [Real.sqrt_mul (by positivity)]
          _ = 2 * (Real.sqrt (Δ * A) * (d / Real.sqrt δ)) := by
                rw [Real.sqrt_div (by positivity) δ]
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdPos.le]
          _ = (2 * Real.sqrt (Δ * A)) * d / Real.sqrt δ := by
                field_simp [Real.sqrt_ne_zero'.2 hDeltaPos]
      rw [hRewrite] at hBound
      have hMul :
          (2 * Real.sqrt (Δ * A)) * d ≤ K * r * Real.sqrt δ := by
        exact (div_le_iff₀ (Real.sqrt_pos.2 hDeltaPos)).mp hBound
      have hCancel :
          (2 * Real.sqrt (Δ * A)) * r ≤ K * Real.sqrt δ := by
        have hrMul : r * r = d := by
          simpa [pow_two] using (Real.sq_sqrt hdPos.le)
        have hMul' :
            ((2 * Real.sqrt (Δ * A)) * r) * r ≤ (K * Real.sqrt δ) * r := by
          calc
            ((2 * Real.sqrt (Δ * A)) * r) * r = (2 * Real.sqrt (Δ * A)) * d := by
              rw [← hrMul]
              ring
            _ ≤ K * r * Real.sqrt δ := hMul
            _ = (K * Real.sqrt δ) * r := by ring
        exact le_of_mul_le_mul_right (by simpa [mul_assoc, mul_left_comm, mul_comm] using hMul') hrPos
      dsimp [cRootLower]
      have hDiv :
          ((2 * Real.sqrt (Δ * A)) * r) / K ≤ Real.sqrt δ := by
        exact (div_le_iff₀ hKpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hCancel)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hDiv
    have hRootUpper :
        Real.sqrt δ ≤ cRootUpper * r := by
      have hTerm3Le :
          Z * Real.sqrt (δ / batchSize)
            ≤ S.fixedBatchFrankWolfeGapReducedLeadingProxy N (betaStar N) batchSize := by
        unfold StochasticFrankWolfeGeometryContext.fixedBatchFrankWolfeGapReducedLeadingProxy
        have hTerm1Nonneg :
            0 ≤ 2 * Real.sqrt (Δ * A * batchSize / (N * δ)) := by positivity
        have hInitNonneg : 0 ≤ C * batchSize / (N * δ) := by positivity
        dsimp [Δ, A, C, Z, fwGapLeadBiasCoeff] at *
        linarith
      have hBound :
          Z * Real.sqrt (δ / batchSize) ≤ K * r :=
        le_trans hTerm3Le hProxyUpper
      have hRewrite :
          Z * Real.sqrt (δ / batchSize) = (Z / Real.sqrt batchSize) * Real.sqrt δ := by
        have hSqrtDiv :
            Real.sqrt (δ / batchSize) = Real.sqrt δ / Real.sqrt batchSize := by
          rw [Real.sqrt_div hDeltaPos.le batchSize]
        calc
          Z * Real.sqrt (δ / batchSize)
            = Z * (Real.sqrt δ / Real.sqrt batchSize) := by rw [hSqrtDiv]
          _ = (Z / Real.sqrt batchSize) * Real.sqrt δ := by
                field_simp [hSqrtBatchPos.ne']
      rw [hRewrite] at hBound
      dsimp [cRootUpper]
      have hCoeffPos : 0 < Z / Real.sqrt batchSize := div_pos hNoise hSqrtBatchPos
      have hDiv : Real.sqrt δ ≤ (K * r) / (Z / Real.sqrt batchSize) := by
        exact (le_div_iff₀ hCoeffPos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hBound)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hDiv
    have hGapLower :
        cBetaLower * d ≤ δ := by
      have hrMul : r * r = d := by
        simpa [pow_two] using (Real.sq_sqrt hdPos.le)
      have hLowerNonneg : 0 ≤ cRootLower * r := by positivity
      have hSq := mul_self_le_mul_self hLowerNonneg hRootLower
      have hSq' : cRootLower ^ 2 * d ≤ δ := by
        calc
          cRootLower ^ 2 * d = (cRootLower * r) * (cRootLower * r) := by
            rw [← hrMul]
            ring
          _ ≤ Real.sqrt δ * Real.sqrt δ := hSq
          _ = δ := by
            simpa [pow_two] using (Real.sq_sqrt hDeltaPos.le)
      simpa [cBetaLower] using hSq'
    have hGapUpper :
        δ ≤ cBetaUpper * d := by
      have hrMul : r * r = d := by
        simpa [pow_two] using (Real.sq_sqrt hdPos.le)
      have hUpperNonneg : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
      have hSq := mul_self_le_mul_self hUpperNonneg hRootUpper
      have hSq' : δ ≤ cRootUpper ^ 2 * d := by
        calc
          δ = Real.sqrt δ * Real.sqrt δ := by
            symm
            simpa [pow_two] using (Real.sq_sqrt hDeltaPos.le)
          _ ≤ (cRootUpper * r) * (cRootUpper * r) := hSq
          _ = cRootUpper ^ 2 * d := by
            rw [← hrMul]
            ring
      simpa [cBetaUpper] using hSq'
    have hEtaEqClosed := hEtaEqFamily N (le_trans hN0EtaLe hN)
    have hEtaEq :
        etaStar N = Real.sqrt (Δ / A) * d * Real.sqrt δ := by
      calc
        etaStar N = S.etaStarFixedBatchClosedForm N (betaStar N) batchSize := hEtaEqClosed
        _ = Real.sqrt (Δ / A) * d * Real.sqrt δ := by
              unfold etaStarFixedBatchClosedForm
              have hInside :
                  Δ * batchSize * δ / (A * N) = (Δ / A) * δ * d ^ 2 := by
                calc
                  Δ * batchSize * δ / (A * N)
                      = (Δ / A) * (batchSize / N) * δ := by
                          field_simp [hApos.ne', hNpos.ne']
                  _ = (Δ / A) * d ^ 2 * δ := by rw [← hDeltaSq]
                  _ = (Δ / A) * δ * d ^ 2 := by ring
              rw [hInside]
              have hMulAssoc :
                  (Δ / A) * δ * d ^ 2 = (Δ / A) * (δ * d ^ 2) := by ring
              calc
                Real.sqrt ((Δ / A) * δ * d ^ 2)
                    = Real.sqrt ((Δ / A) * (δ * d ^ 2)) := by rw [hMulAssoc]
                _ = Real.sqrt (Δ / A) * Real.sqrt (δ * d ^ 2) := by
                        rw [Real.sqrt_mul (div_nonneg hΔpos.le hApos.le)]
                _ = Real.sqrt (Δ / A) * (Real.sqrt δ * Real.sqrt (d ^ 2)) := by
                        rw [Real.sqrt_mul (by positivity)]
                _ = Real.sqrt (Δ / A) * (Real.sqrt δ * d) := by
                        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdPos.le]
                _ = Real.sqrt (Δ / A) * d * Real.sqrt δ := by ring
    have hScaleEq :
        d * r = Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
      have hRatioNonneg : 0 ≤ batchSize / N := div_nonneg hBatch.le hNpos.le
      have hRatioPos : 0 < batchSize / N := div_pos hBatch hNpos
      have hdEq : d = Real.rpow (batchSize / N) (1 / 2 : ℝ) := by
        simp [d, deltaScale, Real.sqrt_eq_rpow]
      have hrEq : r = Real.rpow (batchSize / N) (1 / 4 : ℝ) := by
        calc
          r = Real.sqrt d := by rfl
          _ = Real.sqrt (Real.sqrt (batchSize / N)) := by rfl
          _ = Real.rpow (batchSize / N) (1 / 4 : ℝ) := by
                rw [sqrt_sqrt_eq_rpow_quarter hRatioNonneg]
      calc
        d * r = Real.rpow (batchSize / N) (1 / 2 : ℝ) * Real.rpow (batchSize / N) (1 / 4 : ℝ) := by
          rw [hdEq, hrEq]
        _ = Real.rpow (batchSize / N) ((1 / 2 : ℝ) + (1 / 4 : ℝ)) := by
              symm
              exact Real.rpow_add hRatioPos (1 / 2 : ℝ) (1 / 4 : ℝ)
        _ = Real.rpow (batchSize / N) (3 / 4 : ℝ) := by norm_num
    have hEtaLower :
        cEtaLower * Real.rpow (batchSize / N) (3 / 4 : ℝ) ≤ etaStar N := by
      have hScaleLower :
          Real.sqrt (Δ / A) * cRootLower * Real.rpow (batchSize / N) (3 / 4 : ℝ)
            = (Real.sqrt (Δ / A) * d) * (cRootLower * r) := by
        calc
          Real.sqrt (Δ / A) * cRootLower * Real.rpow (batchSize / N) (3 / 4 : ℝ)
              = Real.sqrt (Δ / A) * cRootLower * (d * r) := by rw [← hScaleEq]
          _ = (Real.sqrt (Δ / A) * d) * (cRootLower * r) := by ring
      calc
        cEtaLower * Real.rpow (batchSize / N) (3 / 4 : ℝ)
            = (Real.sqrt (Δ / A) * d) * (cRootLower * r) := by
                simpa [cEtaLower, mul_assoc, mul_left_comm, mul_comm] using hScaleLower
        _ ≤ (Real.sqrt (Δ / A) * d) * Real.sqrt δ := by
              exact mul_le_mul_of_nonneg_left hRootLower (by positivity)
        _ = etaStar N := by
              symm
              rw [hEtaEq]
    have hEtaUpper :
        etaStar N ≤ cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
      have hScaleUpper :
          (Real.sqrt (Δ / A) * d) * (cRootUpper * r)
            = Real.sqrt (Δ / A) * cRootUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
        calc
          (Real.sqrt (Δ / A) * d) * (cRootUpper * r)
              = Real.sqrt (Δ / A) * cRootUpper * (d * r) := by ring
          _ = Real.sqrt (Δ / A) * cRootUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
                rw [hScaleEq]
      calc
        etaStar N = (Real.sqrt (Δ / A) * d) * Real.sqrt δ := by
              rw [hEtaEq]
        _ ≤ (Real.sqrt (Δ / A) * d) * (cRootUpper * r) := by
              exact mul_le_mul_of_nonneg_left hRootUpper (by positivity)
        _ = cEtaUpper * Real.rpow (batchSize / N) (3 / 4 : ℝ) := by
              simpa [cEtaUpper, mul_assoc, mul_left_comm, mul_comm] using hScaleUpper
    exact ⟨hGapLower, hGapUpper, hEtaLower, hEtaUpper⟩

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

theorem fWExpectedGapSLTheorem2_1_etaMinimizerEqClosedForm
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFrankWolfeGapLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar = Real.sqrt
      (S.fwGapLeadBiasCoeff * batchSize * (1 - β)
        / (S.fixedBatchFwGapLeadDriftConst * N)) := by
  simpa [etaStarFixedBatchClosedForm] using
    S.etaStarFixedBatch_eq hGap hN hBatch hβ1 hMin

theorem fWExpectedGapSLTheorem2_2_tokenBudgetScaling
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {batchSize : ℝ} (hBatch : 0 < batchSize)
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
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
    (hGap : 0 < S.fixedBatchFwGapInitialGap)
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
