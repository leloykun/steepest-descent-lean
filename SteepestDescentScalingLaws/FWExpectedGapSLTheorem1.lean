import SteepestDescentScalingLaws.Commons

namespace SteepestDescentOptimizationBounds

noncomputable section

namespace StochasticFrankWolfeGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
FW Expected Gap Scaling Laws Theorem 1: Fixed-Momentum Large-Horizon Proxy
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- The large-horizon initial-gradient coefficient for the fixed-momentum
Frank-Wolfe-gap proxy. -/
def fwGapProxyInitCoeff
    (S : StochasticFrankWolfeGeometryContext Ω V) (β : ℝ) : ℝ :=
  (2 * β / (S.lambda * (1 - β))) * S.initialGradNorm

/-- The large-horizon drift coefficient for the fixed-momentum
Frank-Wolfe-gap proxy. -/
def fwGapProxyDriftCoeff
    (S : StochasticFrankWolfeGeometryContext Ω V) (β : ℝ) : ℝ :=
  (2 * S.L / S.lambda) * (1 + 2 * β ^ 2 / (1 - β))

/-- The large-horizon minibatch-noise coefficient for the fixed-momentum
Frank-Wolfe-gap proxy. -/
def fwGapProxyNoiseCoeff
    (S : StochasticFrankWolfeGeometryContext Ω V) (β : ℝ) : ℝ :=
  (2 / S.lambda)
    * (β * Real.sqrt ((1 - β) / (1 + β)) + (1 - β))
    * Real.sqrt S.D
    * S.sigma

/-- Fixed-step Frank-Wolfe-gap proxy at fixed momentum. -/
def fwGapProxySL1
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η batchSize T β : ℝ) : ℝ :=
  S.suboptimality 0 / (S.lambda * η * T)
    + S.fwGapProxyInitCoeff β / T
    + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
    + S.fwGapProxyDriftCoeff β * η

/-- Token-budget Frank-Wolfe-gap proxy at fixed momentum. -/
def fwGapProxySL1Token
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η batchSize N β : ℝ) : ℝ :=
  S.suboptimality 0 * batchSize / (S.lambda * η * N)
    + S.fwGapProxyInitCoeff β * batchSize / N
    + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
    + S.fwGapProxyDriftCoeff β * η

/-- `η` minimizes the fixed-step Frank-Wolfe-gap proxy over positive learning
rates. -/
def IsFixedStepFrankWolfeGapProxyMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η batchSize T β : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.fwGapProxySL1 η batchSize T β ≤ S.fwGapProxySL1 η' batchSize T β

/-- `etaStepStar` selects fixed-step Frank-Wolfe-gap minimizers. -/
def IsFixedStepFrankWolfeGapProxyMinimizerFamily
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (β batchSize : ℝ) (etaStepStar : ℝ → ℝ) : Prop :=
  ∀ {T : ℝ}, 0 < T →
    S.IsFixedStepFrankWolfeGapProxyMinimizer (etaStepStar T) batchSize T β

/-- `η` minimizes the token-budget Frank-Wolfe-gap proxy over positive learning
rates. -/
def IsFixedTokenBudgetFrankWolfeGapProxyMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (η batchSize N β : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.fwGapProxySL1Token η batchSize N β ≤ S.fwGapProxySL1Token η' batchSize N β

/-- `etaTokenStar` selects token-budget Frank-Wolfe-gap minimizers. -/
def IsFixedTokenBudgetFrankWolfeGapProxyMinimizerFamily
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (β : ℝ) (etaTokenStar : ℝ → ℝ → ℝ) : Prop :=
  ∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
    S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizer (etaTokenStar N batchSize) batchSize N β

/-- Reduced token-budget Frank-Wolfe-gap proxy after minimizing out `η`. -/
def fixedMomentumFrankWolfeGapReducedProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  2 * Real.sqrt ((S.suboptimality 0 / S.lambda) * S.fwGapProxyDriftCoeff β * batchSize / N)
    + S.fwGapProxyInitCoeff β * batchSize / N
    + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize

/-- `batchSize` minimizes the reduced fixed-momentum Frank-Wolfe-gap proxy over
positive batch sizes. -/
def IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < batchSize ∧
    ∀ batchSize' > 0,
      S.fixedMomentumFrankWolfeGapReducedProxy N β batchSize
        ≤ S.fixedMomentumFrankWolfeGapReducedProxy N β batchSize'

/-- `batchSizeStar` selects reduced fixed-momentum Frank-Wolfe-gap batch
minimizers. -/
def IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizerFamily
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (β : ℝ) (batchSizeStar : ℝ → ℝ) : Prop :=
  ∀ {N : ℝ}, 0 < N →
    S.IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizer N β (batchSizeStar N)

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

private def fwGapBiasCoeff
    (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  S.suboptimality 0 / S.lambda

private def etaStarFixedStepsClosedForm
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (T β : ℝ) : ℝ :=
  Real.sqrt (S.fwGapBiasCoeff / (S.fwGapProxyDriftCoeff β * T))

private def etaStarFixedMomentumClosedForm
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  Real.sqrt (S.fwGapBiasCoeff * batchSize / (S.fwGapProxyDriftCoeff β * N))

private def quarterScale (N : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt N)

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

private theorem reciprocalLinearEqMinAddSq
    {a A η ηStar : ℝ}
    (hη : 0 < η)
    (hRel : a = A * ηStar ^ 2) :
    a / η + A * η = 2 * A * ηStar + A * (η - ηStar) ^ 2 / η := by
  field_simp [hη.ne']
  ring_nf
  nlinarith [hRel]

private theorem reciprocalLinearValueAtClosedForm
    {a A ηStar : ℝ}
    (hEtaStar : 0 < ηStar)
    (hRel : a = A * ηStar ^ 2) :
    a / ηStar + A * ηStar = 2 * A * ηStar := by
  field_simp [hEtaStar.ne']
  ring_nf
  nlinarith [hRel]

private theorem reciprocalLinearLtOfNe
    {a A η ηStar : ℝ}
    (hA : 0 < A) (hη : 0 < η)
    (hRel : a = A * ηStar ^ 2)
    (hNe : η ≠ ηStar) :
    2 * A * ηStar < a / η + A * η := by
  rw [reciprocalLinearEqMinAddSq hη hRel]
  have hSq : 0 < (η - ηStar) ^ 2 := by
    exact sq_pos_iff.mpr (sub_ne_zero.mpr hNe)
  have hTerm : 0 < A * (η - ηStar) ^ 2 / η := by
    positivity
  linarith

private theorem fwGapProxySL1_eq_const_add
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {η β batchSize T a A k : ℝ}
    (hη : 0 < η) (hT : 0 < T)
    (ha : a = S.fwGapBiasCoeff / T)
    (hA : A = S.fwGapProxyDriftCoeff β)
    (hk : k = S.fwGapProxyInitCoeff β / T + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize) :
    S.fwGapProxySL1 η batchSize T β = k + (a / η + A * η) := by
  subst ha hA hk
  unfold fwGapProxySL1 fwGapBiasCoeff
  field_simp [S.lambda_pos.ne', hη.ne', hT.ne']
  ring

private theorem fwGapProxySL1Token_eq_const_add
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {η β batchSize N a A k : ℝ}
    (hη : 0 < η) (hN : 0 < N)
    (ha : a = S.fwGapBiasCoeff * batchSize / N)
    (hA : A = S.fwGapProxyDriftCoeff β)
    (hk : k = S.fwGapProxyInitCoeff β * batchSize / N + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize) :
    S.fwGapProxySL1Token η batchSize N β = k + (a / η + A * η) := by
  subst ha hA hk
  unfold fwGapProxySL1Token fwGapBiasCoeff
  field_simp [S.lambda_pos.ne', hη.ne', hN.ne']
  ring

private theorem fwGapBiasCoeff_pos
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (hGap : 0 < S.suboptimality 0) :
    0 < S.fwGapBiasCoeff := by
  unfold fwGapBiasCoeff
  exact div_pos hGap S.lambda_pos

private theorem fwGapProxyInitCoeff_nonneg
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ S.fwGapProxyInitCoeff β := by
  unfold fwGapProxyInitCoeff
  have hDen : 0 ≤ S.lambda * (1 - β) := by
    exact mul_nonneg S.lambda_pos.le (sub_nonneg.mpr hβ1.le)
  have hFrac : 0 ≤ 2 * β / (S.lambda * (1 - β)) := by
    exact div_nonneg (by positivity) hDen
  exact mul_nonneg hFrac (norm_nonneg _)

private theorem fwGapProxyDriftCoeff_pos
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (_hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 < S.fwGapProxyDriftCoeff β := by
  unfold fwGapProxyDriftCoeff
  have hCoeff : 0 < 2 * S.L / S.lambda := by
    exact div_pos (mul_pos (by norm_num) S.L_pos) S.lambda_pos
  have hFrac : 0 ≤ 2 * β ^ 2 / (1 - β) := by
    exact div_nonneg (by positivity) (sub_nonneg.mpr hβ1.le)
  refine mul_pos hCoeff ?_
  linarith

private theorem fwGapProxyNoiseCoeff_nonneg
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ S.fwGapProxyNoiseCoeff β := by
  unfold fwGapProxyNoiseCoeff
  have hMid : 0 ≤ β * Real.sqrt ((1 - β) / (1 + β)) + (1 - β) := by
    have hSqrt : 0 ≤ Real.sqrt ((1 - β) / (1 + β)) := Real.sqrt_nonneg _
    have hFirst : 0 ≤ β * Real.sqrt ((1 - β) / (1 + β)) := by
      exact mul_nonneg hβ0 hSqrt
    linarith
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (div_nonneg (by norm_num) S.lambda_pos.le) hMid) (Real.sqrt_nonneg _))
    S.sigma_nonneg

private theorem etaStarFixedStepsClosedForm_sq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β T : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0) (hT : 0 < T) :
    (S.etaStarFixedStepsClosedForm T β) ^ 2
      = S.fwGapBiasCoeff / (S.fwGapProxyDriftCoeff β * T) := by
  unfold etaStarFixedStepsClosedForm
  simpa using
    (Real.sq_sqrt
      (show 0 ≤ S.fwGapBiasCoeff / (S.fwGapProxyDriftCoeff β * T) by
        exact div_nonneg (S.fwGapBiasCoeff_pos hGap).le
          (mul_nonneg (S.fwGapProxyDriftCoeff_pos hβ0 hβ1).le hT.le)))

private theorem etaStarFixedMomentumClosedForm_sq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β N batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize) :
    (S.etaStarFixedMomentumClosedForm N β batchSize) ^ 2
      = S.fwGapBiasCoeff * batchSize / (S.fwGapProxyDriftCoeff β * N) := by
  unfold etaStarFixedMomentumClosedForm
  simpa using
    (Real.sq_sqrt
      (show 0 ≤ S.fwGapBiasCoeff * batchSize / (S.fwGapProxyDriftCoeff β * N) by
        exact div_nonneg (mul_nonneg (S.fwGapBiasCoeff_pos hGap).le hBatch.le)
          (mul_nonneg (S.fwGapProxyDriftCoeff_pos hβ0 hβ1).le hN.le)))

private theorem closedForm_fixedStep_isMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize T : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hT : 0 < T) :
    S.IsFixedStepFrankWolfeGapProxyMinimizer
      (S.etaStarFixedStepsClosedForm T β) batchSize T β := by
  let a : ℝ := S.fwGapBiasCoeff / T
  let A : ℝ := S.fwGapProxyDriftCoeff β
  let k : ℝ := S.fwGapProxyInitCoeff β / T + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
  let etaStar : ℝ := S.etaStarFixedStepsClosedForm T β
  have hApos : 0 < A := S.fwGapProxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (S.fwGapBiasCoeff_pos hGap) hT
  have hEtaStarPos : 0 < etaStar := by
    dsimp [etaStar]
    refine Real.sqrt_pos.2 ?_
    exact div_pos (S.fwGapBiasCoeff_pos hGap) (mul_pos hApos hT)
  have hRel : a = A * etaStar ^ 2 := by
    calc
      a = S.fwGapBiasCoeff / T := by rfl
      _ = A * (S.fwGapBiasCoeff / (A * T)) := by
            field_simp [hApos.ne', hT.ne']
      _ = A * etaStar ^ 2 := by
            rw [S.etaStarFixedStepsClosedForm_sq hβ0 hβ1 hGap hT]
  refine ⟨hEtaStarPos, ?_⟩
  intro η hη
  have hCore :
      2 * A * etaStar ≤ a / η + A * η := by
    rw [reciprocalLinearEqMinAddSq hη hRel]
    have hTerm : 0 ≤ A * (η - etaStar) ^ 2 / η := by positivity
    linarith
  calc
    S.fwGapProxySL1 etaStar batchSize T β
      = k + (a / etaStar + A * etaStar) := by
          exact S.fwGapProxySL1_eq_const_add hEtaStarPos hT rfl rfl rfl
    _ = k + 2 * A * etaStar := by
          rw [reciprocalLinearValueAtClosedForm hEtaStarPos hRel]
    _ ≤ k + (a / η + A * η) := by gcongr
    _ = S.fwGapProxySL1 η batchSize T β := by
          symm
          exact S.fwGapProxySL1_eq_const_add hη hT rfl rfl rfl

private theorem closedForm_fixedStep_lt_of_ne
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize T η : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hT : 0 < T) (hη : 0 < η)
    (hNe : η ≠ S.etaStarFixedStepsClosedForm T β) :
    S.fwGapProxySL1 (S.etaStarFixedStepsClosedForm T β) batchSize T β
      < S.fwGapProxySL1 η batchSize T β := by
  let a : ℝ := S.fwGapBiasCoeff / T
  let A : ℝ := S.fwGapProxyDriftCoeff β
  let k : ℝ := S.fwGapProxyInitCoeff β / T + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
  let etaStar : ℝ := S.etaStarFixedStepsClosedForm T β
  have hApos : 0 < A := S.fwGapProxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (S.fwGapBiasCoeff_pos hGap) hT
  have hEtaStarPos : 0 < etaStar := by
    dsimp [etaStar]
    refine Real.sqrt_pos.2 ?_
    exact div_pos (S.fwGapBiasCoeff_pos hGap) (mul_pos hApos hT)
  have hRel : a = A * etaStar ^ 2 := by
    calc
      a = S.fwGapBiasCoeff / T := by rfl
      _ = A * (S.fwGapBiasCoeff / (A * T)) := by
            field_simp [hApos.ne', hT.ne']
      _ = A * etaStar ^ 2 := by
            rw [S.etaStarFixedStepsClosedForm_sq hβ0 hβ1 hGap hT]
  have hCore : 2 * A * etaStar < a / η + A * η :=
    reciprocalLinearLtOfNe hApos hη hRel <| by
      simpa [etaStar] using hNe
  calc
    S.fwGapProxySL1 etaStar batchSize T β
      = k + (a / etaStar + A * etaStar) := by
          exact S.fwGapProxySL1_eq_const_add hEtaStarPos hT rfl rfl rfl
    _ = k + 2 * A * etaStar := by
          rw [reciprocalLinearValueAtClosedForm hEtaStarPos hRel]
    _ < k + (a / η + A * η) := by gcongr
    _ = S.fwGapProxySL1 η batchSize T β := by
          symm
          exact S.fwGapProxySL1_eq_const_add hη hT rfl rfl rfl

private theorem etaStarFixedSteps_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize T ηStar : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hT : 0 < T)
    (hMin : S.IsFixedStepFrankWolfeGapProxyMinimizer ηStar batchSize T β) :
    ηStar = S.etaStarFixedStepsClosedForm T β := by
  by_contra hNe
  have hClosedMin := S.closedForm_fixedStep_isMinimizer (batchSize := batchSize) hβ0 hβ1 hGap hT
  have hLt := S.closedForm_fixedStep_lt_of_ne
      (batchSize := batchSize) (η := ηStar) hβ0 hβ1 hGap hT hMin.1 hNe
  have hLe := hMin.2 (S.etaStarFixedStepsClosedForm T β) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedStepClosedFormFamily_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    {etaStepStar : ℝ → ℝ}
    (hMin : S.IsFixedStepFrankWolfeGapProxyMinimizerFamily β batchSize etaStepStar) :
    ∀ {T : ℝ}, 0 < T →
      etaStepStar T = S.etaStarFixedStepsClosedForm T β := by
  intro T hT
  exact S.etaStarFixedSteps_eq hβ0 hβ1 hGap hT (hMin hT)

private theorem fixedStepIterationScalingBounds
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    {etaStepStar : ℝ → ℝ}
    (hMin : S.IsFixedStepFrankWolfeGapProxyMinimizerFamily β batchSize etaStepStar) :
    ∃ cLower cUpper T0,
      0 < cLower ∧ 0 < cUpper ∧ 0 < T0 ∧
      ∀ T ≥ T0,
        cLower / Real.rpow T (1 / 2 : ℝ) ≤ etaStepStar T ∧
        etaStepStar T ≤ cUpper / Real.rpow T (1 / 2 : ℝ) := by
  let c : ℝ := Real.sqrt (S.fwGapBiasCoeff / S.fwGapProxyDriftCoeff β)
  have hcPos : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 (div_pos (S.fwGapBiasCoeff_pos hGap) (S.fwGapProxyDriftCoeff_pos hβ0 hβ1))
  refine ⟨c, c, 1, hcPos, hcPos, by norm_num, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hT
  have hEq : etaStepStar T = S.etaStarFixedStepsClosedForm T β := S.fixedStepClosedFormFamily_eq hβ0 hβ1 hGap hMin hTpos
  have hRewrite :
      S.etaStarFixedStepsClosedForm T β = c / Real.rpow T (1 / 2 : ℝ) := by
    unfold etaStarFixedStepsClosedForm c fwGapBiasCoeff
    rw [show S.suboptimality 0 / S.lambda / (S.fwGapProxyDriftCoeff β * T)
        = (S.suboptimality 0 / S.lambda / S.fwGapProxyDriftCoeff β) / T by
          field_simp [(S.fwGapProxyDriftCoeff_pos hβ0 hβ1).ne', S.lambda_pos.ne', hTpos.ne']]
    rw [Real.sqrt_div]
    · simp [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_left_comm, mul_comm]
    · exact div_nonneg
        (div_nonneg (le_of_lt hGap) S.lambda_pos.le)
        (S.fwGapProxyDriftCoeff_pos hβ0 hβ1).le
  constructor <;> simpa [hEq, hRewrite]

private theorem closedForm_fixedToken_isMinimizer
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β N batchSize : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize) :
    S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizer
      (S.etaStarFixedMomentumClosedForm N β batchSize) batchSize N β := by
  let a : ℝ := S.fwGapBiasCoeff * batchSize / N
  let A : ℝ := S.fwGapProxyDriftCoeff β
  let k : ℝ := S.fwGapProxyInitCoeff β * batchSize / N + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
  let etaStar : ℝ := S.etaStarFixedMomentumClosedForm N β batchSize
  have hApos : 0 < A := S.fwGapProxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (S.fwGapBiasCoeff_pos hGap) hBatch) hN
  have hEtaStarPos : 0 < etaStar := by
    dsimp [etaStar]
    refine Real.sqrt_pos.2 ?_
    exact div_pos (mul_pos (S.fwGapBiasCoeff_pos hGap) hBatch) (mul_pos hApos hN)
  have hRel : a = A * etaStar ^ 2 := by
    calc
      a = S.fwGapBiasCoeff * batchSize / N := by rfl
      _ = A * (S.fwGapBiasCoeff * batchSize / (A * N)) := by
            field_simp [hApos.ne', hN.ne']
      _ = A * etaStar ^ 2 := by
            rw [S.etaStarFixedMomentumClosedForm_sq hβ0 hβ1 hGap hN hBatch]
  refine ⟨hEtaStarPos, ?_⟩
  intro η hη
  have hCore :
      2 * A * etaStar ≤ a / η + A * η := by
    rw [reciprocalLinearEqMinAddSq hη hRel]
    have hTerm : 0 ≤ A * (η - etaStar) ^ 2 / η := by positivity
    linarith
  calc
    S.fwGapProxySL1Token etaStar batchSize N β
      = k + (a / etaStar + A * etaStar) := by
          exact S.fwGapProxySL1Token_eq_const_add hEtaStarPos hN rfl rfl rfl
    _ = k + 2 * A * etaStar := by
          rw [reciprocalLinearValueAtClosedForm hEtaStarPos hRel]
    _ ≤ k + (a / η + A * η) := by gcongr
    _ = S.fwGapProxySL1Token η batchSize N β := by
          symm
          exact S.fwGapProxySL1Token_eq_const_add hη hN rfl rfl rfl

private theorem closedForm_fixedToken_lt_of_ne
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β N batchSize η : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hη : 0 < η)
    (hNe : η ≠ S.etaStarFixedMomentumClosedForm N β batchSize) :
    S.fwGapProxySL1Token (S.etaStarFixedMomentumClosedForm N β batchSize) batchSize N β
      < S.fwGapProxySL1Token η batchSize N β := by
  let a : ℝ := S.fwGapBiasCoeff * batchSize / N
  let A : ℝ := S.fwGapProxyDriftCoeff β
  let k : ℝ := S.fwGapProxyInitCoeff β * batchSize / N + S.fwGapProxyNoiseCoeff β / Real.sqrt batchSize
  let etaStar : ℝ := S.etaStarFixedMomentumClosedForm N β batchSize
  have hApos : 0 < A := S.fwGapProxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (S.fwGapBiasCoeff_pos hGap) hBatch) hN
  have hEtaStarPos : 0 < etaStar := by
    dsimp [etaStar]
    refine Real.sqrt_pos.2 ?_
    exact div_pos (mul_pos (S.fwGapBiasCoeff_pos hGap) hBatch) (mul_pos hApos hN)
  have hRel : a = A * etaStar ^ 2 := by
    calc
      a = S.fwGapBiasCoeff * batchSize / N := by rfl
      _ = A * (S.fwGapBiasCoeff * batchSize / (A * N)) := by
            field_simp [hApos.ne', hN.ne']
      _ = A * etaStar ^ 2 := by
            rw [S.etaStarFixedMomentumClosedForm_sq hβ0 hβ1 hGap hN hBatch]
  have hCore : 2 * A * etaStar < a / η + A * η :=
    reciprocalLinearLtOfNe hApos hη hRel <| by
      simpa [etaStar] using hNe
  calc
    S.fwGapProxySL1Token etaStar batchSize N β
      = k + (a / etaStar + A * etaStar) := by
          exact S.fwGapProxySL1Token_eq_const_add hEtaStarPos hN rfl rfl rfl
    _ = k + 2 * A * etaStar := by
          rw [reciprocalLinearValueAtClosedForm hEtaStarPos hRel]
    _ < k + (a / η + A * η) := by gcongr
    _ = S.fwGapProxySL1Token η batchSize N β := by
          symm
          exact S.fwGapProxySL1Token_eq_const_add hη hN rfl rfl rfl

private theorem etaStarFixedMomentum_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize N ηStar : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hMin : S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizer ηStar batchSize N β) :
    ηStar = S.etaStarFixedMomentumClosedForm N β batchSize := by
  by_contra hNe
  have hClosedMin := S.closedForm_fixedToken_isMinimizer hβ0 hβ1 hGap hN hBatch
  have hLt := S.closedForm_fixedToken_lt_of_ne
      (η := ηStar) hβ0 hβ1 hGap hN hBatch hMin.1 hNe
  have hLe := hMin.2 (S.etaStarFixedMomentumClosedForm N β batchSize) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedTokenClosedFormFamily_eq
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hMin : S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizerFamily β etaTokenStar) :
    ∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
      etaTokenStar N batchSize = S.etaStarFixedMomentumClosedForm N β batchSize := by
  intro N batchSize hN hBatch
  exact S.etaStarFixedMomentum_eq hβ0 hβ1 hGap hN hBatch (hMin hN hBatch)

private theorem quarterScale_pos {N : ℝ} (hN : 0 < N) :
    0 < quarterScale N := by
  unfold quarterScale
  exact Real.sqrt_pos.2 <| Real.sqrt_pos.2 hN

private theorem quarterScale_sq {N : ℝ} (hN : 0 < N) :
    (quarterScale N) ^ 2 = Real.sqrt N := by
  unfold quarterScale
  simpa [pow_two] using (Real.sq_sqrt (Real.sqrt_nonneg N))

private theorem fixedMomentumFrankWolfeGapTokenBudgetScalingBounds
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fwGapProxyNoiseCoeff β)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizerFamily β batchSizeStar)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hEtaMin : S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizerFamily β etaTokenStar) :
    ∃ cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
      0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBatchLower * Real.rpow N (1 / 2 : ℝ) ≤ batchSizeStar N ∧
        batchSizeStar N ≤ cBatchUpper * Real.rpow N (1 / 2 : ℝ) ∧
        cEtaLower / Real.rpow N (1 / 4 : ℝ) ≤ etaTokenStar N (batchSizeStar N) ∧
        etaTokenStar N (batchSizeStar N) ≤ cEtaUpper / Real.rpow N (1 / 4 : ℝ) := by
  let Δ : ℝ := S.fwGapBiasCoeff
  let A : ℝ := S.fwGapProxyDriftCoeff β
  let C : ℝ := S.fwGapProxyInitCoeff β
  let B : ℝ := S.fwGapProxyNoiseCoeff β
  let K : ℝ := 2 * Real.sqrt (Δ * A) + C + B
  have hΔpos : 0 < Δ := S.fwGapBiasCoeff_pos hGap
  have hApos : 0 < A := S.fwGapProxyDriftCoeff_pos hβ0 hβ1
  have hCnonneg : 0 ≤ C := S.fwGapProxyInitCoeff_nonneg hβ0 hβ1
  have hBpos : 0 < B := hNoise
  have hKpos : 0 < K := by
    have : 0 < 2 * Real.sqrt (Δ * A) := by
      refine mul_pos (by norm_num) ?_
      exact Real.sqrt_pos.2 (mul_pos hΔpos hApos)
    linarith
  refine ⟨(B / K) ^ 2, (K / (2 * Real.sqrt (Δ * A))) ^ 2,
    Real.sqrt (Δ / A) * (B / K), Real.sqrt (Δ / A) * (K / (2 * Real.sqrt (Δ * A))),
    1,
    ?_, ?_, ?_, ?_, by norm_num, ?_⟩
  · positivity
  · positivity
  · positivity
  · positivity
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hN
  have hMin := hBatchMin hNpos
  have hBatchPos : 0 < batchSizeStar N := hMin.1
  let rN : ℝ := quarterScale N
  have hrNpos : 0 < rN := quarterScale_pos hNpos
  have hSqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hRNSq : rN ^ 2 = Real.sqrt N := quarterScale_sq hNpos
  have hRatio :
      Real.sqrt N / N = 1 / Real.sqrt N := by
    field_simp [hNpos.ne']
    simpa [pow_two] using (Real.sq_sqrt hNpos.le)
  have hQuarterInv : Real.sqrt (1 / Real.sqrt N) = 1 / rN := by
    dsimp [rN, quarterScale]
    rw [show 1 / Real.sqrt N = (Real.sqrt N)⁻¹ by simp [one_div]]
    rw [Real.sqrt_inv]
    simp [one_div]
  have hCandidateLe :
      S.fixedMomentumFrankWolfeGapReducedProxy N β (Real.sqrt N) ≤ K / rN := by
    have hTerm1 :
        2 * Real.sqrt (Δ * A * Real.sqrt N / N) = (2 * Real.sqrt (Δ * A)) / rN := by
      have hEq :
          Δ * A * Real.sqrt N / N = (Δ * A) * (1 / Real.sqrt N) := by
        rw [show Δ * A * Real.sqrt N / N = (Δ * A) * (Real.sqrt N / N) by ring]
        rw [hRatio]
      calc
        2 * Real.sqrt (Δ * A * Real.sqrt N / N)
            = 2 * Real.sqrt ((Δ * A) * (1 / Real.sqrt N)) := by rw [hEq]
        _ = 2 * (Real.sqrt (Δ * A) * Real.sqrt (1 / Real.sqrt N)) := by
              rw [Real.sqrt_mul (mul_nonneg hΔpos.le hApos.le)]
        _ = 2 * (Real.sqrt (Δ * A) * (1 / rN)) := by rw [hQuarterInv]
        _ = (2 * Real.sqrt (Δ * A)) / rN := by ring
    have hTerm2 :
        C * Real.sqrt N / N ≤ C / rN := by
      have hInv : 0 ≤ 1 / Real.sqrt N := one_div_nonneg.mpr hSqrtNpos.le
      have hInvLeOne : 1 / Real.sqrt N ≤ 1 := by
        have hOneLeSqrtN : 1 ≤ Real.sqrt N := by
          simpa using (Real.sqrt_le_sqrt hN)
        exact (one_div_le hSqrtNpos (by positivity : (0 : ℝ) < 1)).2 <| by
          simpa using hOneLeSqrtN
      have hLe : 1 / Real.sqrt N ≤ 1 / rN := by
        calc
          1 / Real.sqrt N ≤ Real.sqrt (1 / Real.sqrt N) :=
            le_sqrt_of_nonneg_of_le_one hInv hInvLeOne
          _ = 1 / rN := hQuarterInv
      calc
        C * Real.sqrt N / N = C * (Real.sqrt N / N) := by ring
        _ = C * (1 / Real.sqrt N) := by rw [hRatio]
        _ ≤ C * (1 / rN) := by gcongr
        _ = C / rN := by ring
    calc
      S.fixedMomentumFrankWolfeGapReducedProxy N β (Real.sqrt N)
          = 2 * Real.sqrt (Δ * A * Real.sqrt N / N)
              + C * Real.sqrt N / N
              + B / rN := by
                simp [fixedMomentumFrankWolfeGapReducedProxy, Δ, A, C, B, rN, quarterScale, fwGapBiasCoeff]
      _ = (2 * Real.sqrt (Δ * A)) / rN + C * Real.sqrt N / N + B / rN := by rw [hTerm1]
      _ ≤ (2 * Real.sqrt (Δ * A)) / rN + C / rN + B / rN := by gcongr
      _ = K / rN := by
            field_simp [hrNpos.ne']
            ring
  have hMinLeCandidate := hMin.2 (Real.sqrt N) (Real.sqrt_pos.2 hNpos)
  have hBound : S.fixedMomentumFrankWolfeGapReducedProxy N β (batchSizeStar N) ≤ K / rN := by
    exact le_trans hMinLeCandidate hCandidateLe
  have hFirst :
      2 * Real.sqrt (Δ * A * batchSizeStar N / N) ≤ K / rN := by
    have hRestNonneg :
        0 ≤ C * batchSizeStar N / N + B / Real.sqrt (batchSizeStar N) := by
      positivity
    have hEq :
        S.fixedMomentumFrankWolfeGapReducedProxy N β (batchSizeStar N)
          = 2 * Real.sqrt (Δ * A * batchSizeStar N / N)
              + (C * batchSizeStar N / N + B / Real.sqrt (batchSizeStar N)) := by
      simp [fixedMomentumFrankWolfeGapReducedProxy, Δ, A, C, B, fwGapBiasCoeff, add_assoc]
    rw [hEq] at hBound
    linarith
  have hThird :
      B / Real.sqrt (batchSizeStar N) ≤ K / rN := by
    have hRestNonneg :
        0 ≤ 2 * Real.sqrt (Δ * A * batchSizeStar N / N) + C * batchSizeStar N / N := by
      positivity
    have hEq :
        S.fixedMomentumFrankWolfeGapReducedProxy N β (batchSizeStar N)
          = (2 * Real.sqrt (Δ * A * batchSizeStar N / N) + C * batchSizeStar N / N)
              + B / Real.sqrt (batchSizeStar N) := by
      simp [fixedMomentumFrankWolfeGapReducedProxy, Δ, A, C, B, fwGapBiasCoeff, add_assoc]
    rw [hEq] at hBound
    linarith
  have hFirstRewrite :
      2 * Real.sqrt (Δ * A * batchSizeStar N / N)
        = (2 * Real.sqrt (Δ * A) * Real.sqrt (batchSizeStar N)) / Real.sqrt N := by
    rw [show Δ * A * batchSizeStar N / N = (Δ * A * batchSizeStar N) / N by ring]
    rw [Real.sqrt_div]
    · rw [show Δ * A * batchSizeStar N = (Δ * A) * batchSizeStar N by ring]
      rw [Real.sqrt_mul (mul_nonneg hΔpos.le hApos.le)]
      ring
    · positivity
  have hRatioSqrt : Real.sqrt N / rN = rN := by
    apply (div_eq_iff hrNpos.ne').2
    simpa [pow_two] using Eq.symm hRNSq
  have hFirst' :
      (2 * Real.sqrt (Δ * A) * Real.sqrt (batchSizeStar N)) / Real.sqrt N ≤ K / rN := by
    simpa [hFirstRewrite] using hFirst
  have hMulUpper := mul_le_mul_of_nonneg_right hFirst' hSqrtNpos.le
  have hMidUpper :
      2 * Real.sqrt (Δ * A) * Real.sqrt (batchSizeStar N) ≤ K * rN := by
    calc
      2 * Real.sqrt (Δ * A) * Real.sqrt (batchSizeStar N)
          = ((2 * Real.sqrt (Δ * A) * Real.sqrt (batchSizeStar N)) / Real.sqrt N) * Real.sqrt N := by
              field_simp [hSqrtNpos.ne']
      _ ≤ (K / rN) * Real.sqrt N := hMulUpper
      _ = K * (Real.sqrt N / rN) := by ring
      _ = K * rN := by rw [hRatioSqrt]
  have hUpperRoot :
      Real.sqrt (batchSizeStar N) ≤ (K / (2 * Real.sqrt (Δ * A))) * rN := by
    have hUpperRoot' :
        Real.sqrt (batchSizeStar N) ≤ (K * rN) / (2 * Real.sqrt (Δ * A)) := by
      exact (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (Δ * A))).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hMidUpper
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hUpperRoot'
  have hLowerRoot :
      (B / K) * rN ≤ Real.sqrt (batchSizeStar N) := by
    have hMulLower := mul_le_mul_of_nonneg_right hThird
        (mul_nonneg (Real.sqrt_nonneg (batchSizeStar N)) hrNpos.le)
    have hMidLower :
        B * rN ≤ K * Real.sqrt (batchSizeStar N) := by
      calc
        B * rN = (B / Real.sqrt (batchSizeStar N)) * (Real.sqrt (batchSizeStar N) * rN) := by
          field_simp [hBatchPos.ne']
        _ ≤ (K / rN) * (Real.sqrt (batchSizeStar N) * rN) := hMulLower
        _ = K * Real.sqrt (batchSizeStar N) := by
          field_simp [hrNpos.ne']
    have hLowerRoot' : (B * rN) / K ≤ Real.sqrt (batchSizeStar N) := by
      exact (div_le_iff₀ hKpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hMidLower
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hLowerRoot'
  have hBatchLower :
      (B / K) ^ 2 * Real.rpow N (1 / 2 : ℝ) ≤ batchSizeStar N := by
    have hSq := mul_self_le_mul_self (by positivity : 0 ≤ (B / K) * rN) hLowerRoot
    have hLeft :
        ((B / K) * rN) * ((B / K) * rN)
          = (B / K) ^ 2 * Real.rpow N (1 / 2 : ℝ) := by
      calc
        ((B / K) * rN) * ((B / K) * rN) = (B / K) ^ 2 * (rN * rN) := by ring
        _ = (B / K) ^ 2 * Real.rpow N (1 / 2 : ℝ) := by
              rw [show rN * rN = Real.sqrt N by simpa [pow_two] using hRNSq]
              simpa [Real.sqrt_eq_rpow]
    have hRight :
        Real.sqrt (batchSizeStar N) * Real.sqrt (batchSizeStar N) = batchSizeStar N := by
      simpa [pow_two] using (Real.sq_sqrt hBatchPos.le)
    simpa [hLeft, hRight] using hSq
  have hBatchUpper :
      batchSizeStar N ≤ (K / (2 * Real.sqrt (Δ * A))) ^ 2 * Real.rpow N (1 / 2 : ℝ) := by
    have hSq := mul_self_le_mul_self (Real.sqrt_nonneg (batchSizeStar N)) hUpperRoot
    have hLeft :
        Real.sqrt (batchSizeStar N) * Real.sqrt (batchSizeStar N) = batchSizeStar N := by
      simpa [pow_two] using (Real.sq_sqrt hBatchPos.le)
    have hRight :
        ((K / (2 * Real.sqrt (Δ * A))) * rN)
            * ((K / (2 * Real.sqrt (Δ * A))) * rN)
          = (K / (2 * Real.sqrt (Δ * A))) ^ 2 * Real.rpow N (1 / 2 : ℝ) := by
      calc
        ((K / (2 * Real.sqrt (Δ * A))) * rN)
            * ((K / (2 * Real.sqrt (Δ * A))) * rN)
            = (K / (2 * Real.sqrt (Δ * A))) ^ 2 * (rN * rN) := by ring
        _ = (K / (2 * Real.sqrt (Δ * A))) ^ 2 * Real.rpow N (1 / 2 : ℝ) := by
              rw [show rN * rN = Real.sqrt N by simpa [pow_two] using hRNSq]
              simpa [Real.sqrt_eq_rpow]
    simpa [hLeft, hRight] using hSq
  have hEtaEqClosed :
      etaTokenStar N (batchSizeStar N) = S.etaStarFixedMomentumClosedForm N β (batchSizeStar N) := by
    exact S.fixedTokenClosedFormFamily_eq hβ0 hβ1 hGap hEtaMin hNpos hBatchPos
  have hEtaConstPos : 0 < Real.sqrt (Δ / A) := by
    exact Real.sqrt_pos.2 (div_pos hΔpos hApos)
  have hEtaCore :
      etaTokenStar N (batchSizeStar N)
        = Real.sqrt (Δ / A) * Real.sqrt (batchSizeStar N) / Real.sqrt N := by
    calc
      etaTokenStar N (batchSizeStar N)
          = S.etaStarFixedMomentumClosedForm N β (batchSizeStar N) := hEtaEqClosed
      _ = Real.sqrt ((Δ / A) * (batchSizeStar N / N)) := by
            unfold etaStarFixedMomentumClosedForm
            rw [show S.fwGapBiasCoeff * batchSizeStar N / (S.fwGapProxyDriftCoeff β * N)
                  = (Δ / A) * (batchSizeStar N / N) by
                    field_simp [Δ, A, hApos.ne', hNpos.ne']
                    ring]
      _ = Real.sqrt (Δ / A) * Real.sqrt (batchSizeStar N / N) := by
            rw [Real.sqrt_mul (div_nonneg hΔpos.le hApos.le)]
      _ = Real.sqrt (Δ / A) * (Real.sqrt (batchSizeStar N) / Real.sqrt N) := by
            rw [Real.sqrt_div hBatchPos.le]
      _ = Real.sqrt (Δ / A) * Real.sqrt (batchSizeStar N) / Real.sqrt N := by ring
  have hEtaLower :
      (Real.sqrt (Δ / A) * (B / K)) / Real.rpow N (1 / 4 : ℝ)
        ≤ etaTokenStar N (batchSizeStar N) := by
    have hQuarterRatio : rN / Real.sqrt N = 1 / rN := by
      field_simp [hrNpos.ne', hSqrtNpos.ne']
      simpa [pow_two] using hRNSq
    calc
      (Real.sqrt (Δ / A) * (B / K)) / Real.rpow N (1 / 4 : ℝ)
          = Real.sqrt (Δ / A) * ((B / K) / rN) := by
                rw [← sqrt_sqrt_eq_rpow_quarter hNpos.le]
                dsimp [rN, quarterScale]
                ring
      _ = Real.sqrt (Δ / A) * ((B / K) * rN / Real.sqrt N) := by
            rw [show (B / K) / rN = (B / K) * (rN / Real.sqrt N) by
                  rw [hQuarterRatio]
                  ring]
            ring
      _ ≤ Real.sqrt (Δ / A) * (Real.sqrt (batchSizeStar N) / Real.sqrt N) := by
            gcongr
      _ = etaTokenStar N (batchSizeStar N) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEtaCore.symm
  have hEtaUpper :
      etaTokenStar N (batchSizeStar N)
        ≤ (Real.sqrt (Δ / A) * (K / (2 * Real.sqrt (Δ * A)))) / Real.rpow N (1 / 4 : ℝ) := by
    have hQuarterRatio : rN / Real.sqrt N = 1 / rN := by
      field_simp [hrNpos.ne', hSqrtNpos.ne']
      simpa [pow_two] using hRNSq
    calc
      etaTokenStar N (batchSizeStar N)
          = Real.sqrt (Δ / A) * (Real.sqrt (batchSizeStar N) / Real.sqrt N) := by
              rw [hEtaCore]
              ring
      _ ≤ Real.sqrt (Δ / A) * (((K / (2 * Real.sqrt (Δ * A))) * rN) / Real.sqrt N) := by
            gcongr
      _ = Real.sqrt (Δ / A) * ((K / (2 * Real.sqrt (Δ * A))) / rN) := by
            rw [show ((K / (2 * Real.sqrt (Δ * A))) * rN) / Real.sqrt N
                  = (K / (2 * Real.sqrt (Δ * A))) * (rN / Real.sqrt N) by ring]
            rw [hQuarterRatio]
            ring
      _ = (Real.sqrt (Δ / A) * (K / (2 * Real.sqrt (Δ * A)))) / Real.rpow N (1 / 4 : ℝ) := by
            rw [← sqrt_sqrt_eq_rpow_quarter hNpos.le]
            dsimp [rN, quarterScale]
            ring
  exact ⟨hBatchLower, hBatchUpper, hEtaLower, hEtaUpper⟩

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

theorem fWExpectedGapSLTheorem1_1_iterationScaling
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0) :
    ∀ {etaStepStar : ℝ → ℝ},
      S.IsFixedStepFrankWolfeGapProxyMinimizerFamily β batchSize etaStepStar →
      (∀ {T : ℝ}, 0 < T →
        etaStepStar T = S.etaStarFixedStepsClosedForm T β) ∧
      ∃ cLower cUpper T0,
        0 < cLower ∧ 0 < cUpper ∧ 0 < T0 ∧
        ∀ T ≥ T0,
          cLower / Real.rpow T (1 / 2 : ℝ) ≤ etaStepStar T ∧
          etaStepStar T ≤ cUpper / Real.rpow T (1 / 2 : ℝ) := by
  intro etaStepStar hMin
  exact ⟨S.fixedStepClosedFormFamily_eq hβ0 hβ1 hGap hMin,
    S.fixedStepIterationScalingBounds hβ0 hβ1 hGap hMin⟩

theorem fWExpectedGapSLTheorem1_2_tokenBudgetScaling
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fwGapProxyNoiseCoeff β)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizerFamily β batchSizeStar) :
    ∀ {etaTokenStar : ℝ → ℝ → ℝ},
      S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizerFamily β etaTokenStar →
      (∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
        etaTokenStar N batchSize = S.etaStarFixedMomentumClosedForm N β batchSize) ∧
      ∃ cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
        0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
        ∀ N ≥ N0,
          cBatchLower * Real.rpow N (1 / 2 : ℝ) ≤ batchSizeStar N ∧
          batchSizeStar N ≤ cBatchUpper * Real.rpow N (1 / 2 : ℝ) ∧
          cEtaLower / Real.rpow N (1 / 4 : ℝ) ≤ etaTokenStar N (batchSizeStar N) ∧
          etaTokenStar N (batchSizeStar N) ≤ cEtaUpper / Real.rpow N (1 / 4 : ℝ) := by
  intro etaTokenStar hEtaMin
  exact ⟨S.fixedTokenClosedFormFamily_eq hβ0 hβ1 hGap hEtaMin,
    S.fixedMomentumFrankWolfeGapTokenBudgetScalingBounds hβ0 hβ1 hGap hNoise hBatchMin hEtaMin⟩

theorem fWExpectedGapSLTheorem1_FixedMomentumLargeHorizonProxy
    (S : StochasticFrankWolfeGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.suboptimality 0)
    (hNoise : 0 < S.fwGapProxyNoiseCoeff β)
    {etaStepStar : ℝ → ℝ}
    (hStepMin : S.IsFixedStepFrankWolfeGapProxyMinimizerFamily β batchSize etaStepStar)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hTokenMin : S.IsFixedTokenBudgetFrankWolfeGapProxyMinimizerFamily β etaTokenStar)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsFixedMomentumFrankWolfeGapReducedProxyBatchMinimizerFamily β batchSizeStar) :
    ∃ cStepLower cStepUpper T0 cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
      0 < cStepLower ∧ 0 < cStepUpper ∧ 0 < T0 ∧
      0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      (∀ T ≥ T0,
        cStepLower / Real.rpow T (1 / 2 : ℝ) ≤ etaStepStar T ∧
        etaStepStar T ≤ cStepUpper / Real.rpow T (1 / 2 : ℝ)) ∧
      (∀ N ≥ N0,
        cBatchLower * Real.rpow N (1 / 2 : ℝ) ≤ batchSizeStar N ∧
        batchSizeStar N ≤ cBatchUpper * Real.rpow N (1 / 2 : ℝ) ∧
        cEtaLower / Real.rpow N (1 / 4 : ℝ) ≤ etaTokenStar N (batchSizeStar N) ∧
        etaTokenStar N (batchSizeStar N) ≤ cEtaUpper / Real.rpow N (1 / 4 : ℝ)) := by
  rcases S.fWExpectedGapSLTheorem1_1_iterationScaling (batchSize := batchSize) hβ0 hβ1 hGap
      (etaStepStar := etaStepStar) hStepMin with
    ⟨_, ⟨cStepLower, cStepUpper, T0, hcStepLower, hcStepUpper, hT0, hStep⟩⟩
  rcases S.fWExpectedGapSLTheorem1_2_tokenBudgetScaling hβ0 hβ1 hGap hNoise hBatchMin
      (etaTokenStar := etaTokenStar) hTokenMin with
    ⟨_, ⟨cBatchLower, cBatchUpper, cEtaLower, cEtaUpper, N0,
      hcBatchLower, hcBatchUpper, hcEtaLower, hcEtaUpper, hN0, hToken⟩⟩
  exact ⟨cStepLower, cStepUpper, T0, cBatchLower, cBatchUpper, cEtaLower, cEtaUpper, N0,
    hcStepLower, hcStepUpper, hT0, hcBatchLower, hcBatchUpper, hcEtaLower, hcEtaUpper, hN0,
    hStep, hToken⟩

end StochasticFrankWolfeGeometryContext

end

end SteepestDescentOptimizationBounds
