import MlOptBoundsFormalization.Theorem14

namespace MlOptBoundsFormalization

noncomputable section

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
SL1: Fixed-Momentum Large-Horizon Proxy
------------------------------------------------------------------------ -/

/-- The exact Theorem-14 drift coefficient expressed in `β`. -/
def proxyDriftCoeff (S : StochasticSteepestDescentGeometryContext Ω V) (β : ℝ) : ℝ :=
  (4 * S.L / S.lambda) * (1 + β ^ 2 / (1 - β))
    + (2 * β / (1 - β)) * S.initialGradNorm

/-- The exact Theorem-14 minibatch-noise coefficient expressed in `β`. -/
def proxyNoiseCoeff (S : StochasticSteepestDescentGeometryContext Ω V) (β : ℝ) : ℝ :=
  (2 / S.lambda)
    * (β * Real.sqrt ((1 - β) / (1 + β)) + (1 - β))
    * Real.sqrt S.D
    * S.sigma

/-- The fixed-step large-horizon proxy derived from Theorem 14. -/
def proxySL1
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η batchSize T β : ℝ) : ℝ :=
  S.theorem14InitialGap * Real.exp (-(S.lambda * η * T))
    + S.proxyNoiseCoeff β / Real.sqrt batchSize
    + S.proxyDriftCoeff β * η

/-- The token-budget large-horizon proxy derived from Theorem 14. -/
def proxySL1Token
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η batchSize N β : ℝ) : ℝ :=
  S.theorem14InitialGap * Real.exp (-(S.lambda * η * N / batchSize))
    + S.proxyNoiseCoeff β / Real.sqrt batchSize
    + S.proxyDriftCoeff β * η

/-- `η` minimizes the fixed-step SL1 proxy over positive learning rates. -/
def IsFixedStepProxyMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η batchSize T β : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.proxySL1 η batchSize T β ≤ S.proxySL1 η' batchSize T β

/-- `etaStepStar` selects fixed-step SL1 minimizers. -/
def IsFixedStepProxyMinimizerFamily
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (β batchSize : ℝ) (etaStepStar : ℝ → ℝ) : Prop :=
  ∀ {T : ℝ}, 0 < T →
    S.IsFixedStepProxyMinimizer (etaStepStar T) batchSize T β

/-- `η` minimizes the token-budget SL1 proxy over positive learning rates. -/
def IsFixedTokenBudgetProxyMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η batchSize N β : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.proxySL1Token η batchSize N β ≤ S.proxySL1Token η' batchSize N β

/-- `etaTokenStar` selects token-budget SL1 minimizers. -/
def IsFixedTokenBudgetProxyMinimizerFamily
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (β : ℝ) (etaTokenStar : ℝ → ℝ → ℝ) : Prop :=
  ∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
    S.IsFixedTokenBudgetProxyMinimizer (etaTokenStar N batchSize) batchSize N β

/-- The leading fixed-batch drift constant as `β → 1`. -/
def fixedBatchLeadDriftConst
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  4 * S.L / S.lambda + 2 * S.initialGradNorm

/-- The leading fixed-batch noise constant as `β → 1`. -/
def fixedBatchLeadNoiseConst
    (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  (Real.sqrt 2 / S.lambda) * Real.sqrt S.D * S.sigma

/-- The leading fixed-batch large-horizon proxy near `β → 1`. -/
def fixedBatchLeadingProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η N β batchSize : ℝ) : ℝ :=
  S.theorem14InitialGap * Real.exp (-(S.lambda * η * N / batchSize))
    + S.fixedBatchLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
    + (S.fixedBatchLeadDriftConst / (1 - β)) * η

/-- `η` minimizes the leading fixed-batch proxy over positive learning rates. -/
def IsFixedBatchLeadingProxyEtaMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (η N β batchSize : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.fixedBatchLeadingProxy η N β batchSize
      ≤ S.fixedBatchLeadingProxy η' N β batchSize

/-- `etaStar` selects eventual eta minimizers for the leading fixed-batch proxy. -/
def IsFixedBatchLeadingProxyEtaMinimizerFamily
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (batchSize : ℝ) (betaStar etaStar : ℝ → ℝ) : Prop :=
  ∃ N0, 0 < N0 ∧
    ∀ N ≥ N0,
      0 ≤ betaStar N ∧ betaStar N < 1 ∧
      S.IsFixedBatchLeadingProxyEtaMinimizer (etaStar N) N (betaStar N) batchSize

/-- The reduced leading fixed-batch proxy after minimizing out `η` on the interior branch. -/
def fixedBatchReducedLeadingProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (S.fixedBatchLeadDriftConst * batchSize / (S.lambda * N * (1 - β)))
      * (1 + Real.log
          (S.theorem14InitialGap * S.lambda * N * (1 - β)
            / (S.fixedBatchLeadDriftConst * batchSize)))
    + S.fixedBatchLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)

/-- `β` minimizes the leading fixed-batch reduced proxy over the interior branch. -/
def IsFixedBatchReducedLeadingProxyMomentumMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧
    ∀ β' > 0, β' < 1 →
      S.fixedBatchReducedLeadingProxy N β batchSize
        ≤ S.fixedBatchReducedLeadingProxy N β' batchSize

/-- An eventually interior minimizer family on the small fixed-batch branch. -/
def IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchReducedLeadingProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (batchSize : ℝ) (betaStar : ℝ → ℝ) : Prop :=
  ∃ cLogLower cLogUpper N0,
    0 < cLogLower ∧ 0 < cLogUpper ∧ 0 < N0 ∧
    ∀ N ≥ N0,
      S.IsFixedBatchReducedLeadingProxyMomentumMinimizer N (betaStar N) batchSize ∧
      S.fixedBatchLeadDriftConst * batchSize
        < S.theorem14InitialGap * S.lambda * N * (1 - betaStar N) ∧
      cLogLower * Real.log N
        ≤ Real.log
            (S.theorem14InitialGap * S.lambda * N * (1 - betaStar N)
              / (S.fixedBatchLeadDriftConst * batchSize)) ∧
      Real.log
          (S.theorem14InitialGap * S.lambda * N * (1 - betaStar N)
            / (S.fixedBatchLeadDriftConst * batchSize))
        ≤ cLogUpper * Real.log N

private def etaStarFixedStepsClosedForm
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (T β : ℝ) : ℝ :=
  (1 / (S.lambda * T))
    * Real.log (S.theorem14InitialGap * S.lambda * T / S.proxyDriftCoeff β)

/-- Closed-form token-budget optimizer at fixed batch size. -/
private def etaStarFixedMomentumClosedForm
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (batchSize / (S.lambda * N))
    * Real.log
        (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize))

/-- Reduced token-budget proxy after substituting the closed-form interior optimizer. -/
def fixedMomentumReducedProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (S.proxyDriftCoeff β * batchSize / (S.lambda * N))
      * (1 + Real.log
          (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)))
    + S.proxyNoiseCoeff β / Real.sqrt batchSize

/-- `batchSize` minimizes the reduced token-budget SL1 proxy on the interior branch. -/
def IsFixedMomentumReducedProxyBatchMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < batchSize ∧
    1 < S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize) ∧
    ∀ batchSize' > 0,
      1 < S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize') →
      S.fixedMomentumReducedProxy N β batchSize
        ≤ S.fixedMomentumReducedProxy N β batchSize'

/-- An eventually interior minimizer family on the small fixed-momentum token-budget branch. -/
def IsSmallBranchInteriorBatchMinimizerFamilyFixedMomentumReducedProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (β : ℝ) (batchSizeStar : ℝ → ℝ) : Prop :=
  ∃ cLogLower cLogUpper N0,
    0 < cLogLower ∧ 0 < cLogUpper ∧ 0 < N0 ∧
    ∀ N ≥ N0,
      S.IsFixedMomentumReducedProxyBatchMinimizer N β (batchSizeStar N) ∧
      cLogLower * Real.log N
        ≤ Real.log
            (S.theorem14InitialGap * S.lambda * N
              / (S.proxyDriftCoeff β * batchSizeStar N)) ∧
      Real.log
          (S.theorem14InitialGap * S.lambda * N
            / (S.proxyDriftCoeff β * batchSizeStar N))
        ≤ cLogUpper * Real.log N

/-- The exact fixed-momentum critical-batch expression for the SL1 reduced proxy. -/
private def fixedMomentumCriticalExpression
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  batchSize ^ (3 / 2 : ℝ)
      * Real.log
          (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize))
    - (S.proxyNoiseCoeff β * S.lambda / (2 * S.proxyDriftCoeff β)) * N

private def fixedMomentumLogArg
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)

private def IsInteriorCriticalPointFixedMomentumReducedProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < batchSize ∧
    1 < S.fixedMomentumLogArg N β batchSize ∧
    HasDerivAt (fun b => S.fixedMomentumReducedProxy N β b) 0 batchSize

private def iterationScale (N : ℝ) : ℝ :=
  Real.rpow (N / Real.log N) (2 / 3 : ℝ)

private def etaScaleFixedSteps
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (T : ℝ) : ℝ :=
  Real.log T / (S.lambda * T)

private def etaScaleFixedMomentum
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N : ℝ) : ℝ :=
  Real.rpow (Real.log N) (1 / 3 : ℝ) / (S.lambda * Real.rpow N (1 / 3 : ℝ))

private theorem proxyDriftCoeff_pos
    (S : StochasticSteepestDescentGeometryContext Ω V) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 < S.proxyDriftCoeff β := by
  have hOneSub : 0 < 1 - β := sub_pos.mpr hβ1
  have hCoeff : 0 < 4 * S.L / S.lambda := by
    have : 0 < 4 * S.L := by
      exact mul_pos (by norm_num) S.L_pos
    exact div_pos this S.lambda_pos
  have hTerm1 : 0 < (4 * S.L / S.lambda) * (1 + β ^ 2 / (1 - β)) := by
    refine mul_pos hCoeff ?_
    have hFrac : 0 ≤ β ^ 2 / (1 - β) := by
      exact div_nonneg (sq_nonneg β) hOneSub.le
    linarith
  have hTerm2 : 0 ≤ (2 * β / (1 - β)) * S.initialGradNorm := by
    have hFrac : 0 ≤ 2 * β / (1 - β) := by
      exact div_nonneg (by positivity) hOneSub.le
    exact mul_nonneg hFrac (norm_nonneg _)
  exact add_pos_of_pos_of_nonneg hTerm1 hTerm2

private theorem proxyNoiseCoeff_nonneg
    (S : StochasticSteepestDescentGeometryContext Ω V) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ S.proxyNoiseCoeff β := by
  have hOneSub : 0 ≤ 1 - β := sub_nonneg.mpr hβ1.le
  have hOneAdd : 0 < 1 + β := by linarith
  have hMid : 0 ≤ β * Real.sqrt ((1 - β) / (1 + β)) + (1 - β) := by
    have hSqrt : 0 ≤ Real.sqrt ((1 - β) / (1 + β)) := Real.sqrt_nonneg _
    have hFirst : 0 ≤ β * Real.sqrt ((1 - β) / (1 + β)) := by
      exact mul_nonneg hβ0 hSqrt
    linarith
  have hLeft : 0 ≤ 2 / S.lambda := by
    exact div_nonneg (by norm_num) S.lambda_pos.le
  exact mul_nonneg (mul_nonneg (mul_nonneg hLeft hMid) (Real.sqrt_nonneg _)) S.sigma_nonneg

private theorem etaStarFixedMomentumClosedForm_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) :
    S.etaStarFixedMomentumClosedForm N β batchSize
      = (batchSize / (S.lambda * N))
          * Real.log
              (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)) :=
  rfl

private theorem fixedMomentumReducedProxy_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) :
    S.fixedMomentumReducedProxy N β batchSize
      = (S.proxyDriftCoeff β * batchSize / (S.lambda * N))
          * (1 + Real.log
              (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)))
        + S.proxyNoiseCoeff β / Real.sqrt batchSize :=
  rfl

private theorem hasDerivAt_fixedMomentumReducedProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β N batchSize : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize) :
    HasDerivAt (fun b => S.fixedMomentumReducedProxy N β b)
      ((S.proxyDriftCoeff β / (S.lambda * N)) * Real.log (S.fixedMomentumLogArg N β batchSize)
        - S.proxyNoiseCoeff β / (2 * batchSize ^ (3 / 2 : ℝ))) batchSize := by
  let A := S.proxyDriftCoeff β
  let B := S.proxyNoiseCoeff β
  let C := S.theorem14InitialGap * S.lambda * N / A
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) hApos
  have hLogArgDeriv : HasDerivAt (fun b => Real.log (C / b)) (-1 / batchSize) batchSize := by
    have hDiv : HasDerivAt (fun b => C / b) (-C / batchSize ^ 2) batchSize := by
      simpa [div_eq_mul_inv] using
        ((hasDerivAt_const batchSize C).div (hasDerivAt_id batchSize) hBatch.ne')
    have hDivNe : C / batchSize ≠ 0 := by
      exact div_ne_zero hCpos.ne' hBatch.ne'
    have hLog := hDiv.log hDivNe
    convert hLog using 1
    field_simp [hBatch.ne']
  have hMainDeriv :
      HasDerivAt (fun b => (A / (S.lambda * N)) * (b * (1 + Real.log (C / b))))
        ((A / (S.lambda * N)) * Real.log (C / batchSize)) batchSize := by
    have hInner :
        HasDerivAt (fun b => b * (1 + Real.log (C / b))) (Real.log (C / batchSize)) batchSize := by
      have hMul :=
        (hasDerivAt_id batchSize).mul ((hLogArgDeriv.const_add 1))
      convert hMul using 1
      have hDerivEq :
          1 * (1 + Real.log (C / batchSize)) + id batchSize * (-1 / batchSize)
            = Real.log (C / batchSize) := by
        simp [hBatch.ne', div_eq_mul_inv]
      simpa using hDerivEq.symm
    simpa [mul_assoc, mul_left_comm, mul_comm] using hInner.const_mul (A / (S.lambda * N))
  have hInvSqrt :
      HasDerivAt (fun b => 1 / Real.sqrt b)
        (-(1 / (2 * batchSize * Real.sqrt batchSize))) batchSize := by
    have hSqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt batchSize)) batchSize :=
      Real.hasDerivAt_sqrt hBatch.ne'
    have hInv := hSqrt.inv (Real.sqrt_ne_zero'.2 hBatch)
    convert hInv using 1
    · funext b
      simp [one_div]
    · rw [Real.sq_sqrt hBatch.le]
      field_simp [Real.sqrt_ne_zero'.2 hBatch, hBatch.ne']
  have hNoiseDeriv :
      HasDerivAt (fun b => B / Real.sqrt b)
        (-(B / (2 * batchSize ^ (3 / 2 : ℝ)))) batchSize := by
    convert hInvSqrt.const_mul B using 1
    · simp [div_eq_mul_inv, mul_comm]
    · have hPow :
          batchSize ^ (3 / 2 : ℝ) = batchSize * Real.sqrt batchSize := by
            calc
              batchSize ^ (3 / 2 : ℝ)
                  = batchSize ^ (1 : ℝ) * batchSize ^ (1 / 2 : ℝ) := by
                      rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
                      rw [Real.rpow_add' hBatch.le]
                      norm_num
              _ = batchSize * Real.sqrt batchSize := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      rw [hPow]
      field_simp [Real.sqrt_ne_zero'.2 hBatch, hBatch.ne']
  have hArgEq : C / batchSize = S.fixedMomentumLogArg N β batchSize := by
    unfold C fixedMomentumLogArg
    dsimp [A]
    field_simp [hApos.ne', hBatch.ne']
  have hLogEq : Real.log (C / batchSize) = Real.log (S.fixedMomentumLogArg N β batchSize) := by
    rw [hArgEq]
  convert hMainDeriv.add hNoiseDeriv using 1
  · funext b
    unfold fixedMomentumReducedProxy C A B
    dsimp
    field_simp [hApos.ne']
  · rw [hLogEq]
    simp [A, B, sub_eq_add_neg]

private theorem isInteriorCriticalPointFixedMomentumReducedProxy_of_isBatchMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β N batchSize : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N)
    (hMin : S.IsFixedMomentumReducedProxyBatchMinimizer N β batchSize) :
    S.IsInteriorCriticalPointFixedMomentumReducedProxy N β batchSize := by
  rcases hMin with ⟨hBatch, hInterior, hMinOn⟩
  let A := S.proxyDriftCoeff β
  let C : ℝ := S.theorem14InitialGap * S.lambda * N / A
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have hInteriorMul : A * batchSize < S.theorem14InitialGap * S.lambda * N := by
    have hDenPos : 0 < A * batchSize := mul_pos hApos hBatch
    exact (one_lt_div hDenPos).1 (by
      simpa [fixedMomentumLogArg, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInterior)
  have hBatchLtC : batchSize < C := by
    dsimp [C, A]
    exact (lt_div_iff₀ hApos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hInteriorMul)
  have hIsMinOn :
      IsMinOn (fun b => S.fixedMomentumReducedProxy N β b) (Set.Ioo 0 C) batchSize := by
    intro b hb
    have hbInterior : 1 < S.theorem14InitialGap * S.lambda * N / (A * b) := by
      have hMul : A * b < S.theorem14InitialGap * S.lambda * N := by
        calc
          A * b < A * C := mul_lt_mul_of_pos_left hb.2 hApos
          _ = S.theorem14InitialGap * S.lambda * N := by
                dsimp [C]
                field_simp [hApos.ne']
      exact (one_lt_div (mul_pos hApos hb.1)).2 hMul
    exact hMinOn b hb.1 (by
      simpa [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbInterior)
  have hLocalMin :
      IsLocalMin (fun b => S.fixedMomentumReducedProxy N β b) batchSize := by
    exact hIsMinOn.localize.isLocalMin (Ioo_mem_nhds hBatch hBatchLtC)
  have hDeriv :=
    S.hasDerivAt_fixedMomentumReducedProxy hβ0 hβ1 hGap hN hBatch
  have hDerivZero :
      ((S.proxyDriftCoeff β / (S.lambda * N)) * Real.log (S.fixedMomentumLogArg N β batchSize)
        - S.proxyNoiseCoeff β / (2 * batchSize ^ (3 / 2 : ℝ))) = 0 := by
    exact hLocalMin.hasDerivAt_eq_zero hDeriv
  exact ⟨hBatch, by simpa [fixedMomentumLogArg, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInterior,
    by simpa [hDerivZero] using hDeriv⟩

private theorem fixedMomentumCriticalExpression_eq_zero_of_isInteriorCriticalPoint
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β N batchSize : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N)
    (hCrit : S.IsInteriorCriticalPointFixedMomentumReducedProxy N β batchSize) :
    S.fixedMomentumCriticalExpression N β batchSize = 0 := by
  rcases hCrit with ⟨hBatch, hInterior, hDerivZero⟩
  have hDerivFormula := S.hasDerivAt_fixedMomentumReducedProxy hβ0 hβ1 hGap hN hBatch
  have hEqDeriv :
      ((S.proxyDriftCoeff β / (S.lambda * N)) * Real.log (S.fixedMomentumLogArg N β batchSize)
        - S.proxyNoiseCoeff β / (2 * batchSize ^ (3 / 2 : ℝ))) = 0 := by
    exact hDerivFormula.unique hDerivZero
  have hApos : 0 < S.proxyDriftCoeff β := S.proxyDriftCoeff_pos hβ0 hβ1
  have hMul :
      batchSize ^ (3 / 2 : ℝ)
        * ((S.proxyDriftCoeff β / (S.lambda * N)) * Real.log (S.fixedMomentumLogArg N β batchSize)
            - S.proxyNoiseCoeff β / (2 * batchSize ^ (3 / 2 : ℝ))) = 0 := by
    rw [hEqDeriv, mul_zero]
  have hBatchPowPos : 0 < batchSize ^ (3 / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos hBatch (3 / 2 : ℝ)
  have hBatchPowNe : batchSize ^ (3 / 2 : ℝ) ≠ 0 := hBatchPowPos.ne'
  have hExpanded :
      S.fixedMomentumCriticalExpression N β batchSize
        = (S.lambda * N / S.proxyDriftCoeff β)
            * (batchSize ^ (3 / 2 : ℝ)
                * ((S.proxyDriftCoeff β / (S.lambda * N))
                    * Real.log (S.fixedMomentumLogArg N β batchSize)
                  - S.proxyNoiseCoeff β / (2 * batchSize ^ (3 / 2 : ℝ)))) := by
    unfold fixedMomentumCriticalExpression fixedMomentumLogArg
    field_simp [S.lambda_pos.ne', hN.ne', hApos.ne', hBatchPowNe]
  rw [hExpanded, hMul, mul_zero]

private theorem etaStarFixedMomentumClosedForm_eq_ratio
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ} (hN : N ≠ 0) :
    S.etaStarFixedMomentumClosedForm N β batchSize
      = (1 / S.lambda)
          * (batchSize * Real.log (S.fixedMomentumLogArg N β batchSize) / N) := by
  unfold etaStarFixedMomentumClosedForm fixedMomentumLogArg
  field_simp [S.lambda_pos.ne', hN]

private theorem eventually_large_log_pos {x x0 : ℝ}
    (hx0 : Real.exp 1 ≤ x0) (hx : x0 ≤ x) : 0 < Real.log x := by
  have hOneLtExp : 1 < Real.exp 1 := by simp
  have hOneLtX : 1 < x := lt_of_lt_of_le hOneLtExp (le_trans hx0 hx)
  exact Real.log_pos hOneLtX

private theorem iterationScale_pos {N : ℝ} (hN : 0 < N) (hlog : 0 < Real.log N) :
    0 < iterationScale N := by
  unfold iterationScale
  have hBase : 0 < N / Real.log N := div_pos hN hlog
  exact Real.rpow_pos_of_pos hBase _

private theorem etaScaleFixedMomentum_eq
    (S : StochasticSteepestDescentGeometryContext Ω V) {N : ℝ}
    (hN : 0 < N) (hlog : 0 < Real.log N) :
    etaScaleFixedMomentum S N
      = (1 / S.lambda) * Real.rpow (Real.log N / N) (1 / 3 : ℝ) := by
  unfold etaScaleFixedMomentum
  calc
    Real.rpow (Real.log N) (1 / 3 : ℝ) / (S.lambda * Real.rpow N (1 / 3 : ℝ))
      = (Real.rpow (Real.log N) (1 / 3 : ℝ) / Real.rpow N (1 / 3 : ℝ)) / S.lambda := by
          field_simp [S.lambda_pos.ne']
    _ = Real.rpow (Real.log N / N) (1 / 3 : ℝ) / S.lambda := by
          congr 1
          simpa [div_eq_mul_inv] using (Real.div_rpow hlog.le hN.le (1 / 3 : ℝ)).symm
    _ = (1 / S.lambda) * Real.rpow (Real.log N / N) (1 / 3 : ℝ) := by ring

private theorem iterationScale_mul_log_div_eq_tokenScale
    {N : ℝ} (hN : 0 < N) (hlog : 0 < Real.log N) :
    iterationScale N * Real.log N / N = Real.rpow (Real.log N / N) (1 / 3 : ℝ) := by
  unfold iterationScale
  have hBase : 0 ≤ Real.log N / N := by positivity
  have hMulBase : 0 ≤ N / Real.log N := by positivity
  calc
    (N / Real.log N) ^ (2 / 3 : ℝ) * Real.log N / N
      = (N / Real.log N) ^ (2 / 3 : ℝ) * (Real.log N / N) := by ring
    _ = (N / Real.log N) ^ (2 / 3 : ℝ)
          * ((Real.log N / N) ^ (2 / 3 : ℝ) * (Real.log N / N) ^ (1 / 3 : ℝ)) := by
            rw [← Real.rpow_add' hBase]
            · norm_num
            · norm_num
    _ = ((N / Real.log N) ^ (2 / 3 : ℝ) * (Real.log N / N) ^ (2 / 3 : ℝ))
          * (Real.log N / N) ^ (1 / 3 : ℝ) := by ring
    _ = ((N / Real.log N) * (Real.log N / N)) ^ (2 / 3 : ℝ)
          * (Real.log N / N) ^ (1 / 3 : ℝ) := by
            rw [← Real.mul_rpow hMulBase hBase]
    _ = (1 : ℝ) ^ (2 / 3 : ℝ) * (Real.log N / N) ^ (1 / 3 : ℝ) := by
          congr 2
          field_simp [hN.ne', hlog.ne']
    _ = (Real.log N / N) ^ (1 / 3 : ℝ) := by simp

private theorem one_div_sqrt_iterationScale_eq_tokenScale
    {N : ℝ} (hN : 0 < N) (hlog : 0 < Real.log N) :
    1 / Real.sqrt (iterationScale N) = Real.rpow (Real.log N / N) (1 / 3 : ℝ) := by
  unfold iterationScale
  have hBase : 0 ≤ N / Real.log N := by positivity
  calc
    1 / Real.sqrt ((N / Real.log N) ^ (2 / 3 : ℝ))
      = 1 / ((N / Real.log N) ^ (1 / 3 : ℝ)) := by
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul hBase]
          norm_num
    _ = (1 / (N / Real.log N)) ^ (1 / 3 : ℝ) := by
          rw [Real.div_rpow (show 0 ≤ (1 : ℝ) by norm_num) hBase]
          simp
    _ = (Real.log N / N) ^ (1 / 3 : ℝ) := by
          congr 1
          field_simp [hN.ne', hlog.ne']

private theorem pow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  calc
    x ^ (3 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
      rw [Real.rpow_add' hx]
      norm_num
    _ = x * Real.sqrt x := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

private theorem mul_sqrt_eq_pow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [pow_three_halves_eq_mul_sqrt hx]

private theorem rpow_two_thirds_pow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_mul hx (3 / 2 : ℝ) (2 / 3 : ℝ)]
  norm_num

private theorem le_rpow_two_thirds_of_mul_sqrt_le
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x * Real.sqrt x ≤ y) :
    x ≤ y ^ (2 / 3 : ℝ) := by
  have hpow : x ^ (3 / 2 : ℝ) ≤ y := by
    simpa [mul_sqrt_eq_pow_three_halves hx] using hxy
  have h' :=
    Real.rpow_le_rpow (show 0 ≤ x ^ (3 / 2 : ℝ) by positivity) hpow
      (by positivity : 0 ≤ (2 / 3 : ℝ))
  simpa [rpow_two_thirds_pow_three_halves hx] using h'

private theorem rpow_two_thirds_le_of_le_mul_sqrt
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≤ x * Real.sqrt x) :
    y ^ (2 / 3 : ℝ) ≤ x := by
  have hpow : y ≤ x ^ (3 / 2 : ℝ) := by
    simpa [mul_sqrt_eq_pow_three_halves hx] using hxy
  have h' := Real.rpow_le_rpow hy hpow (by positivity : 0 ≤ (2 / 3 : ℝ))
  simpa [rpow_two_thirds_pow_three_halves hx] using h'

private theorem scale_bounds_of_nonneg
    {c xLower x xUpper : ℝ}
    (hc : 0 ≤ c) (hLower : xLower ≤ x) (hUpper : x ≤ xUpper) :
    c * xLower ≤ c * x ∧ c * x ≤ c * xUpper := by
  constructor
  · exact mul_le_mul_of_nonneg_left hLower hc
  · exact mul_le_mul_of_nonneg_left hUpper hc

private theorem mul_bounds_of_nonneg
    {aLower a aUpper bLower b bUpper : ℝ}
    (haLowerNonneg : 0 ≤ aLower) (hbLowerNonneg : 0 ≤ bLower)
    (haLower : aLower ≤ a) (haUpper : a ≤ aUpper)
    (hbLower : bLower ≤ b) (hbUpper : b ≤ bUpper) :
    aLower * bLower ≤ a * b ∧ a * b ≤ aUpper * bUpper := by
  constructor <;>
    nlinarith [haLowerNonneg, hbLowerNonneg, haLower, haUpper, hbLower, hbUpper]

private theorem hasDerivAt_proxySL1
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {η batchSize T β : ℝ} :
    HasDerivAt (fun η' => S.proxySL1 η' batchSize T β)
      (-(S.theorem14InitialGap * (S.lambda * T) * Real.exp (-(S.lambda * η * T)))
        + S.proxyDriftCoeff β) η := by
  have hInner :
      HasDerivAt (fun η' : ℝ => -(S.lambda * η' * T)) (-(S.lambda * T)) η := by
    have h :=
      ((hasDerivAt_id η).const_mul (S.lambda * T)).neg
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hExp := (Real.hasDerivAt_exp (-(S.lambda * η * T))).comp η hInner
  have hMain :
      HasDerivAt
        (fun η' : ℝ => S.theorem14InitialGap * Real.exp (-(S.lambda * η' * T)))
        (-(S.theorem14InitialGap * (S.lambda * T) * Real.exp (-(S.lambda * η * T)))) η := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hExp.const_mul S.theorem14InitialGap
  have hDrift :
      HasDerivAt (fun η' : ℝ => S.proxyDriftCoeff β * η') (S.proxyDriftCoeff β) η := by
    simpa [mul_comm] using (hasDerivAt_id η).const_mul (S.proxyDriftCoeff β)
  convert hMain.add (hDrift.add_const (S.proxyNoiseCoeff β / Real.sqrt batchSize)) using 1 <;>
    funext η' <;> simp [proxySL1, add_assoc, add_comm]

private theorem hasDerivAt_proxySL1Token
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {η batchSize N β : ℝ} :
    HasDerivAt (fun η' => S.proxySL1Token η' batchSize N β)
      (-(S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * η * N / batchSize)))
        + S.proxyDriftCoeff β) η := by
  have hInner :
      HasDerivAt (fun η' : ℝ => -(S.lambda * η' * N / batchSize))
        (-(S.lambda * N / batchSize)) η := by
    have h :=
      (((hasDerivAt_id η).const_mul (S.lambda * N)).div_const batchSize).neg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hExp := (Real.hasDerivAt_exp (-(S.lambda * η * N / batchSize))).comp η hInner
  have hMain :
      HasDerivAt
        (fun η' : ℝ => S.theorem14InitialGap * Real.exp (-(S.lambda * η' * N / batchSize)))
        (-(S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * η * N / batchSize)))) η := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hExp.const_mul S.theorem14InitialGap
  have hDrift :
      HasDerivAt (fun η' : ℝ => S.proxyDriftCoeff β * η') (S.proxyDriftCoeff β) η := by
    simpa [mul_comm] using (hasDerivAt_id η).const_mul (S.proxyDriftCoeff β)
  convert hMain.add (hDrift.add_const (S.proxyNoiseCoeff β / Real.sqrt batchSize)) using 1 <;>
    funext η' <;> simp [proxySL1Token, add_assoc, add_comm]

private theorem hasDerivAt_fixedBatchLeadingProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {η N β batchSize : ℝ} :
    HasDerivAt (fun η' => S.fixedBatchLeadingProxy η' N β batchSize)
      (-(S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * η * N / batchSize)))
        + S.fixedBatchLeadDriftConst / (1 - β)) η := by
  have hInner :
      HasDerivAt (fun η' : ℝ => -(S.lambda * η' * N / batchSize))
        (-(S.lambda * N / batchSize)) η := by
    have h :=
      (((hasDerivAt_id η).const_mul (S.lambda * N)).div_const batchSize).neg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hExp := (Real.hasDerivAt_exp (-(S.lambda * η * N / batchSize))).comp η hInner
  have hMain :
      HasDerivAt
        (fun η' : ℝ => S.theorem14InitialGap * Real.exp (-(S.lambda * η' * N / batchSize)))
        (-(S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * η * N / batchSize)))) η := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hExp.const_mul S.theorem14InitialGap
  have hDrift :
      HasDerivAt (fun η' : ℝ => (S.fixedBatchLeadDriftConst / (1 - β)) * η')
        (S.fixedBatchLeadDriftConst / (1 - β)) η := by
    simpa [mul_comm] using
      (hasDerivAt_id η).const_mul (S.fixedBatchLeadDriftConst / (1 - β))
  convert hMain.add
      (hDrift.add_const (S.fixedBatchLeadNoiseConst * Real.sqrt ((1 - β) / batchSize))) using 1 <;>
    funext η' <;> simp [fixedBatchLeadingProxy, add_assoc, add_comm]

private theorem closedForm_fixedStep_isMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize T : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hT : 0 < T)
    (hInterior : S.proxyDriftCoeff β < S.theorem14InitialGap * S.lambda * T) :
    S.IsFixedStepProxyMinimizer (S.etaStarFixedStepsClosedForm T β) batchSize T β := by
  let A := S.proxyDriftCoeff β
  let a : ℝ := S.lambda * T
  let ηStar := S.etaStarFixedStepsClosedForm T β
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact mul_pos S.lambda_pos hT
  have hArgPos :
      0 < S.theorem14InitialGap * S.lambda * T / A := by
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hT) hApos
  have hArgGtOne : 1 < S.theorem14InitialGap * S.lambda * T / A := by
    have hDiv := (one_lt_div hApos).2 hInterior
    simpa [one_mul] using hDiv
  have hEtaPos : 0 < ηStar := by
    dsimp [ηStar, etaStarFixedStepsClosedForm]
    refine mul_pos ?_ (Real.log_pos hArgGtOne)
    exact one_div_pos.mpr (mul_pos S.lambda_pos hT)
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.theorem14InitialGap * S.lambda * T / A) := by
      dsimp [a, ηStar, etaStarFixedStepsClosedForm]
      field_simp [S.lambda_pos.ne', hT.ne']
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap
              * Real.exp (-Real.log (S.theorem14InitialGap * S.lambda * T / A)) := by
                rw [hMul]
      _ = S.theorem14InitialGap / (S.theorem14InitialGap * S.lambda * T / A) := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [a]
            field_simp [hApos.ne', S.lambda_pos.ne', hT.ne', hGap.ne']
  refine ⟨hEtaPos, ?_⟩
  intro η hη
  let u : ℝ := a * (η - ηStar)
  have hOneLe : 1 ≤ Real.exp (-u) + u := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hCoeffNonneg : 0 ≤ A / a := by
    exact div_nonneg hApos.le haPos.le
  have hCore : A / a ≤ (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_le_mul_of_nonneg_left hOneLe hCoeffNonneg
    have hU :
        (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hT.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ ≤ (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.proxySL1 ηStar batchSize T β
      = S.proxyNoiseCoeff β / Real.sqrt batchSize + A / a + A * ηStar := by
          unfold proxySL1
          have hExpArg : -(S.lambda * ηStar * T) = -(a * ηStar) := by
            dsimp [a]
            ring
          rw [hExpArg]
          rw [hExpStar]
          ring
    _ ≤ S.proxyNoiseCoeff β / Real.sqrt batchSize + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = S.proxyNoiseCoeff β / Real.sqrt batchSize + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.proxySL1 η batchSize T β := by
          unfold proxySL1
          have hExpArg : -(S.lambda * η * T) = -(a * η) := by
            dsimp [a]
            ring
          rw [hExpArg]
          rw [hExpEta]
          ring

private theorem fixedToken_interior_of_isMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize N ηStar : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hMin : S.IsFixedTokenBudgetProxyMinimizer ηStar batchSize N β) :
    S.proxyDriftCoeff β * batchSize < S.theorem14InitialGap * S.lambda * N := by
  have hIsMinOn : IsMinOn (fun η => S.proxySL1Token η batchSize N β) (Set.Ioi 0) ηStar := by
    intro η hη
    exact hMin.2 η hη
  have hLocalMin : IsLocalMin (fun η => S.proxySL1Token η batchSize N β) ηStar := by
    exact hIsMinOn.localize.isLocalMin (Ioi_mem_nhds hMin.1)
  have hDerivZero :
      -(S.theorem14InitialGap * (S.lambda * N / batchSize)
          * Real.exp (-(S.lambda * ηStar * N / batchSize)))
        + S.proxyDriftCoeff β = 0 := by
    exact hLocalMin.hasDerivAt_eq_zero (S.hasDerivAt_proxySL1Token (η := ηStar))
  have hExpLtOne : Real.exp (-(S.lambda * ηStar * N / batchSize)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hArgPos : 0 < S.lambda * ηStar * N / batchSize := by
      exact div_pos (mul_pos (mul_pos S.lambda_pos hMin.1) hN) hBatch
    linarith
  have hScalePos : 0 < S.theorem14InitialGap * (S.lambda * N / batchSize) := by
    exact mul_pos hGap (div_pos (mul_pos S.lambda_pos hN) hBatch)
  have hLt :
      S.proxyDriftCoeff β
        < S.theorem14InitialGap * (S.lambda * N / batchSize) := by
    calc
      S.proxyDriftCoeff β
        = S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * ηStar * N / batchSize)) := by
            linarith
      _ < (S.theorem14InitialGap * (S.lambda * N / batchSize)) * 1 := by
            exact mul_lt_mul_of_pos_left hExpLtOne hScalePos
      _ = S.theorem14InitialGap * (S.lambda * N / batchSize) := by ring
  have hMul :
      S.proxyDriftCoeff β * batchSize
        < (S.theorem14InitialGap * (S.lambda * N / batchSize)) * batchSize := by
    exact mul_lt_mul_of_pos_right hLt hBatch
  calc
    S.proxyDriftCoeff β * batchSize
      < (S.theorem14InitialGap * (S.lambda * N / batchSize)) * batchSize := hMul
    _ = S.theorem14InitialGap * S.lambda * N := by
          field_simp [hBatch.ne']

private theorem closedForm_fixedStep_lt_of_ne
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize T η : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hT : 0 < T)
    (hNe : η ≠ S.etaStarFixedStepsClosedForm T β) :
    S.proxySL1 (S.etaStarFixedStepsClosedForm T β) batchSize T β
      < S.proxySL1 η batchSize T β := by
  let A := S.proxyDriftCoeff β
  let a : ℝ := S.lambda * T
  let ηStar := S.etaStarFixedStepsClosedForm T β
  let u : ℝ := a * (η - ηStar)
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact mul_pos S.lambda_pos hT
  have huNe : u ≠ 0 := by
    dsimp [u, a, ηStar]
    refine mul_ne_zero ?_ ?_
    · exact (ne_of_gt (mul_pos S.lambda_pos hT))
    · exact sub_ne_zero.mpr hNe
  have hArgPos :
      0 < S.theorem14InitialGap * S.lambda * T / A := by
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hT) hApos
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.theorem14InitialGap * S.lambda * T / A) := by
      dsimp [a, ηStar, etaStarFixedStepsClosedForm]
      field_simp [S.lambda_pos.ne', hT.ne']
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap
              * Real.exp (-Real.log (S.theorem14InitialGap * S.lambda * T / A)) := by
                rw [hMul]
      _ = S.theorem14InitialGap / (S.theorem14InitialGap * S.lambda * T / A) := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [a]
            field_simp [hApos.ne', S.lambda_pos.ne', hT.ne', hGap.ne']
  have hOneLt : 1 < Real.exp (-u) + u := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr huNe)
    linarith
  have hCoeffPos : 0 < A / a := div_pos hApos haPos
  have hCore : A / a < (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_lt_mul_of_pos_left hOneLt hCoeffPos
    have hU :
        (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hT.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ < (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.proxySL1 ηStar batchSize T β
      = S.proxyNoiseCoeff β / Real.sqrt batchSize + A / a + A * ηStar := by
          unfold proxySL1
          have hExpArg : -(S.lambda * ηStar * T) = -(a * ηStar) := by
            dsimp [a]
            ring
          rw [hExpArg]
          rw [hExpStar]
          ring
    _ < S.proxyNoiseCoeff β / Real.sqrt batchSize + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = S.proxyNoiseCoeff β / Real.sqrt batchSize + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.proxySL1 η batchSize T β := by
          unfold proxySL1
          have hExpArg : -(S.lambda * η * T) = -(a * η) := by
            dsimp [a]
            ring
          rw [hExpArg]
          rw [hExpEta]
          ring

private theorem closedForm_fixedToken_isMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize N : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hInterior : S.proxyDriftCoeff β * batchSize < S.theorem14InitialGap * S.lambda * N) :
    S.IsFixedTokenBudgetProxyMinimizer (S.etaStarFixedMomentumClosedForm N β batchSize)
      batchSize N β := by
  let A := S.proxyDriftCoeff β
  let a : ℝ := S.lambda * N / batchSize
  let ηStar := S.etaStarFixedMomentumClosedForm N β batchSize
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos S.lambda_pos hN) hBatch
  have hArgPos :
      0 < S.theorem14InitialGap * S.lambda * N / (A * batchSize) := by
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) (mul_pos hApos hBatch)
  have hArgGtOne : 1 < S.theorem14InitialGap * S.lambda * N / (A * batchSize) := by
    have hDenPos : 0 < A * batchSize := mul_pos hApos hBatch
    have hDiv := (one_lt_div hDenPos).2 hInterior
    simpa [one_mul] using hDiv
  have hEtaPos : 0 < ηStar := by
    dsimp [ηStar, etaStarFixedMomentumClosedForm]
    refine mul_pos ?_ (Real.log_pos hArgGtOne)
    exact div_pos hBatch (mul_pos S.lambda_pos hN)
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.theorem14InitialGap * S.lambda * N / (A * batchSize)) := by
      dsimp [a, ηStar, etaStarFixedMomentumClosedForm]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap
              * Real.exp (-Real.log (S.theorem14InitialGap * S.lambda * N / (A * batchSize))) := by
                rw [hMul]
      _ = S.theorem14InitialGap / (S.theorem14InitialGap * S.lambda * N / (A * batchSize)) := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [a]
            field_simp [hApos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne', hGap.ne']
  refine ⟨hEtaPos, ?_⟩
  intro η hη
  let u : ℝ := a * (η - ηStar)
  have hOneLe : 1 ≤ Real.exp (-u) + u := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hCoeffNonneg : 0 ≤ A / a := by
    exact div_nonneg hApos.le haPos.le
  have hCore : A / a ≤ (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_le_mul_of_nonneg_left hOneLe hCoeffNonneg
    have hU :
        (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ ≤ (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.proxySL1Token ηStar batchSize N β
      = S.proxyNoiseCoeff β / Real.sqrt batchSize + A / a + A * ηStar := by
          unfold proxySL1Token
          have hExpArg : -(S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg]
          rw [hExpStar]
          ring
    _ ≤ S.proxyNoiseCoeff β / Real.sqrt batchSize + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = S.proxyNoiseCoeff β / Real.sqrt batchSize + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.proxySL1Token η batchSize N β := by
          unfold proxySL1Token
          have hExpArg : -(S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg]
          rw [hExpEta]
          ring

private theorem closedForm_fixedToken_lt_of_ne
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize N η : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hNe : η ≠ S.etaStarFixedMomentumClosedForm N β batchSize) :
    S.proxySL1Token (S.etaStarFixedMomentumClosedForm N β batchSize) batchSize N β
      < S.proxySL1Token η batchSize N β := by
  let A := S.proxyDriftCoeff β
  let a : ℝ := S.lambda * N / batchSize
  let ηStar := S.etaStarFixedMomentumClosedForm N β batchSize
  let u : ℝ := a * (η - ηStar)
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos S.lambda_pos hN) hBatch
  have huNe : u ≠ 0 := by
    dsimp [u, a, ηStar]
    refine mul_ne_zero ?_ ?_
    · exact (ne_of_gt (div_pos (mul_pos S.lambda_pos hN) hBatch))
    · exact sub_ne_zero.mpr hNe
  have hArgPos :
      0 < S.theorem14InitialGap * S.lambda * N / (A * batchSize) := by
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) (mul_pos hApos hBatch)
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.theorem14InitialGap * S.lambda * N / (A * batchSize)) := by
      dsimp [a, ηStar, etaStarFixedMomentumClosedForm]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap
              * Real.exp (-Real.log (S.theorem14InitialGap * S.lambda * N / (A * batchSize))) := by
                rw [hMul]
      _ = S.theorem14InitialGap / (S.theorem14InitialGap * S.lambda * N / (A * batchSize)) := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [a]
            field_simp [hApos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne', hGap.ne']
  have hOneLt : 1 < Real.exp (-u) + u := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr huNe)
    linarith
  have hCoeffPos : 0 < A / a := div_pos hApos haPos
  have hCore : A / a < (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_lt_mul_of_pos_left hOneLt hCoeffPos
    have hU :
        (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ < (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.proxySL1Token ηStar batchSize N β
      = S.proxyNoiseCoeff β / Real.sqrt batchSize + A / a + A * ηStar := by
          unfold proxySL1Token
          have hExpArg : -(S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg]
          rw [hExpStar]
          ring
    _ < S.proxyNoiseCoeff β / Real.sqrt batchSize + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = S.proxyNoiseCoeff β / Real.sqrt batchSize + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.proxySL1Token η batchSize N β := by
          unfold proxySL1Token
          have hExpArg : -(S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg]
          rw [hExpEta]
          ring

private theorem fixedStep_interior_of_isMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize T ηStar : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hT : 0 < T)
    (hMin : S.IsFixedStepProxyMinimizer ηStar batchSize T β) :
    S.proxyDriftCoeff β < S.theorem14InitialGap * S.lambda * T := by
  have hIsMinOn : IsMinOn (fun η => S.proxySL1 η batchSize T β) (Set.Ioi 0) ηStar := by
    intro η hη
    exact hMin.2 η hη
  have hLocalMin : IsLocalMin (fun η => S.proxySL1 η batchSize T β) ηStar := by
    exact hIsMinOn.localize.isLocalMin (Ioi_mem_nhds hMin.1)
  have hDerivZero :
      -(S.theorem14InitialGap * (S.lambda * T) * Real.exp (-(S.lambda * ηStar * T)))
        + S.proxyDriftCoeff β = 0 := by
    exact hLocalMin.hasDerivAt_eq_zero (S.hasDerivAt_proxySL1 (η := ηStar))
  have hExpLtOne : Real.exp (-(S.lambda * ηStar * T)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hArgPos : 0 < S.lambda * ηStar * T := by
      exact mul_pos (mul_pos S.lambda_pos hMin.1) hT
    linarith
  have hScalePos : 0 < S.theorem14InitialGap * (S.lambda * T) := by
    exact mul_pos hGap (mul_pos S.lambda_pos hT)
  calc
    S.proxyDriftCoeff β
      = S.theorem14InitialGap * (S.lambda * T) * Real.exp (-(S.lambda * ηStar * T)) := by
          linarith
    _ < (S.theorem14InitialGap * (S.lambda * T)) * 1 := by
          exact mul_lt_mul_of_pos_left hExpLtOne hScalePos
    _ = S.theorem14InitialGap * (S.lambda * T) := by ring
    _ = S.theorem14InitialGap * S.lambda * T := by ring

/-- Any positive fixed-step SL1 minimizer is equal to the closed-form optimizer. -/
private theorem etaStarFixedSteps_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize T ηStar : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hT : 0 < T)
    (hMin : S.IsFixedStepProxyMinimizer ηStar batchSize T β) :
    ηStar
      = (1 / (S.lambda * T))
          * Real.log (S.theorem14InitialGap * S.lambda * T / S.proxyDriftCoeff β) := by
  have hInterior := S.fixedStep_interior_of_isMinimizer hGap hT hMin
  by_contra hNe
  have hLt := S.closedForm_fixedStep_lt_of_ne (batchSize := batchSize) hβ0 hβ1 hGap hT <| by
    simpa [etaStarFixedStepsClosedForm] using hNe
  have hClosedMin := S.closedForm_fixedStep_isMinimizer (batchSize := batchSize) hβ0 hβ1 hGap hT hInterior
  have hLe := hMin.2 (S.etaStarFixedStepsClosedForm T β) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedStepClosedFormFamily_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    {etaStepStar : ℝ → ℝ}
    (hMin : S.IsFixedStepProxyMinimizerFamily β batchSize etaStepStar) :
    ∀ {T : ℝ}, 0 < T →
      etaStepStar T
        = (1 / (S.lambda * T))
            * Real.log (S.theorem14InitialGap * S.lambda * T / S.proxyDriftCoeff β) := by
  intro T hT
  exact S.etaStarFixedSteps_eq hβ0 hβ1 hGap hT (hMin hT)

private theorem fixedStepIterationScalingBounds
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    {etaStepStar : ℝ → ℝ}
    (hMin : S.IsFixedStepProxyMinimizerFamily β batchSize etaStepStar) :
    ∃ cLower cUpper T0,
      0 < cLower ∧ 0 < cUpper ∧ 0 < T0 ∧
      ∀ T ≥ T0,
        cLower * (Real.log T / (S.lambda * T)) ≤ etaStepStar T ∧
        etaStepStar T ≤ cUpper * (Real.log T / (S.lambda * T)) := by
  let A := S.proxyDriftCoeff β
  let c : ℝ := Real.log (S.theorem14InitialGap * S.lambda / A)
  let T0 : ℝ := max (Real.exp 1) (max (Real.exp (2 * |c|)) (A / (S.theorem14InitialGap * S.lambda) + 1))
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have hCpos : 0 < S.theorem14InitialGap * S.lambda / A := by
    exact div_pos (mul_pos hGap S.lambda_pos) hApos
  have hT0pos : 0 < T0 := by
    unfold T0
    exact lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)
  refine ⟨(1 / 2 : ℝ), (2 : ℝ), T0, by norm_num, by norm_num, hT0pos, ?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le hT0pos hT
  have hEqStar :
      etaStepStar T
        = (1 / (S.lambda * T))
            * Real.log (S.theorem14InitialGap * S.lambda * T / A) := by
    exact S.fixedStepClosedFormFamily_eq hβ0 hβ1 hGap hMin hTpos
  have hLogTpos : 0 < Real.log T := by
    unfold T0 at hT
    exact eventually_large_log_pos (le_max_left _ _) hT
  have hAbsLe : |c| ≤ Real.log T / 2 := by
    have hExpBound : Real.exp (2 * |c|) ≤ T := by
      unfold T0 at hT
      exact le_trans
        (le_trans
          (le_max_left (Real.exp (2 * |c|)) (A / (S.theorem14InitialGap * S.lambda) + 1))
          (le_max_right (Real.exp 1) _))
        hT
    have hLogLe : 2 * |c| ≤ Real.log T := by
      have := Real.log_le_log (Real.exp_pos (2 * |c|)) hExpBound
      simpa using this
    linarith
  have hSplit :
      Real.log (S.theorem14InitialGap * S.lambda * T / A) = Real.log T + c := by
    unfold c
    have hRewrite :
        S.theorem14InitialGap * S.lambda * T / A
          = T * (S.theorem14InitialGap * S.lambda / A) := by
      field_simp [hApos.ne']
    rw [hRewrite, Real.log_mul hTpos.ne' hCpos.ne']
  have hLowerLog : (Real.log T) / 2 ≤ Real.log (S.theorem14InitialGap * S.lambda * T / A) := by
    rw [hSplit]
    have : -|c| ≤ c := by exact neg_abs_le c
    linarith
  have hUpperLog : Real.log (S.theorem14InitialGap * S.lambda * T / A) ≤ 2 * Real.log T := by
    rw [hSplit]
    have : c ≤ |c| := le_abs_self c
    linarith
  rw [hEqStar]
  have hFactor : 0 ≤ 1 / (S.lambda * T) := by
    exact one_div_nonneg.mpr (mul_nonneg S.lambda_pos.le hTpos.le)
  have hScaled := scale_bounds_of_nonneg hFactor hLowerLog hUpperLog
  constructor
  · have hLowerScaled :
        (1 / (S.lambda * T)) * ((Real.log T) / 2)
          ≤ (1 / (S.lambda * T))
              * Real.log (S.theorem14InitialGap * S.lambda * T / A) := hScaled.1
    have hRewrite :
        (1 / 2 : ℝ) * (Real.log T / (S.lambda * T))
          = (1 / (S.lambda * T)) * ((Real.log T) / 2) := by
      field_simp [S.lambda_pos.ne', hTpos.ne']
    rw [hRewrite]
    simpa [A] using hLowerScaled
  · have hUpperScaled :
        (1 / (S.lambda * T))
            * Real.log (S.theorem14InitialGap * S.lambda * T / A)
          ≤ (1 / (S.lambda * T)) * (2 * Real.log T) := hScaled.2
    have hRewrite :
        (1 / (S.lambda * T)) * (2 * Real.log T)
          = (2 : ℝ) * (Real.log T / (S.lambda * T)) := by
      field_simp [S.lambda_pos.ne', hTpos.ne']
    rw [← hRewrite]
    simpa [A] using hUpperScaled

/-! ------------------------------------------------------------------------
SL1: Fixed-Momentum Large-Horizon Proxy Theorems
------------------------------------------------------------------------ -/

/-- Fixed-step optimizer identification and iteration scaling for the SL1 proxy. -/
theorem theoremSL1_1_iterationScaling
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap) :
    ∀ {etaStepStar : ℝ → ℝ},
      S.IsFixedStepProxyMinimizerFamily β batchSize etaStepStar →
      (∀ {T : ℝ}, 0 < T →
        etaStepStar T
          = (1 / (S.lambda * T))
              * Real.log (S.theorem14InitialGap * S.lambda * T / S.proxyDriftCoeff β)) ∧
    ∃ cLower cUpper T0,
      0 < cLower ∧ 0 < cUpper ∧ 0 < T0 ∧
      ∀ T ≥ T0,
        cLower * (Real.log T / (S.lambda * T)) ≤ etaStepStar T ∧
        etaStepStar T ≤ cUpper * (Real.log T / (S.lambda * T)) := by
  intro etaStepStar hMin
  exact ⟨S.fixedStepClosedFormFamily_eq hβ0 hβ1 hGap hMin,
    S.fixedStepIterationScalingBounds hβ0 hβ1 hGap hMin⟩

/-- Any positive token-budget SL1 minimizer is equal to the closed-form optimizer. -/
private theorem etaStarFixedMomentum_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize N ηStar : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hMin : S.IsFixedTokenBudgetProxyMinimizer ηStar batchSize N β) :
    ηStar
      = (batchSize / (S.lambda * N))
          * Real.log
              (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)) := by
  have hInterior := S.fixedToken_interior_of_isMinimizer hGap hN hBatch hMin
  by_contra hNe
  have hLt := S.closedForm_fixedToken_lt_of_ne hβ0 hβ1 hGap hN hBatch <| by
    simpa [etaStarFixedMomentumClosedForm] using hNe
  have hClosedMin := S.closedForm_fixedToken_isMinimizer hβ0 hβ1 hGap hN hBatch hInterior
  have hLe := hMin.2 (S.etaStarFixedMomentumClosedForm N β batchSize) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedTokenClosedFormFamily_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hMin : S.IsFixedTokenBudgetProxyMinimizerFamily β etaTokenStar) :
    ∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
      etaTokenStar N batchSize
        = (batchSize / (S.lambda * N))
            * Real.log
                (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize)) := by
  intro N batchSize hN hBatch
  exact S.etaStarFixedMomentum_eq hβ0 hβ1 hGap hN hBatch
    (hMin hN hBatch)

private theorem fixedMomentumTokenBudgetScalingBounds
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hNoise : 0 < S.proxyNoiseCoeff β)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsSmallBranchInteriorBatchMinimizerFamilyFixedMomentumReducedProxy β batchSizeStar)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hMin : S.IsFixedTokenBudgetProxyMinimizerFamily β etaTokenStar) :
    ∃ cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
      0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBatchLower * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ≤ batchSizeStar N ∧
        batchSizeStar N ≤ cBatchUpper * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ∧
        cEtaLower * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ)))
          ≤ etaTokenStar N (batchSizeStar N) ∧
        etaTokenStar N (batchSizeStar N) ≤
          cEtaUpper * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ))) := by
  rcases hBatchMin with ⟨cLogLower, cLogUpper, N0Crit,
    hcLogLower, hcLogUpper, hN0Crit, hBatchMin⟩
  let A := S.proxyDriftCoeff β
  let B := S.proxyNoiseCoeff β
  let K := B * S.lambda / (2 * A)
  let cBatchLower : ℝ := (K / cLogUpper) ^ (2 / 3 : ℝ)
  let cBatchUpper : ℝ := (K / cLogLower) ^ (2 / 3 : ℝ)
  let cEtaLower : ℝ := cLogLower * cBatchLower
  let cEtaUpper : ℝ := cLogUpper * cBatchUpper
  let N0 : ℝ := max (Real.exp 1) N0Crit
  have hApos : 0 < A := by
    dsimp [A]
    exact S.proxyDriftCoeff_pos hβ0 hβ1
  have hKpos : 0 < K := by
    dsimp [K, B, A]
    have : 0 < B * S.lambda := mul_pos hNoise S.lambda_pos
    exact div_pos this (by positivity)
  have hExp_le : Real.exp 1 ≤ N0 := by
    unfold N0
    exact le_max_left _ _
  have hN0Crit_le : N0Crit ≤ N0 := by
    unfold N0
    exact le_max_right _ _
  refine ⟨cBatchLower, cBatchUpper, cEtaLower, cEtaUpper, N0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [cBatchLower]
    positivity
  · dsimp [cBatchUpper]
    positivity
  · dsimp [cEtaLower]
    exact mul_pos hcLogLower (by positivity)
  · dsimp [cEtaUpper]
    exact mul_pos hcLogUpper (by positivity)
  · exact lt_of_lt_of_le hN0Crit hN0Crit_le
  · intro N hN
    have hNpos : 0 < N := lt_of_lt_of_le hN0Crit (le_trans hN0Crit_le hN)
    have hlogN : 0 < Real.log N := eventually_large_log_pos hExp_le hN
    have hBatchMinN := hBatchMin N (le_trans hN0Crit_le hN)
    have hCriticalN :=
      S.isInteriorCriticalPointFixedMomentumReducedProxy_of_isBatchMinimizer
        hβ0 hβ1 hGap hNpos hBatchMinN.1
    have hbPos : 0 < batchSizeStar N := hBatchMinN.1.1
    have hbNonneg : 0 ≤ batchSizeStar N := hbPos.le
    have hInteriorLog :
        1 < S.fixedMomentumLogArg N β (batchSizeStar N) := by
      simpa [fixedMomentumLogArg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hBatchMinN.1.2.1
    have hLogLo :
        cLogLower * Real.log N ≤ Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) := by
      simpa [fixedMomentumLogArg] using hBatchMinN.2.1
    have hLogHi :
        Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) ≤ cLogUpper * Real.log N := by
      simpa [fixedMomentumLogArg] using hBatchMinN.2.2
    have hCritEq :
        batchSizeStar N * Real.sqrt (batchSizeStar N)
            * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N))
          = K * N := by
      have hEq := S.fixedMomentumCriticalExpression_eq_zero_of_isInteriorCriticalPoint
        hβ0 hβ1 hGap hNpos hCriticalN
      have hEq' :
          batchSizeStar N ^ (3 / 2 : ℝ)
              * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N))
            = K * N := by
        simpa [fixedMomentumCriticalExpression, fixedMomentumLogArg, K, A, B, sub_eq_zero,
          div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hEq
      calc
        batchSizeStar N * Real.sqrt (batchSizeStar N)
            * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N))
          = batchSizeStar N ^ (3 / 2 : ℝ)
              * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) := by
                rw [pow_three_halves_eq_mul_sqrt hbNonneg]
        _ = K * N := hEq'
    have hLowerMul :
        (K / cLogUpper) * (N / Real.log N) ≤ batchSizeStar N * Real.sqrt (batchSizeStar N) := by
      have hTmp :
          K * N ≤ (batchSizeStar N * Real.sqrt (batchSizeStar N)) * (cLogUpper * Real.log N) := by
        calc
          K * N
              = (batchSizeStar N * Real.sqrt (batchSizeStar N))
                  * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) := hCritEq.symm
          _ ≤ (batchSizeStar N * Real.sqrt (batchSizeStar N)) * (cLogUpper * Real.log N) := by
              gcongr
      have hDenPos : 0 < cLogUpper * Real.log N := mul_pos hcLogUpper hlogN
      have hDiv :
          (K * N) / (cLogUpper * Real.log N) ≤ batchSizeStar N * Real.sqrt (batchSizeStar N) := by
        exact (div_le_iff₀ hDenPos).2 hTmp
      have hRewr :
          (K * N) / (cLogUpper * Real.log N) = (K / cLogUpper) * (N / Real.log N) := by
        field_simp [hlogN.ne']
      simpa [hRewr] using hDiv
    have hUpperMul :
        batchSizeStar N * Real.sqrt (batchSizeStar N) ≤ (K / cLogLower) * (N / Real.log N) := by
      have hTmp :
          (batchSizeStar N * Real.sqrt (batchSizeStar N)) * (cLogLower * Real.log N) ≤ K * N := by
        calc
          (batchSizeStar N * Real.sqrt (batchSizeStar N)) * (cLogLower * Real.log N)
              ≤ (batchSizeStar N * Real.sqrt (batchSizeStar N))
                  * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) := by
                gcongr
          _ = K * N := hCritEq
      have hDenPos : 0 < cLogLower * Real.log N := mul_pos hcLogLower hlogN
      have hDiv :
          batchSizeStar N * Real.sqrt (batchSizeStar N)
            ≤ (K * N) / (cLogLower * Real.log N) := by
        exact (le_div_iff₀ hDenPos).2 hTmp
      have hRewr :
          (K * N) / (cLogLower * Real.log N) = (K / cLogLower) * (N / Real.log N) := by
        field_simp [hlogN.ne']
      simpa [hRewr] using hDiv
    have hScaleNonneg : 0 ≤ N / Real.log N := by positivity
    have hBatchLower :
        cBatchLower * iterationScale N ≤ batchSizeStar N := by
      have hBase :=
        rpow_two_thirds_le_of_le_mul_sqrt hbNonneg
          (show 0 ≤ (K / cLogUpper) * (N / Real.log N) by positivity)
          hLowerMul
      have hMul :
          ((K / cLogUpper) * (N / Real.log N)) ^ (2 / 3 : ℝ)
            = (K / cLogUpper) ^ (2 / 3 : ℝ) * iterationScale N := by
        unfold iterationScale
        rw [Real.mul_rpow]
        · rfl
        · positivity
        · exact hScaleNonneg
      simpa [cBatchLower, hMul] using hBase
    have hBatchUpper :
        batchSizeStar N ≤ cBatchUpper * iterationScale N := by
      have hBase :=
        le_rpow_two_thirds_of_mul_sqrt_le hbNonneg
          hUpperMul
      have hMul :
          ((K / cLogLower) * (N / Real.log N)) ^ (2 / 3 : ℝ)
            = (K / cLogLower) ^ (2 / 3 : ℝ) * iterationScale N := by
        unfold iterationScale
        rw [Real.mul_rpow]
        · rfl
        · positivity
        · exact hScaleNonneg
      simpa [cBatchUpper, hMul] using hBase
    have hIterationScaleNonneg : 0 ≤ iterationScale N := (iterationScale_pos hNpos hlogN).le
    have hBatchLowerFactorNonneg : 0 ≤ cBatchLower * iterationScale N := by
      positivity
    have hLogLowerFactorNonneg : 0 ≤ cLogLower * Real.log N := by
      positivity
    have hProdBounds :=
      mul_bounds_of_nonneg
        hBatchLowerFactorNonneg
        hLogLowerFactorNonneg
        hBatchLower hBatchUpper hLogLo hLogHi
    have hDivProdBounds :=
      scale_bounds_of_nonneg (show 0 ≤ 1 / N by positivity)
        hProdBounds.1 hProdBounds.2
    have hEtaEqClosed :
        etaTokenStar N (batchSizeStar N)
          = (batchSizeStar N / (S.lambda * N))
              * Real.log
                  (S.theorem14InitialGap * S.lambda * N
                    / (S.proxyDriftCoeff β * batchSizeStar N)) := by
      exact S.fixedTokenClosedFormFamily_eq hβ0 hβ1 hGap hMin hNpos hbPos
    have hEtaEq :
        etaTokenStar N (batchSizeStar N)
          = (1 / S.lambda)
              * (batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N) := by
      calc
        etaTokenStar N (batchSizeStar N)
            = S.etaStarFixedMomentumClosedForm N β (batchSizeStar N) := by
                trans ((batchSizeStar N / (S.lambda * N))
                    * Real.log
                        (S.theorem14InitialGap * S.lambda * N
                          / (S.proxyDriftCoeff β * batchSizeStar N)))
                · exact hEtaEqClosed
                · symm
                  exact S.etaStarFixedMomentumClosedForm_eq N β (batchSizeStar N)
        _ = (1 / S.lambda)
              * (batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N) := by
              exact S.etaStarFixedMomentumClosedForm_eq_ratio hNpos.ne'
    have hEtaLowerMul :
        (cLogLower * cBatchLower) * (iterationScale N * Real.log N / N)
          ≤ batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N := by
      simpa [cEtaLower, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hDivProdBounds.1
    have hEtaUpperMul :
      batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N
          ≤ (cLogUpper * cBatchUpper) * (iterationScale N * Real.log N / N) := by
      simpa [cEtaUpper, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hDivProdBounds.2
    have hEtaScaleBounds :=
      scale_bounds_of_nonneg
        (show 0 ≤ 1 / S.lambda by exact one_div_nonneg.mpr S.lambda_pos.le)
        hEtaLowerMul hEtaUpperMul
    have hEtaLower' :
        cEtaLower * etaScaleFixedMomentum S N ≤ etaTokenStar N (batchSizeStar N) := by
      calc
        cEtaLower * etaScaleFixedMomentum S N
            = (1 / S.lambda) * (cEtaLower * (iterationScale N * Real.log N / N)) := by
                rw [S.etaScaleFixedMomentum_eq hNpos hlogN,
                  iterationScale_mul_log_div_eq_tokenScale hNpos hlogN]
                ring
        _ ≤ (1 / S.lambda)
              * (batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N) :=
              hEtaScaleBounds.1
        _ = etaTokenStar N (batchSizeStar N) := hEtaEq.symm
    have hEtaUpper' :
        etaTokenStar N (batchSizeStar N) ≤ cEtaUpper * etaScaleFixedMomentum S N := by
      calc
        etaTokenStar N (batchSizeStar N)
            = (1 / S.lambda)
                * (batchSizeStar N * Real.log (S.fixedMomentumLogArg N β (batchSizeStar N)) / N) :=
              hEtaEq
        _ ≤ (1 / S.lambda) * (cEtaUpper * (iterationScale N * Real.log N / N)) :=
              hEtaScaleBounds.2
        _ = cEtaUpper * etaScaleFixedMomentum S N := by
              rw [S.etaScaleFixedMomentum_eq hNpos hlogN,
                iterationScale_mul_log_div_eq_tokenScale hNpos hlogN]
              ring
    have hEtaLower :
        cEtaLower * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ)))
          ≤ etaTokenStar N (batchSizeStar N) := by
      simpa [etaScaleFixedMomentum] using hEtaLower'
    have hEtaUpper :
        etaTokenStar N (batchSizeStar N) ≤
          cEtaUpper * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ))) := by
      simpa [etaScaleFixedMomentum] using hEtaUpper'
    exact ⟨by simpa [iterationScale] using hBatchLower,
      by simpa [iterationScale] using hBatchUpper,
      hEtaLower, hEtaUpper⟩

/- 
Fixed-momentum token-budget scaling on the small interior minimizer branch of
the SL1 reduced proxy.
-/
set_option maxHeartbeats 400000 in
theorem theoremSL1_2_tokenBudgetScaling
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hNoise : 0 < S.proxyNoiseCoeff β)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsSmallBranchInteriorBatchMinimizerFamilyFixedMomentumReducedProxy β batchSizeStar) :
    ∀ {etaTokenStar : ℝ → ℝ → ℝ},
      S.IsFixedTokenBudgetProxyMinimizerFamily β etaTokenStar →
      (∀ {N batchSize : ℝ}, 0 < N → 0 < batchSize →
        etaTokenStar N batchSize
          = (batchSize / (S.lambda * N))
              * Real.log
                  (S.theorem14InitialGap * S.lambda * N / (S.proxyDriftCoeff β * batchSize))) ∧
      ∃ cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
        0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
        ∀ N ≥ N0,
          cBatchLower * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ≤ batchSizeStar N ∧
          batchSizeStar N ≤ cBatchUpper * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ∧
        cEtaLower * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ)))
          ≤ etaTokenStar N (batchSizeStar N) ∧
        etaTokenStar N (batchSizeStar N) ≤
          cEtaUpper * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ))) := by
  intro etaTokenStar hMin
  exact ⟨S.fixedTokenClosedFormFamily_eq hβ0 hβ1 hGap hMin,
    S.fixedMomentumTokenBudgetScalingBounds hβ0 hβ1 hGap hNoise hBatchMin hMin⟩

/- Summary theorem packaging the SL1 fixed-step and token-budget asymptotics. -/
set_option maxHeartbeats 400000 in
theorem theoremSL1_FixedMomentumLargeHorizonProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {β batchSize : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hGap : 0 < S.theorem14InitialGap)
    (hNoise : 0 < S.proxyNoiseCoeff β)
    {etaStepStar : ℝ → ℝ}
    (hStepMin : S.IsFixedStepProxyMinimizerFamily β batchSize etaStepStar)
    {etaTokenStar : ℝ → ℝ → ℝ}
    (hTokenMin : S.IsFixedTokenBudgetProxyMinimizerFamily β etaTokenStar)
    {batchSizeStar : ℝ → ℝ}
    (hBatchMin :
      S.IsSmallBranchInteriorBatchMinimizerFamilyFixedMomentumReducedProxy β batchSizeStar) :
    ∃ cStepLower cStepUpper T0 cBatchLower cBatchUpper cEtaLower cEtaUpper N0,
      0 < cStepLower ∧ 0 < cStepUpper ∧ 0 < T0 ∧
      0 < cBatchLower ∧ 0 < cBatchUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      (∀ T ≥ T0,
        cStepLower * (Real.log T / (S.lambda * T)) ≤ etaStepStar T ∧
        etaStepStar T ≤ cStepUpper * (Real.log T / (S.lambda * T))) ∧
      (∀ N ≥ N0,
        cBatchLower * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ≤ batchSizeStar N ∧
        batchSizeStar N ≤ cBatchUpper * Real.rpow (N / Real.log N) (2 / 3 : ℝ) ∧
        cEtaLower * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ)))
          ≤ etaTokenStar N (batchSizeStar N) ∧
        etaTokenStar N (batchSizeStar N) ≤
          cEtaUpper * (Real.rpow (Real.log N) (1 / 3 : ℝ)
            / (S.lambda * Real.rpow N (1 / 3 : ℝ)))) := by
  rcases S.theoremSL1_1_iterationScaling (batchSize := batchSize) hβ0 hβ1 hGap
      (etaStepStar := etaStepStar) hStepMin with
    ⟨_, ⟨cStepLower, cStepUpper, T0, hcStepLower, hcStepUpper, hT0, hStep⟩⟩
  rcases S.theoremSL1_2_tokenBudgetScaling hβ0 hβ1 hGap hNoise hBatchMin
      (etaTokenStar := etaTokenStar) hTokenMin with
    ⟨_, ⟨cBatchLower, cBatchUpper, cEtaLower, cEtaUpper, N0,
      hcBatchLower, hcBatchUpper, hcEtaLower, hcEtaUpper, hN0, hToken⟩⟩
  refine ⟨cStepLower, cStepUpper, T0, cBatchLower, cBatchUpper, cEtaLower, cEtaUpper, N0,
    hcStepLower, hcStepUpper, hT0, hcBatchLower, hcBatchUpper, hcEtaLower, hcEtaUpper, hN0,
    hStep, hToken⟩

/-! ------------------------------------------------------------------------
SL2: Fixed-Batch Large-Horizon Proxy
------------------------------------------------------------------------ -/

private def fixedBatchLeadingLogArg
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  S.theorem14InitialGap * S.lambda * N * (1 - β)
    / (S.fixedBatchLeadDriftConst * batchSize)

private def etaStarFixedBatchClosedForm
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (batchSize / (S.lambda * N)) * Real.log (S.fixedBatchLeadingLogArg N β batchSize)

private theorem fixedBatchLeadDriftConst_pos
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    0 < S.fixedBatchLeadDriftConst := by
  unfold fixedBatchLeadDriftConst
  have hMain : 0 < 4 * S.L / S.lambda := by
    exact div_pos (mul_pos (by norm_num) S.L_pos) S.lambda_pos
  have hGrad : 0 ≤ S.initialGradNorm := by
    unfold StochasticSteepestDescentGeometryContext.initialGradNorm
    exact norm_nonneg _
  have hRest : 0 ≤ 2 * S.initialGradNorm := by nlinarith
  linarith

private theorem etaStarFixedBatchClosedForm_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (N β batchSize : ℝ) :
    S.etaStarFixedBatchClosedForm N β batchSize
      = (batchSize / (S.lambda * N))
          * Real.log
              (S.theorem14InitialGap * S.lambda * N * (1 - β)
                / (S.fixedBatchLeadDriftConst * batchSize)) :=
  rfl

private theorem etaStarFixedBatchClosedForm_eq_ratio
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ} (hN : N ≠ 0) :
    S.etaStarFixedBatchClosedForm N β batchSize
      = (1 / S.lambda)
          * (batchSize * Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
  unfold etaStarFixedBatchClosedForm fixedBatchLeadingLogArg
  field_simp [S.lambda_pos.ne', hN]

private theorem closedForm_fixedBatchLeading_isMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hInterior :
      S.fixedBatchLeadDriftConst * batchSize
        < S.theorem14InitialGap * S.lambda * N * (1 - β)) :
    S.IsFixedBatchLeadingProxyEtaMinimizer (S.etaStarFixedBatchClosedForm N β batchSize)
      N β batchSize := by
  let A := S.fixedBatchLeadDriftConst / (1 - β)
  let a : ℝ := S.lambda * N / batchSize
  let ηStar := S.etaStarFixedBatchClosedForm N β batchSize
  let noiseTerm : ℝ := S.fixedBatchLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos S.fixedBatchLeadDriftConst_pos hDeltaPos
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos S.lambda_pos hN) hBatch
  have hArgPos : 0 < S.fixedBatchLeadingLogArg N β batchSize := by
    unfold fixedBatchLeadingLogArg
    exact div_pos (mul_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) hDeltaPos)
      (mul_pos S.fixedBatchLeadDriftConst_pos hBatch)
  have hArgGtOne : 1 < S.fixedBatchLeadingLogArg N β batchSize := by
    have hDenPos : 0 < S.fixedBatchLeadDriftConst * batchSize := by
      exact mul_pos S.fixedBatchLeadDriftConst_pos hBatch
    have hDiv := (one_lt_div hDenPos).2 hInterior
    simpa [fixedBatchLeadingLogArg, one_mul] using hDiv
  have hEtaPos : 0 < ηStar := by
    dsimp [ηStar, etaStarFixedBatchClosedForm]
    refine mul_pos ?_ (Real.log_pos hArgGtOne)
    exact div_pos hBatch (mul_pos S.lambda_pos hN)
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
      dsimp [a, ηStar, etaStarFixedBatchClosedForm, fixedBatchLeadingLogArg]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne',
        S.fixedBatchLeadDriftConst_pos.ne']
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap * Real.exp (-Real.log (S.fixedBatchLeadingLogArg N β batchSize)) := by
              rw [hMul]
      _ = S.theorem14InitialGap / S.fixedBatchLeadingLogArg N β batchSize := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [A, a]
            unfold fixedBatchLeadingLogArg
            field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne',
              S.fixedBatchLeadDriftConst_pos.ne', hDeltaPos.ne', hGap.ne']
  refine ⟨hEtaPos, ?_⟩
  intro η hη
  let u : ℝ := a * (η - ηStar)
  have hOneLe : 1 ≤ Real.exp (-u) + u := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hCoeffNonneg : 0 ≤ A / a := by exact div_nonneg hApos.le haPos.le
  have hCore : A / a ≤ (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_le_mul_of_nonneg_left hOneLe hCoeffNonneg
    have hU : (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ ≤ (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.fixedBatchLeadingProxy ηStar N β batchSize
      = noiseTerm + A / a + A * ηStar := by
          unfold fixedBatchLeadingProxy noiseTerm
          have hExpArg : -(S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpStar]
          dsimp [A]
          ring
    _ ≤ noiseTerm + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = noiseTerm + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.fixedBatchLeadingProxy η N β batchSize := by
          unfold fixedBatchLeadingProxy noiseTerm
          have hExpArg : -(S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpEta]
          dsimp [A]
          ring

private theorem closedForm_fixedBatchLeading_lt_of_ne
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize η : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hNe : η ≠ S.etaStarFixedBatchClosedForm N β batchSize) :
    S.fixedBatchLeadingProxy (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize
      < S.fixedBatchLeadingProxy η N β batchSize := by
  let A := S.fixedBatchLeadDriftConst / (1 - β)
  let a : ℝ := S.lambda * N / batchSize
  let ηStar := S.etaStarFixedBatchClosedForm N β batchSize
  let u : ℝ := a * (η - ηStar)
  let noiseTerm : ℝ := S.fixedBatchLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos S.fixedBatchLeadDriftConst_pos hDeltaPos
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos S.lambda_pos hN) hBatch
  have huNe : u ≠ 0 := by
    dsimp [u, a, ηStar]
    refine mul_ne_zero ?_ ?_
    · exact (ne_of_gt (div_pos (mul_pos S.lambda_pos hN) hBatch))
    · exact sub_ne_zero.mpr hNe
  have hArgPos : 0 < S.fixedBatchLeadingLogArg N β batchSize := by
    unfold fixedBatchLeadingLogArg
    exact div_pos (mul_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) hDeltaPos)
      (mul_pos S.fixedBatchLeadDriftConst_pos hBatch)
  have hExpStar :
      S.theorem14InitialGap * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
      dsimp [a, ηStar, etaStarFixedBatchClosedForm, fixedBatchLeadingLogArg]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne',
        S.fixedBatchLeadDriftConst_pos.ne']
    calc
      S.theorem14InitialGap * Real.exp (-(a * ηStar))
          = S.theorem14InitialGap * Real.exp (-Real.log (S.fixedBatchLeadingLogArg N β batchSize)) := by
              rw [hMul]
      _ = S.theorem14InitialGap / S.fixedBatchLeadingLogArg N β batchSize := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [A, a]
            unfold fixedBatchLeadingLogArg
            field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne',
              S.fixedBatchLeadDriftConst_pos.ne', hDeltaPos.ne', hGap.ne']
  have hOneLt : 1 < Real.exp (-u) + u := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr huNe)
    linarith
  have hCoeffPos : 0 < A / a := div_pos hApos haPos
  have hCore : A / a < (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_lt_mul_of_pos_left hOneLt hCoeffPos
    have hU : (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ < (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.theorem14InitialGap * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.theorem14InitialGap * Real.exp (-(a * η))
          = S.theorem14InitialGap * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.theorem14InitialGap * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.fixedBatchLeadingProxy ηStar N β batchSize
      = noiseTerm + A / a + A * ηStar := by
          unfold fixedBatchLeadingProxy noiseTerm
          have hExpArg : -(S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpStar]
          dsimp [A]
          ring
    _ < noiseTerm + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = noiseTerm + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.fixedBatchLeadingProxy η N β batchSize := by
          unfold fixedBatchLeadingProxy noiseTerm
          have hExpArg : -(S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpEta]
          dsimp [A]
          ring

private theorem fixedBatchLeading_interior_of_isEtaMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchLeadingProxyEtaMinimizer ηStar N β batchSize) :
    S.fixedBatchLeadDriftConst * batchSize
      < S.theorem14InitialGap * S.lambda * N * (1 - β) := by
  have hIsMinOn :
      IsMinOn (fun η => S.fixedBatchLeadingProxy η N β batchSize) (Set.Ioi 0) ηStar := by
    intro η hη
    exact hMin.2 η hη
  have hLocalMin : IsLocalMin (fun η => S.fixedBatchLeadingProxy η N β batchSize) ηStar := by
    exact hIsMinOn.localize.isLocalMin (Ioi_mem_nhds hMin.1)
  have hDerivZero :
      -(S.theorem14InitialGap * (S.lambda * N / batchSize)
          * Real.exp (-(S.lambda * ηStar * N / batchSize)))
        + S.fixedBatchLeadDriftConst / (1 - β) = 0 := by
    exact hLocalMin.hasDerivAt_eq_zero
      (S.hasDerivAt_fixedBatchLeadingProxy (η := ηStar))
  have hExpLtOne : Real.exp (-(S.lambda * ηStar * N / batchSize)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hArgPos : 0 < S.lambda * ηStar * N / batchSize := by
      exact div_pos (mul_pos (mul_pos S.lambda_pos hMin.1) hN) hBatch
    linarith
  have hScalePos : 0 < S.theorem14InitialGap * (S.lambda * N / batchSize) := by
    exact mul_pos hGap (div_pos (mul_pos S.lambda_pos hN) hBatch)
  have hLt :
      S.fixedBatchLeadDriftConst / (1 - β)
        < S.theorem14InitialGap * (S.lambda * N / batchSize) := by
    calc
      S.fixedBatchLeadDriftConst / (1 - β)
        = S.theorem14InitialGap * (S.lambda * N / batchSize)
            * Real.exp (-(S.lambda * ηStar * N / batchSize)) := by
            linarith
      _ < (S.theorem14InitialGap * (S.lambda * N / batchSize)) * 1 := by
            exact mul_lt_mul_of_pos_left hExpLtOne hScalePos
      _ = S.theorem14InitialGap * (S.lambda * N / batchSize) := by ring
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hLt' :
      S.fixedBatchLeadDriftConst
        < (S.theorem14InitialGap * (S.lambda * N / batchSize)) * (1 - β) := by
    exact (div_lt_iff₀ hDeltaPos).1 hLt
  have hMul :
      S.fixedBatchLeadDriftConst * batchSize
        < ((S.theorem14InitialGap * (S.lambda * N / batchSize)) * (1 - β)) * batchSize := by
    exact mul_lt_mul_of_pos_right hLt' hBatch
  calc
    S.fixedBatchLeadDriftConst * batchSize
      < ((S.theorem14InitialGap * (S.lambda * N / batchSize)) * (1 - β)) * batchSize := hMul
    _ = S.theorem14InitialGap * S.lambda * N * (1 - β) := by
          field_simp [hBatch.ne']

/-- Fixed-batch leading-proxy eta minimizers are equal to the interior closed form. -/
theorem theoremSL2_1_etaMinimizerEqClosedForm
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar
      = (batchSize / (S.lambda * N))
          * Real.log
              (S.theorem14InitialGap * S.lambda * N * (1 - β)
                / (S.fixedBatchLeadDriftConst * batchSize)) := by
  have hInterior := S.fixedBatchLeading_interior_of_isEtaMinimizer hGap hN hBatch hβ1 hMin
  by_contra hNe
  have hLt := S.closedForm_fixedBatchLeading_lt_of_ne hGap hN hBatch hβ1 <| by
    simpa [etaStarFixedBatchClosedForm] using hNe
  have hClosedMin := S.closedForm_fixedBatchLeading_isMinimizer hGap hN hBatch hβ1 hInterior
  have hLe := hMin.2 (S.etaStarFixedBatchClosedForm N β batchSize) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedBatchLeadingClosedFormFamily_eq
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {batchSize : ℝ} (hGap : 0 < S.theorem14InitialGap) (hBatch : 0 < batchSize)
    {betaStar etaStar : ℝ → ℝ}
    (hMin : S.IsFixedBatchLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ N0, 0 < N0 ∧
      ∀ N ≥ N0,
        etaStar N
          = (batchSize / (S.lambda * N))
              * Real.log
                  (S.theorem14InitialGap * S.lambda * N * (1 - betaStar N)
                    / (S.fixedBatchLeadDriftConst * batchSize)) := by
  rcases hMin with ⟨N0, hN0, hMin⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le hN0 hN
  rcases hMin N hN with ⟨_, hβ1, hEtaMin⟩
  exact S.theoremSL2_1_etaMinimizerEqClosedForm hGap hNpos hBatch hβ1 hEtaMin

private theorem hasDerivAt_fixedBatchReducedLeadingProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize) (hβ1 : β < 1) :
    HasDerivAt (fun β' => S.fixedBatchReducedLeadingProxy N β' batchSize)
      (((S.fixedBatchLeadDriftConst * batchSize) / (S.lambda * N * (1 - β) ^ 2))
          * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
        - S.fixedBatchLeadNoiseConst
            / (2 * Real.sqrt batchSize * Real.sqrt (1 - β))) β := by
  let C := S.fixedBatchLeadDriftConst
  let Z := S.fixedBatchLeadNoiseConst
  let K : ℝ := S.theorem14InitialGap * S.lambda * N / (C * batchSize)
  have hCpos : 0 < C := by dsimp [C]; exact S.fixedBatchLeadDriftConst_pos
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hKpos : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos (mul_pos hGap S.lambda_pos) hN) (mul_pos hCpos hBatch)
  have hDelta :
      HasDerivAt (fun β' : ℝ => 1 - β') (-1) β := by
    simpa using (hasDerivAt_const β (1 : ℝ)).sub (hasDerivAt_id β)
  have hNum :
      HasDerivAt (fun β' : ℝ => 1 + Real.log (K * (1 - β'))) (-1 / (1 - β)) β := by
    have hInner :
        HasDerivAt (fun β' : ℝ => K * (1 - β')) (-K) β := by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hDelta.const_mul K
    have hLog := hInner.log (mul_ne_zero hKpos.ne' hDeltaPos.ne')
    convert hLog.const_add 1 using 1
    field_simp [hKpos.ne', hDeltaPos.ne']
  have hFrac :
      HasDerivAt
        (fun β' : ℝ => (1 + Real.log (K * (1 - β'))) / (1 - β'))
        (Real.log (K * (1 - β)) / (1 - β) ^ 2) β := by
    have h := hNum.div hDelta hDeltaPos.ne'
    convert h using 1
    field_simp [hDeltaPos.ne']
    ring
  have hMain :
      HasDerivAt
        (fun β' : ℝ =>
          (C * batchSize / (S.lambda * N))
            * ((1 + Real.log (K * (1 - β'))) / (1 - β')))
        (((C * batchSize) / (S.lambda * N * (1 - β) ^ 2))
            * Real.log (K * (1 - β))) β := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hFrac.const_mul (C * batchSize / (S.lambda * N))
  have hInnerSqrt :
      HasDerivAt (fun β' : ℝ => (1 - β') / batchSize) (-1 / batchSize) β := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hDelta.div_const batchSize
  have hSqrt :
      HasDerivAt (fun β' : ℝ => Real.sqrt ((1 - β') / batchSize))
        (-(1 / (2 * Real.sqrt batchSize * Real.sqrt (1 - β)))) β := by
    have hInsidePos : 0 < (1 - β) / batchSize := div_pos hDeltaPos hBatch
    have h := (Real.hasDerivAt_sqrt hInsidePos.ne').comp β hInnerSqrt
    convert h using 1
    rw [Real.sqrt_div hDeltaPos.le]
    have hSqrtBatchPos : 0 < Real.sqrt batchSize := Real.sqrt_pos.2 hBatch
    field_simp [Real.sqrt_ne_zero'.2 hDeltaPos, hSqrtBatchPos.ne']
    rw [Real.sq_sqrt hBatch.le]
  have hNoise :
      HasDerivAt
        (fun β' : ℝ => Z * Real.sqrt ((1 - β') / batchSize))
        (-(Z / (2 * Real.sqrt batchSize * Real.sqrt (1 - β)))) β := by
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hSqrt.const_mul Z
  convert hMain.add hNoise using 1
  · funext β'
    unfold fixedBatchReducedLeadingProxy
    dsimp [C, Z, K]
    field_simp [S.fixedBatchLeadDriftConst_pos.ne']
  · rw [show K * (1 - β) = S.fixedBatchLeadingLogArg N β batchSize by
          simp [K, C, fixedBatchLeadingLogArg, div_eq_mul_inv,
            mul_assoc, mul_left_comm, mul_comm]]
    ring

private theorem fixedBatchReducedLeading_deriv_eq_zero_of_isMomentumMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hMin : S.IsFixedBatchReducedLeadingProxyMomentumMinimizer N β batchSize) :
    (((S.fixedBatchLeadDriftConst * batchSize) / (S.lambda * N * (1 - β) ^ 2))
        * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
      - S.fixedBatchLeadNoiseConst
          / (2 * Real.sqrt batchSize * Real.sqrt (1 - β))) = 0 := by
  rcases hMin with ⟨hβ0, hβ1, hMinOn⟩
  have hIsMinOn :
      IsMinOn (fun β' => S.fixedBatchReducedLeadingProxy N β' batchSize) (Set.Ioo 0 1) β := by
    intro β' hβ'
    exact hMinOn β' hβ'.1 hβ'.2
  have hLocalMin : IsLocalMin (fun β' => S.fixedBatchReducedLeadingProxy N β' batchSize) β := by
    exact hIsMinOn.localize.isLocalMin (Ioo_mem_nhds hβ0 hβ1)
  exact hLocalMin.hasDerivAt_eq_zero (S.hasDerivAt_fixedBatchReducedLeadingProxy hGap hN hBatch hβ1)

private theorem fixedBatchGap_mul_sqrt_eq_of_isMomentumMinimizer
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchLeadNoiseConst)
    (hMin : S.IsFixedBatchReducedLeadingProxyMomentumMinimizer N β batchSize) :
    (1 - β) * Real.sqrt (1 - β)
      = (2 * S.fixedBatchLeadDriftConst / (S.fixedBatchLeadNoiseConst * S.lambda))
          * (batchSize * Real.sqrt batchSize)
          * (Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
  have hDerivZero :=
    S.fixedBatchReducedLeading_deriv_eq_zero_of_isMomentumMinimizer hGap hN hBatch hMin
  rcases hMin with ⟨_, hβ1, _⟩
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hEq :
      ((S.fixedBatchLeadDriftConst * batchSize) / (S.lambda * N * (1 - β) ^ 2))
          * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
        = S.fixedBatchLeadNoiseConst
            / (2 * Real.sqrt batchSize * Real.sqrt (1 - β)) := by
    linarith
  have hSqrtBatchPos : 0 < Real.sqrt batchSize := Real.sqrt_pos.2 hBatch
  have hSqrtDeltaPos : 0 < Real.sqrt (1 - β) := Real.sqrt_pos.2 hDeltaPos
  have hCross := hEq
  field_simp [S.lambda_pos.ne', hN.ne', hBatch.ne', hNoise.ne',
    S.fixedBatchLeadDriftConst_pos.ne', hDeltaPos.ne', hSqrtBatchPos.ne', hSqrtDeltaPos.ne'] at hCross
  have hDeltaSq :
      (1 - β) ^ 2 = ((1 - β) * Real.sqrt (1 - β)) * Real.sqrt (1 - β) := by
    calc
      (1 - β) ^ 2 = (1 - β) * (Real.sqrt (1 - β)) ^ 2 := by
        rw [show (Real.sqrt (1 - β)) ^ 2 = 1 - β by
          simpa [pow_two] using (Real.sq_sqrt hDeltaPos.le)]
        ring
      _ = ((1 - β) * Real.sqrt (1 - β)) * Real.sqrt (1 - β) := by ring
  rw [hDeltaSq] at hCross
  have hCancel :
      S.fixedBatchLeadDriftConst * batchSize * Real.log (S.fixedBatchLeadingLogArg N β batchSize) * 2 * Real.sqrt batchSize
        = S.lambda * N * ((1 - β) * Real.sqrt (1 - β)) * S.fixedBatchLeadNoiseConst := by
    exact (mul_right_cancel₀ hSqrtDeltaPos.ne') (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hCross)
  have hCancel' :
      S.lambda * N * S.fixedBatchLeadNoiseConst * ((1 - β) * Real.sqrt (1 - β))
        = 2 * S.fixedBatchLeadDriftConst * batchSize * Real.sqrt batchSize
            * Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hCancel.symm
  calc
    (1 - β) * Real.sqrt (1 - β)
        = (S.lambda * N * S.fixedBatchLeadNoiseConst * ((1 - β) * Real.sqrt (1 - β)))
            / (S.lambda * N * S.fixedBatchLeadNoiseConst) := by
              field_simp [S.lambda_pos.ne', hN.ne', hNoise.ne']
    _ = (2 * S.fixedBatchLeadDriftConst * batchSize * Real.sqrt batchSize
            * Real.log (S.fixedBatchLeadingLogArg N β batchSize))
            / (S.lambda * N * S.fixedBatchLeadNoiseConst) := by
              rw [hCancel']
    _ = (2 * S.fixedBatchLeadDriftConst / (S.fixedBatchLeadNoiseConst * S.lambda))
            * (batchSize * Real.sqrt batchSize)
            * (Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
              field_simp [S.lambda_pos.ne', hN.ne', hNoise.ne']

private theorem fixedBatchLeadingTokenBudgetScalingBounds
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchLeadNoiseConst)
    {betaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchReducedLeadingProxy batchSize betaStar)
    {etaStar : ℝ → ℝ}
    (hEtaMin :
      S.IsFixedBatchLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / (S.lambda * N))
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.lambda * N)) := by
  rcases hMomentum with ⟨cLogLower, cLogUpper, N0Momentum,
    hcLogLower, hcLogUpper, hN0Momentum, hMomentum⟩
  rcases S.fixedBatchLeadingClosedFormFamily_eq hGap hBatch hEtaMin with
    ⟨N0Eta, hN0Eta, hEtaEq⟩
  let K := 2 * S.fixedBatchLeadDriftConst / (S.fixedBatchLeadNoiseConst * S.lambda)
  let cBetaLower : ℝ := (K * cLogLower) ^ (2 / 3 : ℝ)
  let cBetaUpper : ℝ := (K * cLogUpper) ^ (2 / 3 : ℝ)
  let cEtaLower : ℝ := cLogLower
  let cEtaUpper : ℝ := cLogUpper
  let N0 : ℝ := max (Real.exp 1) (max N0Momentum N0Eta)
  have hKpos : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos (by norm_num) S.fixedBatchLeadDriftConst_pos) (mul_pos hNoise S.lambda_pos)
  have hExpLe : Real.exp 1 ≤ N0 := by
    unfold N0
    exact le_max_left _ _
  have hN0MomentumLe : N0Momentum ≤ N0 := by
    unfold N0
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hN0EtaLe : N0Eta ≤ N0 := by
    unfold N0
    exact le_trans (le_max_right N0Momentum N0Eta) (le_max_right _ _)
  refine ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0,
    by positivity, by positivity, hcLogLower, hcLogUpper, ?_, ?_⟩
  · exact lt_of_lt_of_le hN0Momentum hN0MomentumLe
  · intro N hN
    have hNpos : 0 < N := lt_of_lt_of_le (lt_of_lt_of_le hN0Momentum hN0MomentumLe) hN
    have hLogNPos : 0 < Real.log N := eventually_large_log_pos hExpLe hN
    have hMomentumN := hMomentum N (le_trans hN0MomentumLe hN)
    rcases hMomentumN with ⟨hMinBeta, _, hLogLo, hLogHi⟩
    have hBetaLt : betaStar N < 1 := hMinBeta.2.1
    have hGapPos : 0 < 1 - betaStar N := sub_pos.mpr hBetaLt
    have hGapNonneg : 0 ≤ 1 - betaStar N := hGapPos.le
    have hCritical :
        (1 - betaStar N) * Real.sqrt (1 - betaStar N)
          = K * (batchSize * Real.sqrt batchSize)
              * (Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize) / N) := by
      dsimp [K]
      exact S.fixedBatchGap_mul_sqrt_eq_of_isMomentumMinimizer hGap hNpos hBatch hNoise hMinBeta
    have hLogLo' :
        cLogLower * Real.log N
          ≤ Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize) := by
      simpa [fixedBatchLeadingLogArg] using hLogLo
    have hLogHi' :
        Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)
          ≤ cLogUpper * Real.log N := by
      simpa [fixedBatchLeadingLogArg] using hLogHi
    have hLowerMul :
        (K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))
          ≤ (1 - betaStar N) * Real.sqrt (1 - betaStar N) := by
      calc
        (K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))
            = K * (batchSize * Real.sqrt batchSize) * (cLogLower * Real.log N / N) := by ring
        _ ≤ K * (batchSize * Real.sqrt batchSize)
              * (Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize) / N) := by
              gcongr
        _ = (1 - betaStar N) * Real.sqrt (1 - betaStar N) := hCritical.symm
    have hUpperMul :
        (1 - betaStar N) * Real.sqrt (1 - betaStar N)
          ≤ (K * cLogUpper) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N)) := by
      calc
        (1 - betaStar N) * Real.sqrt (1 - betaStar N)
            = K * (batchSize * Real.sqrt batchSize)
                * (Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize) / N) := hCritical
        _ ≤ K * (batchSize * Real.sqrt batchSize) * (cLogUpper * Real.log N / N) := by
              gcongr
        _ = (K * cLogUpper) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N)) := by ring
    have hScaleNonneg : 0 ≤ Real.log N / N := by positivity
    have hGapLowerBase :
        ((K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ)
          ≤ 1 - betaStar N := by
      exact rpow_two_thirds_le_of_le_mul_sqrt hGapNonneg
        (show 0 ≤ (K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N)) by positivity)
        hLowerMul
    have hGapUpperBase :
        1 - betaStar N
          ≤ ((K * cLogUpper) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ) := by
      exact le_rpow_two_thirds_of_mul_sqrt_le hGapNonneg hUpperMul
    have hGapLowerMul :
        ((K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ)
          = cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) := by
      calc
        ((K * cLogLower) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ)
            = ((K * cLogLower) * (batchSize ^ (3 / 2 : ℝ) * (Real.log N / N))) ^ (2 / 3 : ℝ) := by
                congr 1
                rw [pow_three_halves_eq_mul_sqrt hBatch.le]
        _ = (K * cLogLower) ^ (2 / 3 : ℝ)
              * (batchSize ^ (3 / 2 : ℝ) * (Real.log N / N)) ^ (2 / 3 : ℝ) := by
                exact Real.mul_rpow (show 0 ≤ K * cLogLower by positivity)
                  (show 0 ≤ batchSize ^ (3 / 2 : ℝ) * (Real.log N / N) by positivity)
        _ = (K * cLogLower) ^ (2 / 3 : ℝ)
              * ((batchSize ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
                  * (Real.log N / N) ^ (2 / 3 : ℝ)) := by
                congr 1
                exact Real.mul_rpow (show 0 ≤ batchSize ^ (3 / 2 : ℝ) by positivity)
                  hScaleNonneg
        _ = cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) := by
              rw [rpow_two_thirds_pow_three_halves hBatch.le]
              simp [cBetaLower, mul_assoc, mul_comm]
    have hGapUpperMul :
        ((K * cLogUpper) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ)
          = cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) := by
      calc
        ((K * cLogUpper) * ((batchSize * Real.sqrt batchSize) * (Real.log N / N))) ^ (2 / 3 : ℝ)
            = ((K * cLogUpper) * (batchSize ^ (3 / 2 : ℝ) * (Real.log N / N))) ^ (2 / 3 : ℝ) := by
                congr 1
                rw [pow_three_halves_eq_mul_sqrt hBatch.le]
        _ = (K * cLogUpper) ^ (2 / 3 : ℝ)
              * (batchSize ^ (3 / 2 : ℝ) * (Real.log N / N)) ^ (2 / 3 : ℝ) := by
                exact Real.mul_rpow (show 0 ≤ K * cLogUpper by positivity)
                  (show 0 ≤ batchSize ^ (3 / 2 : ℝ) * (Real.log N / N) by positivity)
        _ = (K * cLogUpper) ^ (2 / 3 : ℝ)
              * ((batchSize ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
                  * (Real.log N / N) ^ (2 / 3 : ℝ)) := by
                congr 1
                exact Real.mul_rpow (show 0 ≤ batchSize ^ (3 / 2 : ℝ) by positivity)
                  hScaleNonneg
        _ = cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) := by
              rw [rpow_two_thirds_pow_three_halves hBatch.le]
              simp [cBetaUpper, mul_assoc, mul_comm]
    have hEtaEqClosed :=
      hEtaEq N (le_trans hN0EtaLe hN)
    have hEtaEq :
        etaStar N
          = (1 / S.lambda)
              * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := by
      calc
        etaStar N = S.etaStarFixedBatchClosedForm N (betaStar N) batchSize := by
          trans ((batchSize / (S.lambda * N))
            * Real.log
                (S.theorem14InitialGap * S.lambda * N * (1 - betaStar N)
                  / (S.fixedBatchLeadDriftConst * batchSize)))
          · exact hEtaEqClosed
          · symm
            exact S.etaStarFixedBatchClosedForm_eq N (betaStar N) batchSize
        _ = (1 / S.lambda)
              * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := by
              rw [S.etaStarFixedBatchClosedForm_eq_ratio hNpos.ne']
              field_simp [S.lambda_pos.ne', hNpos.ne']
    have hBatchOverNNonneg : 0 ≤ batchSize / N := div_nonneg hBatch.le hNpos.le
    have hEtaMulBounds :=
      scale_bounds_of_nonneg hBatchOverNNonneg hLogLo' hLogHi'
    have hEtaScaleBounds :=
      scale_bounds_of_nonneg
        (show 0 ≤ 1 / S.lambda by exact one_div_nonneg.mpr S.lambda_pos.le)
        hEtaMulBounds.1 hEtaMulBounds.2
    have hGapLower :
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N := by
      simpa [hGapLowerMul] using hGapLowerBase
    have hGapUpper :
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) := by
      simpa [hGapUpperMul] using hGapUpperBase
    have hEtaLower :
        cEtaLower * (batchSize * Real.log N / (S.lambda * N))
          ≤ etaStar N := by
      calc
        cEtaLower * (batchSize * Real.log N / (S.lambda * N))
            = (1 / S.lambda) * ((batchSize / N) * (cEtaLower * Real.log N)) := by
                field_simp [S.lambda_pos.ne', hNpos.ne']
        _ ≤ (1 / S.lambda)
              * ((batchSize / N)
                  * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := hEtaScaleBounds.1
        _ = etaStar N := by rw [hEtaEq]
    have hEtaUpper :
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.lambda * N)) := by
      calc
        etaStar N
            = (1 / S.lambda)
                * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := hEtaEq
        _ ≤ (1 / S.lambda) * ((batchSize / N) * (cEtaUpper * Real.log N)) := hEtaScaleBounds.2
        _ = cEtaUpper * (batchSize * Real.log N / (S.lambda * N)) := by
              field_simp [S.lambda_pos.ne', hNpos.ne']
    exact ⟨hGapLower, hGapUpper, hEtaLower, hEtaUpper⟩

/-! ------------------------------------------------------------------------
SL2: Fixed-Batch Large-Horizon Proxy Theorems
------------------------------------------------------------------------ -/

theorem theoremSL2_2_tokenBudgetScaling
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchReducedLeadingProxy batchSize betaStar)
    (hEtaMin :
      S.IsFixedBatchLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / (S.lambda * N))
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.lambda * N)) := by
  exact S.fixedBatchLeadingTokenBudgetScalingBounds hGap hBatch hNoise hMomentum hEtaMin

theorem theoremSL2_FixedBatchLargeHorizonProxy
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.theorem14InitialGap) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchReducedLeadingProxy batchSize betaStar)
    (hEtaMin :
      S.IsFixedBatchLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0 T0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧
      0 < N0 ∧ 0 < T0 ∧
      (∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / (S.lambda * N))
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.lambda * N))) ∧
      (∀ T ≥ T0,
        cBetaLower
            * (batchSize * Real.rpow (Real.log (batchSize * T) / (batchSize * T)) (2 / 3 : ℝ))
          ≤ 1 - betaStar (batchSize * T) ∧
        1 - betaStar (batchSize * T)
          ≤ cBetaUpper
              * (batchSize * Real.rpow (Real.log (batchSize * T) / (batchSize * T)) (2 / 3 : ℝ)) ∧
        cEtaLower * (Real.log (batchSize * T) / (S.lambda * T))
          ≤ etaStar (batchSize * T) ∧
        etaStar (batchSize * T)
          ≤ cEtaUpper * (Real.log (batchSize * T) / (S.lambda * T))) := by
  rcases S.theoremSL2_2_tokenBudgetScaling hGap hBatch hNoise hMomentum hEtaMin with
    ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0,
      hcBetaLower, hcBetaUpper, hcEtaLower, hcEtaUpper, hN0, hNBound⟩
  let T0 : ℝ := N0 / batchSize
  refine ⟨cBetaLower, cBetaUpper, cEtaLower, cEtaUpper, N0, T0,
    hcBetaLower, hcBetaUpper, hcEtaLower, hcEtaUpper, hN0, div_pos hN0 hBatch, hNBound, ?_⟩
  intro T hT
  have hN : N0 ≤ batchSize * T := by
    have := (div_le_iff₀ hBatch).mp hT
    simpa [T0, mul_comm, mul_left_comm, mul_assoc] using this
  have hNForm := hNBound (batchSize * T) hN
  refine ⟨hNForm.1, hNForm.2.1, ?_, ?_⟩
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hBatch.ne'] using hNForm.2.2.1
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hBatch.ne'] using hNForm.2.2.2


end StochasticSteepestDescentGeometryContext

end

end MlOptBoundsFormalization
