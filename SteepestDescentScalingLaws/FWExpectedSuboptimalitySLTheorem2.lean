import SteepestDescentScalingLaws.Commons
import SteepestDescentOptimizationBounds.FrankWolfeExpectedSuboptimality

/-!
Frank-Wolfe expected-suboptimality scaling laws, fixed-batch family.

Upstream: `SteepestDescentScalingLaws.Commons` and the FW expected-suboptimality
bounds in `SteepestDescentOptimizationBounds`.
Downstream: the README summaries and the fixed-batch FW expected-suboptimality
section of the blueprint.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

namespace StochasticFrankWolfeKLGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
SL2: Fixed-Batch Large-Horizon Proxy
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- The leading fixed-batch drift constant as `β → 1`. -/
def fixedBatchFWExpectedSuboptimalityLeadDriftConst
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  4 * S.L / (S.muFW * S.lambda) + 2 * S.initialExpectedMomentumError

/-- The leading fixed-batch noise constant as `β → 1`. -/
def fixedBatchFWExpectedSuboptimalityLeadNoiseConst
    (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  ((2 * Real.sqrt 2) / (S.muFW * S.lambda)) * Real.sqrt S.D * S.sigma

/-- The leading fixed-batch large-horizon proxy near `β → 1`. -/
def fixedBatchFWExpectedSuboptimalityLeadingProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (η N β batchSize : ℝ) : ℝ :=
  S.initialExpectedSuboptimality * Real.exp (-(S.muFW * S.lambda * η * N / batchSize))
    + S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
    + (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)) * η

/-- `η` minimizes the leading fixed-batch proxy over positive learning rates. -/
def IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (η N β batchSize : ℝ) : Prop :=
  0 < η ∧
    ∀ η' > 0, S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize
      ≤ S.fixedBatchFWExpectedSuboptimalityLeadingProxy η' N β batchSize

/-- `etaStar` selects eventual eta minimizers for the leading fixed-batch proxy. -/
def IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizerFamily
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (batchSize : ℝ) (betaStar etaStar : ℝ → ℝ) : Prop :=
  ∃ N0, 0 < N0 ∧
    ∀ N ≥ N0,
      0 ≤ betaStar N ∧ betaStar N < 1 ∧
      S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer (etaStar N) N (betaStar N) batchSize

/-- The reduced leading fixed-batch proxy after minimizing out `η` on the interior branch. -/
def fixedBatchFWExpectedSuboptimalityReducedLeadingProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize / (S.muFW * S.lambda * N * (1 - β)))
      * (1 + Real.log
          (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)
            / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)))
    + S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)

/-- `β` minimizes the leading fixed-batch reduced proxy over the interior branch. -/
def IsFixedBatchFWExpectedSuboptimalityReducedLeadingProxyMomentumMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (N β batchSize : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧
    ∀ β' > 0, β' < 1 →
      S.fixedBatchFWExpectedSuboptimalityReducedLeadingProxy N β batchSize
        ≤ S.fixedBatchFWExpectedSuboptimalityReducedLeadingProxy N β' batchSize

/-- An eventually interior minimizer family on the small fixed-batch branch. -/
def IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchFWExpectedSuboptimalityReducedLeadingProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (batchSize : ℝ) (betaStar : ℝ → ℝ) : Prop :=
  ∃ cLogLower cLogUpper N0,
    0 < cLogLower ∧ 0 < cLogUpper ∧ 0 < N0 ∧
    ∀ N ≥ N0,
      S.IsFixedBatchFWExpectedSuboptimalityReducedLeadingProxyMomentumMinimizer N (betaStar N) batchSize ∧
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize
        < S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - betaStar N) ∧
      cLogLower * Real.log N
        ≤ Real.log
            (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - betaStar N)
              / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)) ∧
      Real.log
          (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - betaStar N)
            / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize))
        ≤ cLogUpper * Real.log N

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

private def fixedBatchLeadingLogArg
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)
    / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)

private def etaStarFixedBatchClosedForm
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (N β batchSize : ℝ) : ℝ :=
  (batchSize / (S.muFW * S.lambda * N)) * Real.log (S.fixedBatchLeadingLogArg N β batchSize)

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

private theorem fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos
    (S : StochasticFrankWolfeKLGeometryContext Ω V) :
    0 < S.fixedBatchFWExpectedSuboptimalityLeadDriftConst := by
  unfold fixedBatchFWExpectedSuboptimalityLeadDriftConst
  have hMain : 0 < 4 * S.L / (S.muFW * S.lambda) := by
    exact div_pos (mul_pos (by norm_num) S.L_pos) (mul_pos S.muFW_pos S.lambda_pos)
  have hGrad : 0 ≤ S.initialExpectedMomentumError := S.initialExpectedMomentumError_nonneg
  have hRest : 0 ≤ 2 * S.initialExpectedMomentumError := by nlinarith
  linarith

private theorem etaStarFixedBatchClosedForm_eq
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    (N β batchSize : ℝ) :
    S.etaStarFixedBatchClosedForm N β batchSize
      = (batchSize / (S.muFW * S.lambda * N))
          * Real.log
              (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)
                / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)) :=
  rfl

private theorem etaStarFixedBatchClosedForm_eq_ratio
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize : ℝ} (hN : N ≠ 0) :
    S.etaStarFixedBatchClosedForm N β batchSize
      = (1 / (S.muFW * S.lambda))
          * (batchSize * Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
  unfold etaStarFixedBatchClosedForm fixedBatchLeadingLogArg
  field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN]

private theorem hasDerivAt_fixedBatchFWExpectedSuboptimalityLeadingProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {η N β batchSize : ℝ} :
    HasDerivAt (fun η' => S.fixedBatchFWExpectedSuboptimalityLeadingProxy η' N β batchSize)
      (-(S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)
            * Real.exp (-(S.muFW * S.lambda * η * N / batchSize)))
        + S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)) η := by
  have hInner :
      HasDerivAt (fun η' : ℝ => -(S.muFW * S.lambda * η' * N / batchSize))
        (-(S.muFW * S.lambda * N / batchSize)) η := by
    have h :=
      (((hasDerivAt_id η).const_mul (S.muFW * S.lambda * N)).div_const batchSize).neg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hExp := (Real.hasDerivAt_exp (-(S.muFW * S.lambda * η * N / batchSize))).comp η hInner
  have hMain :
      HasDerivAt
        (fun η' : ℝ => S.initialExpectedSuboptimality * Real.exp (-(S.muFW * S.lambda * η' * N / batchSize)))
        (-(S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)
            * Real.exp (-(S.muFW * S.lambda * η * N / batchSize)))) η := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hExp.const_mul S.initialExpectedSuboptimality
  have hDrift :
      HasDerivAt (fun η' : ℝ => (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)) * η')
        (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)) η := by
    simpa [mul_comm] using
      (hasDerivAt_id η).const_mul (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β))
  (convert hMain.add
      (hDrift.add_const (S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * Real.sqrt ((1 - β) / batchSize))) using 1
    ; funext η'
      ; simp [fixedBatchFWExpectedSuboptimalityLeadingProxy, div_eq_mul_inv,
          add_left_comm, add_comm, mul_assoc, mul_comm])

private theorem closedForm_fixedBatchLeading_isMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hInterior :
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize
        < S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)) :
    S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer (S.etaStarFixedBatchClosedForm N β batchSize)
      N β batchSize := by
  let A := S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)
  let a : ℝ := S.muFW * S.lambda * N / batchSize
  let ηStar := S.etaStarFixedBatchClosedForm N β batchSize
  let noiseTerm : ℝ := S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos hDeltaPos
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hN) hBatch
  have hArgPos : 0 < S.fixedBatchLeadingLogArg N β batchSize := by
    unfold fixedBatchLeadingLogArg
    have hNum :
        0 < ((S.initialExpectedSuboptimality * S.muFW * S.lambda) * N) * (1 - β) := by
      exact mul_pos (mul_pos (mul_pos (mul_pos hGap S.muFW_pos) S.lambda_pos) hN) hDeltaPos
    exact div_pos (by simpa [mul_assoc] using hNum)
      (mul_pos S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos hBatch)
  have hArgGtOne : 1 < S.fixedBatchLeadingLogArg N β batchSize := by
    have hDenPos : 0 < S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize := by
      exact mul_pos S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos hBatch
    have hDiv := (one_lt_div hDenPos).2 hInterior
    simpa [fixedBatchLeadingLogArg, one_mul] using hDiv
  have hEtaPos : 0 < ηStar := by
    dsimp [ηStar, etaStarFixedBatchClosedForm]
    refine mul_pos ?_ (Real.log_pos hArgGtOne)
    exact div_pos hBatch (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hN)
  have hExpStar :
      S.initialExpectedSuboptimality * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
      dsimp [a, ηStar, etaStarFixedBatchClosedForm, fixedBatchLeadingLogArg]
      field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne',
        S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne']
    calc
      S.initialExpectedSuboptimality * Real.exp (-(a * ηStar))
          = S.initialExpectedSuboptimality * Real.exp (-Real.log (S.fixedBatchLeadingLogArg N β batchSize)) := by
              rw [hMul]
      _ = S.initialExpectedSuboptimality / S.fixedBatchLeadingLogArg N β batchSize := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [A, a]
            unfold fixedBatchLeadingLogArg
            field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne',
              S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne', hDeltaPos.ne', hGap.ne']
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
      field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ ≤ (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.initialExpectedSuboptimality * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.initialExpectedSuboptimality * Real.exp (-(a * η))
          = S.initialExpectedSuboptimality * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.initialExpectedSuboptimality * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.fixedBatchFWExpectedSuboptimalityLeadingProxy ηStar N β batchSize
      = noiseTerm + A / a + A * ηStar := by
          unfold fixedBatchFWExpectedSuboptimalityLeadingProxy noiseTerm
          have hExpArg : -(S.muFW * S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpStar]
          dsimp [A]
          ring
    _ ≤ noiseTerm + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = noiseTerm + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize := by
          unfold fixedBatchFWExpectedSuboptimalityLeadingProxy noiseTerm
          have hExpArg : -(S.muFW * S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpEta]
          dsimp [A]
          ring

private theorem closedForm_fixedBatchLeading_lt_of_ne
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize η : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hNe : η ≠ S.etaStarFixedBatchClosedForm N β batchSize) :
    S.fixedBatchFWExpectedSuboptimalityLeadingProxy (S.etaStarFixedBatchClosedForm N β batchSize) N β batchSize
      < S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize := by
  let A := S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)
  let a : ℝ := S.muFW * S.lambda * N / batchSize
  let ηStar := S.etaStarFixedBatchClosedForm N β batchSize
  let u : ℝ := a * (η - ηStar)
  let noiseTerm : ℝ := S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * Real.sqrt ((1 - β) / batchSize)
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos hDeltaPos
  have haPos : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hN) hBatch
  have huNe : u ≠ 0 := by
    dsimp [u, a, ηStar]
    refine mul_ne_zero ?_ ?_
    · exact (ne_of_gt (div_pos (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hN) hBatch))
    · exact sub_ne_zero.mpr hNe
  have hArgPos : 0 < S.fixedBatchLeadingLogArg N β batchSize := by
    unfold fixedBatchLeadingLogArg
    have hNum :
        0 < ((S.initialExpectedSuboptimality * S.muFW * S.lambda) * N) * (1 - β) := by
      exact mul_pos (mul_pos (mul_pos (mul_pos hGap S.muFW_pos) S.lambda_pos) hN) hDeltaPos
    exact div_pos (by simpa [mul_assoc] using hNum)
      (mul_pos S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos hBatch)
  have hExpStar :
      S.initialExpectedSuboptimality * Real.exp (-(a * ηStar)) = A / a := by
    have hMul : a * ηStar = Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
      dsimp [a, ηStar, etaStarFixedBatchClosedForm, fixedBatchLeadingLogArg]
      field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne',
        S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne']
    calc
      S.initialExpectedSuboptimality * Real.exp (-(a * ηStar))
          = S.initialExpectedSuboptimality * Real.exp (-Real.log (S.fixedBatchLeadingLogArg N β batchSize)) := by
              rw [hMul]
      _ = S.initialExpectedSuboptimality / S.fixedBatchLeadingLogArg N β batchSize := by
            rw [Real.exp_neg, Real.exp_log hArgPos]
            simp [div_eq_mul_inv]
      _ = A / a := by
            dsimp [A, a]
            unfold fixedBatchLeadingLogArg
            field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne',
              S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne', hDeltaPos.ne', hGap.ne']
  have hOneLt : 1 < Real.exp (-u) + u := by
    have h := Real.add_one_lt_exp (neg_ne_zero.mpr huNe)
    linarith
  have hCoeffPos : 0 < A / a := div_pos hApos haPos
  have hCore : A / a < (A / a) * Real.exp (-u) + A * (η - ηStar) := by
    have hMul := mul_lt_mul_of_pos_left hOneLt hCoeffPos
    have hU : (A / a) * u = A * (η - ηStar) := by
      dsimp [u, a]
      field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne']
    calc
      A / a = (A / a) * 1 := by ring
      _ < (A / a) * (Real.exp (-u) + u) := hMul
      _ = (A / a) * Real.exp (-u) + A * (η - ηStar) := by rw [mul_add, hU]
  have hExpEta :
      S.initialExpectedSuboptimality * Real.exp (-(a * η))
        = (A / a) * Real.exp (-u) := by
    have hDecomp : -(a * η) = -(a * ηStar) + (-u) := by
      dsimp [u]
      ring
    calc
      S.initialExpectedSuboptimality * Real.exp (-(a * η))
          = S.initialExpectedSuboptimality * (Real.exp (-(a * ηStar)) * Real.exp (-u)) := by
              rw [hDecomp, Real.exp_add]
      _ = (S.initialExpectedSuboptimality * Real.exp (-(a * ηStar))) * Real.exp (-u) := by ring
      _ = (A / a) * Real.exp (-u) := by rw [hExpStar]
  calc
    S.fixedBatchFWExpectedSuboptimalityLeadingProxy ηStar N β batchSize
      = noiseTerm + A / a + A * ηStar := by
          unfold fixedBatchFWExpectedSuboptimalityLeadingProxy noiseTerm
          have hExpArg : -(S.muFW * S.lambda * ηStar * N / batchSize) = -(a * ηStar) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpStar]
          dsimp [A]
          ring
    _ < noiseTerm + ((A / a) * Real.exp (-u) + A * (η - ηStar)) + A * ηStar := by
          gcongr
    _ = noiseTerm + (A / a) * Real.exp (-u) + A * η := by ring
    _ = S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize := by
          unfold fixedBatchFWExpectedSuboptimalityLeadingProxy noiseTerm
          have hExpArg : -(S.muFW * S.lambda * η * N / batchSize) = -(a * η) := by
            dsimp [a]
            field_simp [hBatch.ne']
          rw [hExpArg, hExpEta]
          dsimp [A]
          ring

private theorem fixedBatchLeading_interior_of_isEtaMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer ηStar N β batchSize) :
    S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize
      < S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β) := by
  have hIsMinOn :
      IsMinOn (fun η => S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize) (Set.Ioi 0) ηStar := by
    intro η hη
    exact hMin.2 η hη
  have hLocalMin : IsLocalMin (fun η => S.fixedBatchFWExpectedSuboptimalityLeadingProxy η N β batchSize) ηStar := by
    exact hIsMinOn.localize.isLocalMin (Ioi_mem_nhds hMin.1)
  have hDerivZero :
      -(S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)
          * Real.exp (-(S.muFW * S.lambda * ηStar * N / batchSize)))
        + S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β) = 0 := by
    exact hLocalMin.hasDerivAt_eq_zero
      (S.hasDerivAt_fixedBatchFWExpectedSuboptimalityLeadingProxy (η := ηStar))
  have hExpLtOne : Real.exp (-(S.muFW * S.lambda * ηStar * N / batchSize)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hArgPos : 0 < S.muFW * S.lambda * ηStar * N / batchSize := by
      exact div_pos (mul_pos (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hMin.1) hN) hBatch
    linarith
  have hScalePos : 0 < S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize) := by
    exact mul_pos hGap (div_pos (mul_pos (mul_pos S.muFW_pos S.lambda_pos) hN) hBatch)
  have hLt :
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)
        < S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize) := by
    calc
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (1 - β)
        = S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)
            * Real.exp (-(S.muFW * S.lambda * ηStar * N / batchSize)) := by
            linarith
      _ < (S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)) * 1 := by
            exact mul_lt_mul_of_pos_left hExpLtOne hScalePos
      _ = S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize) := by ring
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hLt' :
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst
        < (S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)) * (1 - β) := by
    exact (div_lt_iff₀ hDeltaPos).1 hLt
  have hMul :
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize
        < ((S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)) * (1 - β)) * batchSize := by
    exact mul_lt_mul_of_pos_right hLt' hBatch
  calc
    S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize
      < ((S.initialExpectedSuboptimality * (S.muFW * S.lambda * N / batchSize)) * (1 - β)) * batchSize := hMul
    _ = S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β) := by
          field_simp [hBatch.ne']

/-- Fixed-batch leading-proxy eta minimizers are equal to the interior closed form. -/
private theorem fixedBatchEtaMinimizerEqClosedForm
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar
      = (batchSize / (S.muFW * S.lambda * N))
          * Real.log
              (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)
                / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)) := by
  have hInterior := S.fixedBatchLeading_interior_of_isEtaMinimizer hGap hN hBatch hβ1 hMin
  by_contra hNe
  have hLt := S.closedForm_fixedBatchLeading_lt_of_ne hGap hN hBatch hβ1 <| by
    simpa [etaStarFixedBatchClosedForm] using hNe
  have hClosedMin := S.closedForm_fixedBatchLeading_isMinimizer hGap hN hBatch hβ1 hInterior
  have hLe := hMin.2 (S.etaStarFixedBatchClosedForm N β batchSize) hClosedMin.1
  exact not_lt_of_ge hLe hLt

private theorem fixedBatchLeadingClosedFormFamily_eq
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {batchSize : ℝ} (hGap : 0 < S.initialExpectedSuboptimality) (hBatch : 0 < batchSize)
    {betaStar etaStar : ℝ → ℝ}
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ N0, 0 < N0 ∧
      ∀ N ≥ N0,
        etaStar N
          = (batchSize / (S.muFW * S.lambda * N))
              * Real.log
                  (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - betaStar N)
                    / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)) := by
  rcases hMin with ⟨N0, hN0, hMin⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le hN0 hN
  rcases hMin N hN with ⟨_, hβ1, hEtaMin⟩
  exact S.fixedBatchEtaMinimizerEqClosedForm hGap hNpos hBatch hβ1 hEtaMin

private theorem hasDerivAt_fixedBatchFWExpectedSuboptimalityReducedLeadingProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize) (hβ1 : β < 1) :
    HasDerivAt (fun β' => S.fixedBatchFWExpectedSuboptimalityReducedLeadingProxy N β' batchSize)
      (((S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize) / (S.muFW * S.lambda * N * (1 - β) ^ 2))
          * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
        - S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst
            / (2 * Real.sqrt batchSize * Real.sqrt (1 - β))) β := by
  let C := S.fixedBatchFWExpectedSuboptimalityLeadDriftConst
  let Z := S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst
  let K : ℝ := S.initialExpectedSuboptimality * S.muFW * S.lambda * N / (C * batchSize)
  have hCpos : 0 < C := by dsimp [C]; exact S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hKpos : 0 < K := by
    dsimp [K]
    have hNum : 0 < (S.initialExpectedSuboptimality * S.muFW * S.lambda) * N := by
      exact mul_pos (mul_pos (mul_pos hGap S.muFW_pos) S.lambda_pos) hN
    exact div_pos (by simpa [mul_assoc] using hNum) (mul_pos hCpos hBatch)
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
          (C * batchSize / (S.muFW * S.lambda * N))
            * ((1 + Real.log (K * (1 - β'))) / (1 - β')))
        (((C * batchSize) / (S.muFW * S.lambda * N * (1 - β) ^ 2))
            * Real.log (K * (1 - β))) β := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hFrac.const_mul (C * batchSize / (S.muFW * S.lambda * N))
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
    unfold fixedBatchFWExpectedSuboptimalityReducedLeadingProxy
    dsimp [C, Z, K]
    field_simp [S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne']
  · rw [show K * (1 - β) = S.fixedBatchLeadingLogArg N β batchSize by
          simp [K, C, fixedBatchLeadingLogArg, div_eq_mul_inv,
            mul_assoc, mul_left_comm, mul_comm]]
    ring

private theorem fixedBatchReducedLeading_deriv_eq_zero_of_isMomentumMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityReducedLeadingProxyMomentumMinimizer N β batchSize) :
    (((S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize) / (S.muFW * S.lambda * N * (1 - β) ^ 2))
        * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
      - S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst
          / (2 * Real.sqrt batchSize * Real.sqrt (1 - β))) = 0 := by
  rcases hMin with ⟨hβ0, hβ1, hMinOn⟩
  have hIsMinOn :
      IsMinOn (fun β' => S.fixedBatchFWExpectedSuboptimalityReducedLeadingProxy N β' batchSize) (Set.Ioo 0 1) β := by
    intro β' hβ'
    exact hMinOn β' hβ'.1 hβ'.2
  have hLocalMin : IsLocalMin (fun β' => S.fixedBatchFWExpectedSuboptimalityReducedLeadingProxy N β' batchSize) β := by
    exact hIsMinOn.localize.isLocalMin (Ioo_mem_nhds hβ0 hβ1)
  exact hLocalMin.hasDerivAt_eq_zero (S.hasDerivAt_fixedBatchFWExpectedSuboptimalityReducedLeadingProxy hGap hN hBatch hβ1)

private theorem fixedBatchGap_mul_sqrt_eq_of_isMomentumMinimizer
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst)
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityReducedLeadingProxyMomentumMinimizer N β batchSize) :
    (1 - β) * Real.sqrt (1 - β)
      = (2 * S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * (S.muFW * S.lambda)))
          * (batchSize * Real.sqrt batchSize)
          * (Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
  have hDerivZero :=
    S.fixedBatchReducedLeading_deriv_eq_zero_of_isMomentumMinimizer hGap hN hBatch hMin
  rcases hMin with ⟨_, hβ1, _⟩
  have hDeltaPos : 0 < 1 - β := sub_pos.mpr hβ1
  have hEq :
      ((S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize) / (S.muFW * S.lambda * N * (1 - β) ^ 2))
          * Real.log (S.fixedBatchLeadingLogArg N β batchSize)
        = S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst
            / (2 * Real.sqrt batchSize * Real.sqrt (1 - β)) := by
    linarith
  have hSqrtBatchPos : 0 < Real.sqrt batchSize := Real.sqrt_pos.2 hBatch
  have hSqrtDeltaPos : 0 < Real.sqrt (1 - β) := Real.sqrt_pos.2 hDeltaPos
  have hCross := hEq
  field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hBatch.ne', hNoise.ne',
    S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos.ne', hDeltaPos.ne', hSqrtBatchPos.ne', hSqrtDeltaPos.ne'] at hCross
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
      S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize * Real.log (S.fixedBatchLeadingLogArg N β batchSize) * 2 * Real.sqrt batchSize
        = S.muFW * S.lambda * N * ((1 - β) * Real.sqrt (1 - β)) * S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst := by
    exact (mul_right_cancel₀ hSqrtDeltaPos.ne') (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hCross)
  have hCancel' :
      S.muFW * S.lambda * N * S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * ((1 - β) * Real.sqrt (1 - β))
        = 2 * S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize * Real.sqrt batchSize
            * Real.log (S.fixedBatchLeadingLogArg N β batchSize) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hCancel.symm
  calc
    (1 - β) * Real.sqrt (1 - β)
        = (S.muFW * S.lambda * N * S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * ((1 - β) * Real.sqrt (1 - β)))
            / (S.muFW * S.lambda * N * S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst) := by
              field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hNoise.ne']
    _ = (2 * S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize * Real.sqrt batchSize
            * Real.log (S.fixedBatchLeadingLogArg N β batchSize))
            / (S.muFW * S.lambda * N * S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst) := by
              rw [hCancel']
    _ = (2 * S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * (S.muFW * S.lambda)))
            * (batchSize * Real.sqrt batchSize)
            * (Real.log (S.fixedBatchLeadingLogArg N β batchSize) / N) := by
              field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hN.ne', hNoise.ne']

private theorem fixedBatchLeadingTokenBudgetScalingBounds
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst)
    {betaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchFWExpectedSuboptimalityReducedLeadingProxy batchSize betaStar)
    {etaStar : ℝ → ℝ}
    (hEtaMin :
      S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / (S.muFW * S.lambda * N))
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.muFW * S.lambda * N)) := by
  rcases hMomentum with ⟨cLogLower, cLogUpper, N0Momentum,
    hcLogLower, hcLogUpper, hN0Momentum, hMomentum⟩
  rcases S.fixedBatchLeadingClosedFormFamily_eq hGap hBatch hEtaMin with
    ⟨N0Eta, hN0Eta, hEtaEq⟩
  let K := 2 * S.fixedBatchFWExpectedSuboptimalityLeadDriftConst / (S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst * (S.muFW * S.lambda))
  let cBetaLower : ℝ := (K * cLogLower) ^ (2 / 3 : ℝ)
  let cBetaUpper : ℝ := (K * cLogUpper) ^ (2 / 3 : ℝ)
  let cEtaLower : ℝ := cLogLower
  let cEtaUpper : ℝ := cLogUpper
  let N0 : ℝ := max (Real.exp 1) (max N0Momentum N0Eta)
  have hKpos : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos (by norm_num) S.fixedBatchFWExpectedSuboptimalityLeadDriftConst_pos) (mul_pos hNoise (mul_pos S.muFW_pos S.lambda_pos))
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
          = (1 / (S.muFW * S.lambda))
              * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := by
      calc
        etaStar N = S.etaStarFixedBatchClosedForm N (betaStar N) batchSize := by
          trans ((batchSize / (S.muFW * S.lambda * N))
            * Real.log
                (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - betaStar N)
                  / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)))
          · exact hEtaEqClosed
          · symm
            exact S.etaStarFixedBatchClosedForm_eq N (betaStar N) batchSize
        _ = (1 / (S.muFW * S.lambda))
              * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := by
              rw [S.etaStarFixedBatchClosedForm_eq_ratio hNpos.ne']
              field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hNpos.ne']
    have hBatchOverNNonneg : 0 ≤ batchSize / N := div_nonneg hBatch.le hNpos.le
    have hEtaMulBounds :=
      scale_bounds_of_nonneg hBatchOverNNonneg hLogLo' hLogHi'
    have hEtaScaleBounds :=
      scale_bounds_of_nonneg
        (show 0 ≤ 1 / (S.muFW * S.lambda) by exact one_div_nonneg.mpr (mul_nonneg S.muFW_pos.le S.lambda_pos.le))
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
        cEtaLower * (batchSize * Real.log N / (S.muFW * S.lambda * N))
          ≤ etaStar N := by
      calc
        cEtaLower * (batchSize * Real.log N / (S.muFW * S.lambda * N))
            = (1 / (S.muFW * S.lambda)) * ((batchSize / N) * (cEtaLower * Real.log N)) := by
                field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hNpos.ne']
        _ ≤ (1 / (S.muFW * S.lambda))
              * ((batchSize / N)
                  * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := hEtaScaleBounds.1
        _ = etaStar N := by rw [hEtaEq]
    have hEtaUpper :
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / (S.muFW * S.lambda * N)) := by
      calc
        etaStar N
            = (1 / (S.muFW * S.lambda))
                * ((batchSize / N) * Real.log (S.fixedBatchLeadingLogArg N (betaStar N) batchSize)) := hEtaEq
        _ ≤ (1 / (S.muFW * S.lambda)) * ((batchSize / N) * (cEtaUpper * Real.log N)) := hEtaScaleBounds.2
        _ = cEtaUpper * (batchSize * Real.log N / (S.muFW * S.lambda * N)) := by
              field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hNpos.ne']
    exact ⟨hGapLower, hGapUpper, hEtaLower, hEtaUpper⟩

/-! ------------------------------------------------------------------------
SL2: Fixed-Batch Large-Horizon Proxy Theorems
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

theorem fWExpectedSuboptimalitySLTheorem2_1_etaMinimizerEqClosedForm
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {N β batchSize ηStar : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hN : 0 < N) (hBatch : 0 < batchSize)
    (hβ1 : β < 1)
    (hMin : S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizer ηStar N β batchSize) :
    ηStar
      = (batchSize / (S.muFW * S.lambda * N))
          * Real.log
              (S.initialExpectedSuboptimality * S.muFW * S.lambda * N * (1 - β)
                / (S.fixedBatchFWExpectedSuboptimalityLeadDriftConst * batchSize)) := by
  exact S.fixedBatchEtaMinimizerEqClosedForm hGap hN hBatch hβ1 hMin

theorem fWExpectedSuboptimalitySLTheorem2_2_tokenBudgetScaling
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchFWExpectedSuboptimalityReducedLeadingProxy batchSize betaStar)
    (hEtaMin :
      S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧ 0 < N0 ∧
      ∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / N)
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / N) := by
  rcases S.fixedBatchLeadingTokenBudgetScalingBounds hGap hBatch hNoise hMomentum hEtaMin with
    ⟨cBetaLower, cBetaUpper, cEtaLowerOld, cEtaUpperOld, N0,
      hcBetaLower, hcBetaUpper, hcEtaLowerOld, hcEtaUpperOld, hN0, hBounds⟩
  refine ⟨cBetaLower, cBetaUpper, cEtaLowerOld / (S.muFW * S.lambda), cEtaUpperOld / (S.muFW * S.lambda), N0,
    hcBetaLower, hcBetaUpper, div_pos hcEtaLowerOld (mul_pos S.muFW_pos S.lambda_pos),
    div_pos hcEtaUpperOld (mul_pos S.muFW_pos S.lambda_pos), hN0, ?_⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le hN0 hN
  rcases hBounds N hN with ⟨hGapLower, hGapUpper, hEtaLowerOld, hEtaUpperOld⟩
  refine ⟨hGapLower, hGapUpper, ?_, ?_⟩
  · calc
      (cEtaLowerOld / (S.muFW * S.lambda)) * (batchSize * Real.log N / N)
          = cEtaLowerOld * (batchSize * Real.log N / (S.muFW * S.lambda * N)) := by
              field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hNpos.ne']
      _ ≤ etaStar N := hEtaLowerOld
  · calc
      etaStar N ≤ cEtaUpperOld * (batchSize * Real.log N / (S.muFW * S.lambda * N)) := hEtaUpperOld
      _ = (cEtaUpperOld / (S.muFW * S.lambda)) * (batchSize * Real.log N / N) := by
            field_simp [S.muFW_pos.ne', S.lambda_pos.ne', hNpos.ne']

theorem fWExpectedSuboptimalitySLTheorem2_FixedBatchLargeHorizonProxy
    (S : StochasticFrankWolfeKLGeometryContext Ω V)
    {batchSize : ℝ}
    (hGap : 0 < S.initialExpectedSuboptimality) (hBatch : 0 < batchSize)
    (hNoise : 0 < S.fixedBatchFWExpectedSuboptimalityLeadNoiseConst)
    {betaStar etaStar : ℝ → ℝ}
    (hMomentum :
      S.IsSmallBranchInteriorMomentumMinimizerFamilyFixedBatchFWExpectedSuboptimalityReducedLeadingProxy batchSize betaStar)
    (hEtaMin :
      S.IsFixedBatchFWExpectedSuboptimalityLeadingProxyEtaMinimizerFamily batchSize betaStar etaStar) :
    ∃ cBetaLower cBetaUpper cEtaLower cEtaUpper N0 T0,
      0 < cBetaLower ∧ 0 < cBetaUpper ∧ 0 < cEtaLower ∧ 0 < cEtaUpper ∧
      0 < N0 ∧ 0 < T0 ∧
      (∀ N ≥ N0,
        cBetaLower * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ))
          ≤ 1 - betaStar N ∧
        1 - betaStar N
          ≤ cBetaUpper * (batchSize * Real.rpow (Real.log N / N) (2 / 3 : ℝ)) ∧
        cEtaLower * (batchSize * Real.log N / N)
          ≤ etaStar N ∧
        etaStar N
          ≤ cEtaUpper * (batchSize * Real.log N / N)) ∧
      (∀ T ≥ T0,
        cBetaLower
            * (batchSize * Real.rpow (Real.log (batchSize * T) / (batchSize * T)) (2 / 3 : ℝ))
          ≤ 1 - betaStar (batchSize * T) ∧
        1 - betaStar (batchSize * T)
          ≤ cBetaUpper
              * (batchSize * Real.rpow (Real.log (batchSize * T) / (batchSize * T)) (2 / 3 : ℝ)) ∧
        cEtaLower * (Real.log (batchSize * T) / T)
          ≤ etaStar (batchSize * T) ∧
        etaStar (batchSize * T)
          ≤ cEtaUpper * (Real.log (batchSize * T) / T)) := by
  rcases S.fWExpectedSuboptimalitySLTheorem2_2_tokenBudgetScaling hGap hBatch hNoise hMomentum hEtaMin with
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

end StochasticFrankWolfeKLGeometryContext

end

end SteepestDescentOptimizationBounds
