import SteepestDescentScalingLaws.Commons

/-!
Star-convex expected-suboptimality scaling laws for independent weight-decay
variation.

Upstream:
- `SteepestDescentScalingLaws.Commons`
- `SteepestDescentOptimizationBounds.StarConvex`

Downstream:
- the weight-decay-only scaling discussion and any later formalized README or
  blueprint summaries.

This file freezes all theorem coefficients except the weight decay `λ` and
studies the theorem-facing proxy as a function of `(λ, η)`.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

namespace StochasticStarConvexGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [SecondCountableTopology (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- The `λ`-independent drift constant in the weight-decay-only star-convex proxy. -/
def starConvexIndependentWeightDecayProxyDriftConst
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  4 * S.L * (1 + S.beta ^ 2 / (1 - S.beta))

/-- The `λ`-independent minibatch-noise constant in the weight-decay-only proxy. -/
def starConvexIndependentWeightDecayProxyNoiseConst
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  2
    * (S.beta * Real.sqrt ((1 - S.beta) / (1 + S.beta)) + (1 - S.beta))
    * Real.sqrt S.D
    * S.sigma

/-- The `λ`-independent linear residual coefficient in the weight-decay-only proxy. -/
def starConvexIndependentWeightDecayProxyResidualConst
    (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  (2 * S.beta / (1 - S.beta)) * S.initialExpectedMomentumError

/--
The star-convex expected-suboptimality proxy obtained by varying only weight
decay `λ` while freezing all other theorem coefficients.
-/
def starConvexIndependentWeightDecayProxy
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) (lambdaValue η : ℝ) : ℝ :=
  S.initialExpectedSuboptimality * (1 - lambdaValue * η) ^ T
    + S.starConvexIndependentWeightDecayProxyNoiseConst / lambdaValue
    + (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
        + S.starConvexIndependentWeightDecayProxyResidualConst) * η

/--
The exact closed-form interior stationary point of the weight-decay-only proxy.

This is the theorem-facing candidate that comes from differentiating the proxy
with respect to `η` and solving the first-order condition on the interior branch.
-/
def starConvexIndependentWeightDecayInteriorStationaryPoint
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) (lambdaValue : ℝ) : ℝ :=
  (1 / lambdaValue)
    * (1 - Real.rpow
        ((S.starConvexIndependentWeightDecayProxyDriftConst
              + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue)
          / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2))
        (1 / ((T - 1 : ℕ) : ℝ)))

/-- The interior stationary-point predicate for the weight-decay-only proxy. -/
def IsStarConvexIndependentWeightDecayInteriorStationaryPoint
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) (lambdaValue η : ℝ) : Prop :=
  0 < η ∧ η < 1 / lambdaValue ∧
    HasDerivAt (fun η' => S.starConvexIndependentWeightDecayProxy T lambdaValue η') 0 η

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

private def starConvexIndependentWeightDecayStationaryRatio
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) (lambdaValue : ℝ) : ℝ :=
  (S.starConvexIndependentWeightDecayProxyDriftConst
      + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue)
    / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2)

private def independentWeightDecayLowerScaleThreshold
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) (q : ℝ) : ℝ :=
  let alpha := Real.rpow (1 - q) ((T - 1 : ℕ) : ℝ)
  max 1
    (max
      (2 * S.starConvexIndependentWeightDecayProxyDriftConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * alpha))
      (2 * S.starConvexIndependentWeightDecayProxyResidualConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * alpha)))

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

private theorem starConvexIndependentWeightDecayProxyDriftConst_pos
    (S : StochasticStarConvexGeometryContext Ω V) :
    0 < S.starConvexIndependentWeightDecayProxyDriftConst := by
  dsimp [starConvexIndependentWeightDecayProxyDriftConst]
  have hFrac : 0 ≤ S.beta ^ 2 / (1 - S.beta) := S.beta_sq_div_one_sub_nonneg
  have hCoeff : 0 < 4 * S.L := by nlinarith [S.L_pos]
  have hParen : 0 < 1 + S.beta ^ 2 / (1 - S.beta) := by linarith
  exact mul_pos hCoeff hParen

private theorem starConvexIndependentWeightDecayProxyResidualConst_nonneg
    (S : StochasticStarConvexGeometryContext Ω V) :
    0 ≤ S.starConvexIndependentWeightDecayProxyResidualConst := by
  dsimp [starConvexIndependentWeightDecayProxyResidualConst]
  have hFrac : 0 ≤ 2 * S.beta / (1 - S.beta) := by
    exact div_nonneg (mul_nonneg (by positivity) S.beta_nonneg) S.one_sub_beta_pos.le
  exact mul_nonneg hFrac S.initialExpectedMomentumError_nonneg

private theorem hasDerivAt_starConvexIndependentWeightDecayProxy
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) {lambdaValue η : ℝ} :
    HasDerivAt
      (fun η' => S.starConvexIndependentWeightDecayProxy T lambdaValue η')
      (-(S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue * (1 - lambdaValue * η) ^ (T - 1))
        + (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
            + S.starConvexIndependentWeightDecayProxyResidualConst))
      η := by
  have hInner :
      HasDerivAt (fun η' : ℝ => 1 - lambdaValue * η') (-lambdaValue) η := by
    have hLinear :
        HasDerivAt (fun η' : ℝ => (-lambdaValue) * η') (-lambdaValue) η := by
      simpa [mul_comm] using (hasDerivAt_id η).const_mul (-lambdaValue)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hLinear.add_const (1 : ℝ)
  have hPow :
      HasDerivAt (fun η' : ℝ => (1 - lambdaValue * η') ^ T)
        ((T : ℝ) * (1 - lambdaValue * η) ^ (T - 1) * (-lambdaValue)) η := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hInner.pow T
  have hMain :
      HasDerivAt
        (fun η' : ℝ => S.initialExpectedSuboptimality * (1 - lambdaValue * η') ^ T)
        (S.initialExpectedSuboptimality * ((T : ℝ) * (1 - lambdaValue * η) ^ (T - 1) * (-lambdaValue))) η := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hPow.const_mul S.initialExpectedSuboptimality
  have hLinear :
      HasDerivAt
        (fun η' : ℝ =>
          (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
            + S.starConvexIndependentWeightDecayProxyResidualConst) * η')
        (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
          + S.starConvexIndependentWeightDecayProxyResidualConst) η := by
    simpa [mul_comm] using
      (hasDerivAt_id η).const_mul
        (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
          + S.starConvexIndependentWeightDecayProxyResidualConst)
  have hConst :
      HasDerivAt
        (fun _ : ℝ => S.starConvexIndependentWeightDecayProxyNoiseConst / lambdaValue)
        0 η := by
    simpa using hasDerivAt_const η (S.starConvexIndependentWeightDecayProxyNoiseConst / lambdaValue)
  convert hMain.add (hConst.add hLinear) using 1
  · funext η'
    simp [starConvexIndependentWeightDecayProxy, add_assoc, add_comm]
  · ring

private theorem one_sub_lambda_mul_stationaryPoint
    (S : StochasticStarConvexGeometryContext Ω V)
    (T : ℕ) {lambdaValue : ℝ}
    (hLambda : 0 < lambdaValue) :
    1 - lambdaValue * S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue
      =
        Real.rpow
          (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
          (1 / ((T - 1 : ℕ) : ℝ)) := by
  dsimp [starConvexIndependentWeightDecayInteriorStationaryPoint,
    starConvexIndependentWeightDecayStationaryRatio]
  field_simp [hLambda.ne']
  ring

private theorem stationaryRatio_nonneg
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 0 < T) {lambdaValue : ℝ} (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality) :
    0 ≤ S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue := by
  dsimp [starConvexIndependentWeightDecayStationaryRatio]
  have hNum :
      0 ≤
        S.starConvexIndependentWeightDecayProxyDriftConst
          + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue := by
    have hDrift : 0 ≤ S.starConvexIndependentWeightDecayProxyDriftConst := by
      exact S.starConvexIndependentWeightDecayProxyDriftConst_pos.le
    have hResidual :
        0 ≤ S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue := by
      exact mul_nonneg S.starConvexIndependentWeightDecayProxyResidualConst_nonneg hLambda.le
    linarith
  have hDen :
      0 ≤ S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2 := by
    exact mul_nonneg (mul_nonneg hGap.le (by exact_mod_cast hT.le)) (sq_nonneg _)
  exact div_nonneg hNum hDen

private theorem stationaryRatio_pos
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 0 < T) {lambdaValue : ℝ} (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality) :
    0 < S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue := by
  dsimp [starConvexIndependentWeightDecayStationaryRatio]
  have hNum :
      0 <
        S.starConvexIndependentWeightDecayProxyDriftConst
          + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue := by
    have hDrift : 0 < S.starConvexIndependentWeightDecayProxyDriftConst :=
      S.starConvexIndependentWeightDecayProxyDriftConst_pos
    have hResidual :
        0 ≤ S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue := by
      exact mul_nonneg S.starConvexIndependentWeightDecayProxyResidualConst_nonneg hLambda.le
    exact add_pos_of_pos_of_nonneg hDrift hResidual
  have hDen :
      0 < S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2 := by
    have hTS : 0 < (T : ℝ) := by exact_mod_cast hT
    exact mul_pos (mul_pos hGap hTS) (sq_pos_iff.mpr hLambda.ne')
  exact div_pos hNum hDen

private theorem stationaryPoint_pow_eq_ratio
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T) {lambdaValue : ℝ} (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality) :
    (1 - lambdaValue * S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue) ^ (T - 1)
      = S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue := by
  have hTm1PosNat : 0 < T - 1 := by omega
  have hTm1Pos : 0 < ((T - 1 : ℕ) : ℝ) := by exact_mod_cast hTm1PosNat
  have hRatioNonneg :
      0 ≤ S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue :=
    S.stationaryRatio_nonneg (T := T) (show 0 < T by omega) hLambda hGap
  rw [S.one_sub_lambda_mul_stationaryPoint T hLambda]
  have hRpow :
      Real.rpow
        (Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
          (1 / ((T - 1 : ℕ) : ℝ)))
        ((T - 1 : ℕ) : ℝ)
        =
        S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue := by
    calc
      Real.rpow
          (Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
            (1 / ((T - 1 : ℕ) : ℝ)))
          ((T - 1 : ℕ) : ℝ)
        =
          Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
            ((1 / ((T - 1 : ℕ) : ℝ)) * ((T - 1 : ℕ) : ℝ)) := by
              symm
              exact Real.rpow_mul hRatioNonneg _ _
      _ = S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue := by
            have hMul : (1 / ((T - 1 : ℕ) : ℝ)) * ((T - 1 : ℕ) : ℝ) = 1 := by
              field_simp [hTm1Pos.ne']
            rw [hMul]
            simp
  simpa [Real.rpow_natCast] using hRpow

private theorem stationaryPoint_lt_one_div_lambda
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T) {lambdaValue : ℝ}
    (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hInterior :
      S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue < 1) :
    S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue < 1 / lambdaValue := by
  have hTm1PosNat : 0 < T - 1 := by omega
  have hExpPos : 0 < 1 / ((T - 1 : ℕ) : ℝ) := by
    positivity
  have hRatioPos :
      0 < S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue :=
    S.stationaryRatio_pos (T := T) (show 0 < T by omega) hLambda hGap
  have hRootLtOne :
      Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ)) < 1 := by
    simpa using Real.rpow_lt_rpow hRatioPos.le hInterior hExpPos
  have hRootNonneg :
      0 ≤ Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ)) := by
    exact Real.rpow_nonneg (S.stationaryRatio_nonneg (T := T) (show 0 < T by omega) hLambda hGap) _
  have hRootPos :
      0 < Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ)) := by
    exact Real.rpow_pos_of_pos hRatioPos _
  dsimp [starConvexIndependentWeightDecayInteriorStationaryPoint]
  have hInvPos : 0 < 1 / lambdaValue := one_div_pos.mpr hLambda
  have hInnerLt : 1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ)) < 1 := by
    exact sub_lt_self 1 hRootPos
  calc
    S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue
      = (1 / lambdaValue)
          * (1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
              (1 / ((T - 1 : ℕ) : ℝ))) := by
              simp [starConvexIndependentWeightDecayInteriorStationaryPoint,
                starConvexIndependentWeightDecayStationaryRatio]
    _ < (1 / lambdaValue) * 1 := by
          exact mul_lt_mul_of_pos_left hInnerLt hInvPos
    _ = 1 / lambdaValue := by ring

private theorem stationaryPoint_pos
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T) {lambdaValue : ℝ}
    (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality)
    (hInterior :
      S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue < 1) :
    0 < S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue := by
  have hTm1PosNat : 0 < T - 1 := by omega
  have hExpPos : 0 < 1 / ((T - 1 : ℕ) : ℝ) := by
    positivity
  have hRatioPos :
      0 < S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue :=
    S.stationaryRatio_pos (T := T) (show 0 < T by omega) hLambda hGap
  have hRootLtOne :
      Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ)) < 1 := by
    simpa using Real.rpow_lt_rpow hRatioPos.le hInterior hExpPos
  dsimp [starConvexIndependentWeightDecayInteriorStationaryPoint]
  refine mul_pos (one_div_pos.mpr hLambda) ?_
  exact sub_pos.mpr hRootLtOne

private theorem stationaryPoint_deriv_zero
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T) {lambdaValue : ℝ}
    (hLambda : 0 < lambdaValue)
    (hGap : 0 < S.initialExpectedSuboptimality) :
    HasDerivAt
      (fun η' => S.starConvexIndependentWeightDecayProxy T lambdaValue η')
      0
      (S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue) := by
  have hTpos : 0 < (T : ℝ) := by positivity
  have hDeriv :=
    S.hasDerivAt_starConvexIndependentWeightDecayProxy T
      (lambdaValue := lambdaValue)
      (η := S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue)
  have hPowEq :
      (1 - lambdaValue * S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue) ^ (T - 1)
        = S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue :=
    S.stationaryPoint_pow_eq_ratio (T := T) hT hLambda hGap
  have hZero :
      -(S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue
          * (1 - lambdaValue * S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue) ^ (T - 1))
        + (S.starConvexIndependentWeightDecayProxyDriftConst / lambdaValue
            + S.starConvexIndependentWeightDecayProxyResidualConst)
        = 0 := by
    rw [hPowEq]
    dsimp [starConvexIndependentWeightDecayStationaryRatio]
    have hTne : (T : ℝ) ≠ 0 := by positivity
    field_simp [hLambda.ne', hGap.ne', hTne]
    ring
  simpa [hZero] using hDeriv

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

/--
Exact closed-form interior stationary point for the weight-decay-only
star-convex expected-suboptimality proxy.
-/
theorem starConvexScalingLawsIndependentWeightDecay_exactInteriorStationaryPoint
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T)
    (hGap : 0 < S.initialExpectedSuboptimality)
    {lambdaValue : ℝ} (hLambda : 0 < lambdaValue)
    (hInterior :
      (S.starConvexIndependentWeightDecayProxyDriftConst
          + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue)
        / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2) < 1) :
    S.IsStarConvexIndependentWeightDecayInteriorStationaryPoint
      T lambdaValue (S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue) := by
  refine ⟨S.stationaryPoint_pos (T := T) hT hLambda hGap hInterior,
    S.stationaryPoint_lt_one_div_lambda (T := T) hT hLambda hGap hInterior,
    S.stationaryPoint_deriv_zero (T := T) hT hLambda hGap⟩

/--
Eventual inverse-scaling lower and upper bounds for the exact interior
stationary point under independent weight-decay scaling.

This is the theorem-facing `Ω(1 / λ)` statement, packaged with the matching
trivial `O(1 / λ)` upper bound.
-/
theorem starConvexScalingLawsIndependentWeightDecay_inverseScaling
    (S : StochasticStarConvexGeometryContext Ω V)
    {T : ℕ} (hT : 2 ≤ T)
    (hGap : 0 < S.initialExpectedSuboptimality) :
    ∀ {q : ℝ}, 0 < q → q < 1 →
      ∃ lambdaThreshold, 0 < lambdaThreshold ∧
        ∀ {lambdaValue : ℝ}, lambdaThreshold ≤ lambdaValue →
          q / lambdaValue
            ≤ S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue ∧
          S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue
            ≤ 1 / lambdaValue := by
  intro q hq0 hq1
  let alpha : ℝ := Real.rpow (1 - q) ((T - 1 : ℕ) : ℝ)
  let lambdaThreshold : ℝ := S.independentWeightDecayLowerScaleThreshold T q
  have hTm1PosNat : 0 < T - 1 := by omega
  have hBaseNonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq1.le
  have hAlphaPos : 0 < alpha := by
    dsimp [alpha]
    exact Real.rpow_pos_of_pos (sub_pos.mpr hq1) _
  have hThresholdPos : 0 < lambdaThreshold := by
    dsimp [lambdaThreshold, independentWeightDecayLowerScaleThreshold]
    positivity
  refine ⟨lambdaThreshold, hThresholdPos, ?_⟩
  intro lambdaValue hLambdaThreshold
  have hLambda : 0 < lambdaValue := lt_of_lt_of_le hThresholdPos hLambdaThreshold
  have hOne : (1 : ℝ) ≤ lambdaValue := by
    have : (1 : ℝ) ≤ lambdaThreshold := by
      dsimp [lambdaThreshold, independentWeightDecayLowerScaleThreshold]
      exact le_max_left _ _
    exact le_trans this hLambdaThreshold
  have hDriftBound :
      2 * S.starConvexIndependentWeightDecayProxyDriftConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * alpha)
        ≤ lambdaValue := by
    have :
        2 * S.starConvexIndependentWeightDecayProxyDriftConst
          / (S.initialExpectedSuboptimality * (T : ℝ) * alpha)
          ≤ lambdaThreshold := by
      dsimp [lambdaThreshold, independentWeightDecayLowerScaleThreshold]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans this hLambdaThreshold
  have hResidualBound :
      2 * S.starConvexIndependentWeightDecayProxyResidualConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * alpha)
        ≤ lambdaValue := by
    have :
        2 * S.starConvexIndependentWeightDecayProxyResidualConst
          / (S.initialExpectedSuboptimality * (T : ℝ) * alpha)
          ≤ lambdaThreshold := by
      dsimp [lambdaThreshold, independentWeightDecayLowerScaleThreshold]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact le_trans this hLambdaThreshold
  have hTRealPos : 0 < (T : ℝ) := by positivity
  have hCoeffDenPos :
      0 < S.initialExpectedSuboptimality * (T : ℝ) := by
    exact mul_pos hGap hTRealPos
  have hDriftRatioHalf :
      S.starConvexIndependentWeightDecayProxyDriftConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2)
        ≤ alpha / 2 := by
    have hDenPos :
        0 < S.initialExpectedSuboptimality * (T : ℝ) * alpha := by
      exact mul_pos hCoeffDenPos hAlphaPos
    have hAOverLambda :
        S.starConvexIndependentWeightDecayProxyDriftConst
          / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue)
          ≤ alpha / 2 := by
      have hMul :
          2 * S.starConvexIndependentWeightDecayProxyDriftConst
            ≤ lambdaValue * (S.initialExpectedSuboptimality * (T : ℝ) * alpha) := by
        exact (div_le_iff₀ hDenPos).mp hDriftBound
      have hGoal :
          S.starConvexIndependentWeightDecayProxyDriftConst
            ≤ (alpha / 2) * (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue) := by
        nlinarith
      exact (div_le_iff₀ (mul_pos hCoeffDenPos hLambda)).2 hGoal
    have hInvSqLeInv : 1 / lambdaValue ^ 2 ≤ 1 / lambdaValue := by
      field_simp [hLambda.ne']
      nlinarith [hLambda, hOne]
    have hCoeffNonneg :
        0 ≤ S.starConvexIndependentWeightDecayProxyDriftConst
            / (S.initialExpectedSuboptimality * (T : ℝ)) := by
      exact div_nonneg S.starConvexIndependentWeightDecayProxyDriftConst_pos.le hCoeffDenPos.le
    calc
      S.starConvexIndependentWeightDecayProxyDriftConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2)
        = (S.starConvexIndependentWeightDecayProxyDriftConst
            / (S.initialExpectedSuboptimality * (T : ℝ))) * (1 / lambdaValue ^ 2) := by
            field_simp [hGap.ne', hTRealPos.ne', hLambda.ne']
      _ ≤ (S.starConvexIndependentWeightDecayProxyDriftConst
            / (S.initialExpectedSuboptimality * (T : ℝ))) * (1 / lambdaValue) := by
            exact mul_le_mul_of_nonneg_left hInvSqLeInv hCoeffNonneg
      _ = S.starConvexIndependentWeightDecayProxyDriftConst
            / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue) := by
            field_simp [hGap.ne', hTRealPos.ne', hLambda.ne']
      _ ≤ alpha / 2 := hAOverLambda
  have hResidualRatioHalf :
      S.starConvexIndependentWeightDecayProxyResidualConst
        / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue)
        ≤ alpha / 2 := by
    have hDenPos :
        0 < S.initialExpectedSuboptimality * (T : ℝ) * alpha := by
      exact mul_pos hCoeffDenPos hAlphaPos
    have hMul :
        2 * S.starConvexIndependentWeightDecayProxyResidualConst
          ≤ lambdaValue * (S.initialExpectedSuboptimality * (T : ℝ) * alpha) := by
      exact (div_le_iff₀ hDenPos).mp hResidualBound
    have hGoal :
        S.starConvexIndependentWeightDecayProxyResidualConst
          ≤ (alpha / 2) * (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue) := by
      nlinarith
    exact (div_le_iff₀ (mul_pos hCoeffDenPos hLambda)).2 hGoal
  have hRatioLeAlpha :
      S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue ≤ alpha := by
    dsimp [starConvexIndependentWeightDecayStationaryRatio]
    have hSplit :
        (S.starConvexIndependentWeightDecayProxyDriftConst
            + S.starConvexIndependentWeightDecayProxyResidualConst * lambdaValue)
          / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2)
          =
            S.starConvexIndependentWeightDecayProxyDriftConst
              / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue ^ 2)
            + S.starConvexIndependentWeightDecayProxyResidualConst
                / (S.initialExpectedSuboptimality * (T : ℝ) * lambdaValue) := by
      field_simp [hGap.ne', hTRealPos.ne', hLambda.ne']
    rw [hSplit]
    linarith
  have hExpPos : 0 < 1 / ((T - 1 : ℕ) : ℝ) := by positivity
  have hRootLe :
      Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ))
        ≤ 1 - q := by
    calc
      Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue) (1 / ((T - 1 : ℕ) : ℝ))
        ≤ Real.rpow alpha (1 / ((T - 1 : ℕ) : ℝ)) := by
            exact Real.rpow_le_rpow
              (S.stationaryRatio_nonneg (T := T) (show 0 < T by omega) hLambda hGap)
              hRatioLeAlpha hExpPos.le
      _ = 1 - q := by
            dsimp [alpha]
            rw [← Real.rpow_mul hBaseNonneg]
            have hMul : ((T - 1 : ℕ) : ℝ) * (1 / ((T - 1 : ℕ) : ℝ)) = 1 := by
              field_simp [show (((T - 1 : ℕ) : ℝ)) ≠ 0 by positivity]
            rw [hMul, Real.rpow_one]
  have hLowerInner :
      q ≤ 1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
            (1 / ((T - 1 : ℕ) : ℝ)) := by
    linarith
  have hLower :
      q / lambdaValue
        ≤ S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue := by
    have hInvPos : 0 < 1 / lambdaValue := one_div_pos.mpr hLambda
    calc
      q / lambdaValue = (1 / lambdaValue) * q := by ring
      _ ≤ (1 / lambdaValue)
            * (1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
                (1 / ((T - 1 : ℕ) : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hLowerInner hInvPos.le
      _ = S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue := by
            simp [starConvexIndependentWeightDecayInteriorStationaryPoint,
              starConvexIndependentWeightDecayStationaryRatio]
  have hRootNonneg :
      0 ≤ Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
          (1 / ((T - 1 : ℕ) : ℝ)) := by
    exact Real.rpow_nonneg
      (S.stationaryRatio_nonneg (T := T) (show 0 < T by omega) hLambda hGap) _
  have hUpper :
      S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue
        ≤ 1 / lambdaValue := by
    have hInvNonneg : 0 ≤ 1 / lambdaValue := by positivity
    calc
      S.starConvexIndependentWeightDecayInteriorStationaryPoint T lambdaValue
        = (1 / lambdaValue)
            * (1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
                (1 / ((T - 1 : ℕ) : ℝ))) := by
              simp [starConvexIndependentWeightDecayInteriorStationaryPoint,
                starConvexIndependentWeightDecayStationaryRatio]
      _ ≤ (1 / lambdaValue) * 1 := by
            have hInnerLe :
                1 - Real.rpow (S.starConvexIndependentWeightDecayStationaryRatio T lambdaValue)
                  (1 / ((T - 1 : ℕ) : ℝ)) ≤ 1 := by
              linarith
            exact mul_le_mul_of_nonneg_left hInnerLe hInvNonneg
      _ = 1 / lambdaValue := by ring
  exact ⟨hLower, hUpper⟩

end StochasticStarConvexGeometryContext

end

end SteepestDescentOptimizationBounds
