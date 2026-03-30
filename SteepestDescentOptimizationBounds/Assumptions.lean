import Mathlib

namespace SteepestDescentOptimizationBounds

noncomputable section

open MeasureTheory
open ProbabilityTheory

/--
Continuous realization of the abstract dual pairing.

This is the extra analytic structure needed to connect a normed dual variable
`X† : VDual` to a Fréchet derivative `V →L[ℝ] ℝ`.
-/
structure ContinuousDualPairingContext
    (V VDual : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual] where
  toLinear : VDual →L[ℝ] V →L[ℝ] ℝ
  opNorm_le : ∀ xDual, ‖toLinear xDual‖ ≤ ‖xDual‖

namespace ContinuousDualPairingContext

variable {V VDual : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]

/-- The pairing map is Lipschitz from the dual norm into operator norm. -/
lemma opNorm_sub_le
    (P : ContinuousDualPairingContext V VDual) (xDual yDual : VDual) :
    ‖P.toLinear yDual - P.toLinear xDual‖ ≤ ‖yDual - xDual‖ := by
  calc
    ‖P.toLinear yDual - P.toLinear xDual‖ = ‖P.toLinear (yDual - xDual)‖ := by
      rw [ContinuousLinearMap.map_sub]
    _ ≤ ‖yDual - xDual‖ := P.opNorm_le _

end ContinuousDualPairingContext

/--
Canonical parameter block for stochastic steepest descent with weight decay and
momentum.
-/
structure StochasticSteepestDescentParameters where
  eta : ℝ
  lambda : ℝ
  beta : ℝ
  batchSize : ℕ
  eta_pos : 0 < eta
  lambda_pos : 0 < lambda
  lambda_eta_le_one : lambda * eta ≤ 1
  beta_nonneg : 0 ≤ beta
  beta_lt_one : beta < 1
  batchSize_pos : 0 < batchSize

namespace StochasticSteepestDescentParameters

/-- The real-valued minibatch size. -/
def batchSizeℝ (P : StochasticSteepestDescentParameters) : ℝ :=
  (P.batchSize : ℝ)

/-- The interpolation coefficient `λη` is nonnegative. -/
lemma lambda_eta_nonneg (P : StochasticSteepestDescentParameters) :
    0 ≤ P.lambda * P.eta :=
  mul_nonneg P.lambda_pos.le P.eta_pos.le

/-- The interpolation coefficient `λη` is strictly positive. -/
lemma lambda_eta_pos (P : StochasticSteepestDescentParameters) :
    0 < P.lambda * P.eta :=
  mul_pos P.lambda_pos P.eta_pos

/-- The interpolation coefficient `λη` is nonzero. -/
lemma lambda_eta_ne_zero (P : StochasticSteepestDescentParameters) :
    P.lambda * P.eta ≠ 0 :=
  ne_of_gt P.lambda_eta_pos

/-- The contraction factor `1 - λη` is nonnegative. -/
lemma one_sub_lambda_eta_nonneg (P : StochasticSteepestDescentParameters) :
    0 ≤ 1 - P.lambda * P.eta := by
  nlinarith [P.lambda_eta_le_one]

/-- The contraction factor `1 - λη` is at most `1`. -/
lemma one_sub_lambda_eta_le_one (P : StochasticSteepestDescentParameters) :
    1 - P.lambda * P.eta ≤ 1 := by
  nlinarith [P.lambda_eta_nonneg]

/-- The identity `1 - (1 - λη) = λη`. -/
lemma one_sub_one_sub_lambda_eta (P : StochasticSteepestDescentParameters) :
    1 - (1 - P.lambda * P.eta) = P.lambda * P.eta := by
  ring

/-- `β` lies in the unit interval. -/
lemma beta_le_one (P : StochasticSteepestDescentParameters) : P.beta ≤ 1 :=
  le_of_lt P.beta_lt_one

/-- The denominator `1 - β` is positive. -/
lemma one_sub_beta_pos (P : StochasticSteepestDescentParameters) : 0 < 1 - P.beta := by
  exact sub_pos.mpr P.beta_lt_one

/-- The denominator `1 - β` is nonzero. -/
lemma one_sub_beta_ne_zero (P : StochasticSteepestDescentParameters) :
    1 - P.beta ≠ 0 :=
  ne_of_gt P.one_sub_beta_pos

/-- The denominator `1 + β` is positive. -/
lemma one_add_beta_pos (P : StochasticSteepestDescentParameters) : 0 < 1 + P.beta := by
  linarith [P.beta_nonneg]

/-- The square-root argument `(1 - β) / (1 + β)` is nonnegative. -/
lemma one_sub_div_one_add_nonneg (P : StochasticSteepestDescentParameters) :
    0 ≤ (1 - P.beta) / (1 + P.beta) :=
  div_nonneg P.one_sub_beta_pos.le P.one_add_beta_pos.le

/-- The rational term `β² / (1 - β)` is nonnegative. -/
lemma beta_sq_div_one_sub_nonneg (P : StochasticSteepestDescentParameters) :
    0 ≤ P.beta ^ 2 / (1 - P.beta) :=
  div_nonneg (sq_nonneg _) P.one_sub_beta_pos.le

/-- The minibatch size is positive as a real number. -/
lemma batchSizeℝ_pos (P : StochasticSteepestDescentParameters) : 0 < P.batchSizeℝ := by
  simpa [batchSizeℝ] using (show (0 : ℝ) < (P.batchSize : ℝ) by exact_mod_cast P.batchSize_pos)

/-- The minibatch size is nonzero as a real number. -/
lemma batchSizeℝ_ne_zero (P : StochasticSteepestDescentParameters) :
    P.batchSizeℝ ≠ 0 :=
  ne_of_gt P.batchSizeℝ_pos

/-- `sqrt(batchSize)` is positive. -/
lemma sqrt_batchSizeℝ_pos (P : StochasticSteepestDescentParameters) :
    0 < Real.sqrt P.batchSizeℝ :=
  Real.sqrt_pos.2 P.batchSizeℝ_pos

/-- `sqrt(batchSize)` is nonzero. -/
lemma sqrt_batchSizeℝ_ne_zero (P : StochasticSteepestDescentParameters) :
    Real.sqrt P.batchSizeℝ ≠ 0 :=
  ne_of_gt P.sqrt_batchSizeℝ_pos

end StochasticSteepestDescentParameters

/-- Canonical uniform minibatch coefficient `1 / b`. -/
def uniformBatchWeight (b : ℕ) : ℝ :=
  1 / (b : ℝ)

lemma uniformBatchWeight_nonneg {b : ℕ} : 0 ≤ uniformBatchWeight b := by
  unfold uniformBatchWeight
  positivity

lemma uniformBatchWeight_sum_eq_one {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b) = 1 := by
  have hbnz : (b : ℝ) ≠ 0 := by positivity
  calc
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b)
      = (b : ℝ) * uniformBatchWeight b := by simp [uniformBatchWeight]
    _ = (b : ℝ) * (1 / (b : ℝ)) := by simp [uniformBatchWeight]
    _ = 1 := by field_simp [hbnz]

lemma uniformBatchWeight_sum_le_one {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b) ≤ 1 := by
  simp [uniformBatchWeight_sum_eq_one hb]

lemma uniformBatchWeight_sq_sum_eq {b : ℕ} (hb : 0 < b) :
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b ^ 2) = 1 / (b : ℝ) := by
  have hbnz : (b : ℝ) ≠ 0 := by positivity
  calc
    Finset.sum (Finset.range b) (fun _ => uniformBatchWeight b ^ 2)
      = (b : ℝ) * uniformBatchWeight b ^ 2 := by simp [uniformBatchWeight]
    _ = (b : ℝ) * (1 / (b : ℝ)) ^ 2 := by simp [uniformBatchWeight]
    _ = 1 / (b : ℝ) := by field_simp [hbnz]

/--
Stochastic gradient oracle `g(x; ζ)`.

Here `x` is a deterministic point in parameter space, `ζ` is a fresh sample draw, and
`g(x; ζ)` is the resulting stochastic gradient estimator.
-/
structure StochasticGradientOracle
    (V Ξ VDual : Type*)
    [MeasurableSpace VDual]
    (measurableSpaceΞ : MeasurableSpace Ξ) where
  g : V → Ξ → VDual
  g_measurable : ∀ x, @Measurable Ξ VDual measurableSpaceΞ inferInstance (g x)

/--
Fresh sample-draw process used to instantiate the oracle at each time and
sample index.

The ambient probability space `Ω` carries the whole table of fresh draws
`ζ_{t,i}`; the explicit sample type `Ξ` keeps the sample draws separate from the
derived gradient-noise object `ξ_{t,i}`.
-/
structure PerSampleDrawProcess
    (Ω Ξ : Type*)
    [MeasurableSpace Ω]
    (batchSize : ℕ)
    (measurableSpaceΞ : MeasurableSpace Ξ) where
  μ : Measure Ω
  prob : IsProbabilityMeasure μ
  draw : ℕ → Fin batchSize → Ω → Ξ
  draw_measurable : ∀ t i, @Measurable Ω Ξ inferInstance measurableSpaceΞ (draw t i)
  batchSize_pos : 0 < batchSize

/--
Assumption 1 in the oracle formulation.

For each deterministic iterate `W_t`, the per-sample estimator
`g(W_t; ζ_{t,i})` is unbiased, samples inside a minibatch are independent, and
whole minibatches are fresh independent draws across time.

This is different from a random-process formulation in which `W_t` itself would
be random and unbiasedness would be stated conditionally on the past
sigma-algebra. The current development deliberately keeps `W_t` deterministic
and places all randomness in the fresh sample draws `ζ_{t,i}`.
-/
structure Assumption1_UnbiasedFreshBatchSampling
    (Ω Ξ V VDual : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    [MeasurableSpace VDual] [BorelSpace VDual]
    (batchSize : ℕ)
    (measurableSpaceΞ : MeasurableSpace Ξ)
    (drawProcess : PerSampleDrawProcess Ω Ξ batchSize measurableSpaceΞ)
    (oracle : StochasticGradientOracle V Ξ VDual measurableSpaceΞ)
    (W : ℕ → V)
    (grad : V → VDual) where
  estimator_integrable :
    ∀ t i, Integrable (fun ω => oracle.g (W t) (drawProcess.draw t i ω)) drawProcess.μ
  estimator_mean_eq_grad :
    ∀ t i, ∫ ω, oracle.g (W t) (drawProcess.draw t i ω) ∂drawProcess.μ = grad (W t)
  withinBatch_iIndep :
    ∀ t, iIndepFun (fun i : Fin batchSize => drawProcess.draw t i) drawProcess.μ
  freshBatch_iIndep :
    iIndepFun (fun t ω i => drawProcess.draw t i ω) drawProcess.μ

/--
Assumption 2: a uniform per-sample second-moment bound on the derived noise
`ξ_{t,i} := ∇f(W_t) - g(W_t; ζ_{t,i})`.
-/
structure Assumption2_PerSampleGradientNoiseSecondMomentBound
    (Ω Ξ V VDual : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    [MeasurableSpace VDual] [BorelSpace VDual]
    (batchSize : ℕ)
    (measurableSpaceΞ : MeasurableSpace Ξ)
    (drawProcess : PerSampleDrawProcess Ω Ξ batchSize measurableSpaceΞ)
    (oracle : StochasticGradientOracle V Ξ VDual measurableSpaceΞ)
    (W : ℕ → V)
    (grad : V → VDual) where
  sigma : ℝ
  sigma_nonneg : 0 ≤ sigma
  second_moment_bound :
    ∀ t i,
      Integrable
          (fun ω => ‖grad (W t) - oracle.g (W t) (drawProcess.draw t i ω)‖ ^ 2)
          drawProcess.μ ∧
        ∫ ω, ‖grad (W t) - oracle.g (W t) (drawProcess.draw t i ω)‖ ^ 2 ∂drawProcess.μ ≤
          sigma ^ 2

/--
Weighted sums of vectors in the radius-`R` ball remain in that ball whenever
the coefficients are nonnegative and sum to at most `1`.

This is the convexity fact needed to use Assumption 4 on partial sums of noise
variables.
-/
lemma norm_sum_range_smul_le_of_nonneg_of_sum_le_one
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
          exact mul_le_mul_of_nonneg_left (hx i (Finset.mem_range.mp hi))
            (hα_nonneg i (Finset.mem_range.mp hi))
    _ = (Finset.sum (Finset.range n) α) * R := by
          rw [Finset.sum_mul]
    _ ≤ 1 * R := by
          exact mul_le_mul_of_nonneg_right hα_sum hR_nonneg
    _ = R := by ring

/--
Prefix sums inherit the same radius bound from a larger nonnegative
coefficient family whose total mass is at most `1`.
-/
lemma norm_sum_range_smul_le_of_nonneg_prefix
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
      intro i hiN hiK
      exact hα_nonneg i (Finset.mem_range.mp hiN)
    linarith
  have hx_k : ∀ i < k, ‖x i‖ ≤ R := by
    intro i hi
    exact hx i (lt_of_lt_of_le hi hk)
  exact
    norm_sum_range_smul_le_of_nonneg_of_sum_le_one
      hα_nonneg_k hα_sum_k hx_k hR_nonneg

/--
Global Lipschitz continuity of a map under the chosen domain and codomain norms.
-/
def GlobalLipschitzUnderNormPair
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : X → Y) (L : ℝ) : Prop :=
  0 < L ∧ ∀ x y, ‖g y - g x‖ ≤ L * ‖y - x‖

namespace GlobalLipschitzUnderNormPair

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {g : X → Y} {L : ℝ}

lemma pos (h : GlobalLipschitzUnderNormPair g L) : 0 < L :=
  h.1

lemma nonneg (h : GlobalLipschitzUnderNormPair g L) : 0 ≤ L :=
  h.1.le

lemma bound (h : GlobalLipschitzUnderNormPair g L) :
    ∀ x y, ‖g y - g x‖ ≤ L * ‖y - x‖ :=
  h.2

end GlobalLipschitzUnderNormPair

/--
Local Lipschitz continuity of a map on the closed ball `‖x‖ ≤ R` under the
chosen domain and codomain norms.
-/
def LocalLipschitzOnClosedBallUnderNormPair
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : X → Y) (R L : ℝ) : Prop :=
  0 < L ∧ ∀ ⦃x y⦄, ‖x‖ ≤ R → ‖y‖ ≤ R →
    ‖g y - g x‖ ≤ L * ‖y - x‖

namespace LocalLipschitzOnClosedBallUnderNormPair

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {g : X → Y} {R L : ℝ}

lemma pos (h : LocalLipschitzOnClosedBallUnderNormPair g R L) : 0 < L :=
  h.1

lemma nonneg (h : LocalLipschitzOnClosedBallUnderNormPair g R L) : 0 ≤ L :=
  h.1.le

lemma bound (h : LocalLipschitzOnClosedBallUnderNormPair g R L) :
    ∀ ⦃x y⦄, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖g y - g x‖ ≤ L * ‖y - x‖ :=
  h.2

end LocalLipschitzOnClosedBallUnderNormPair

/--
Assumption 3: the objective gradient is locally `L`-Lipschitz on the primal
closed ball `‖x‖ ≤ 1 / λ`.
-/
structure Assumption3_FLocalSmoothness
    {V VDual : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (fGrad : V → VDual) (lambda : ℝ) where
  L : ℝ
  local_lipschitz : LocalLipschitzOnClosedBallUnderNormPair fGrad (1 / lambda) L

namespace Assumption3_FLocalSmoothness

variable {V VDual : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
variable {fGrad : V → VDual} {lambda : ℝ}

lemma pos (h : Assumption3_FLocalSmoothness fGrad lambda) : 0 < h.L :=
  h.local_lipschitz.pos

lemma nonneg (h : Assumption3_FLocalSmoothness fGrad lambda) : 0 ≤ h.L :=
  h.local_lipschitz.nonneg

lemma bound (h : Assumption3_FLocalSmoothness fGrad lambda) :
    ∀ ⦃X Y⦄, ‖X‖ ≤ 1 / lambda → ‖Y‖ ≤ 1 / lambda →
      ‖fGrad Y - fGrad X‖ ≤ h.L * ‖Y - X‖ :=
  h.local_lipschitz.bound

end Assumption3_FLocalSmoothness

/--
Assumption 4 as used in Lemma 5: a local smooth proxy potential on the
closed dual ball `‖x‖ ≤ noiseRadius`.

This assumption does not require `x ↦ (1 / 2) * ‖x‖^2` for the target dual norm
to be smooth. Instead, it asks for an auxiliary potential `g` with derivative-like
map `Φ` such that, on the closed `noiseRadius` ball:

- `g` dominates `‖x‖^2 / 2`,
- `Φ` is the Fréchet derivative of `g` through the chosen pairing,
- `Φ` is `D`-Lipschitz on that ball,
- `Φ 0 = 0`.

The stochastic side then separately assumes that the derived per-sample noises
lie in this ball almost surely.
-/
structure Assumption4_LocalSmoothProxyPotential
    (V VDual : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    (pairing : ContinuousDualPairingContext VDual V) where
  potential : VDual → ℝ
  mirrorMap : VDual → V
  D : ℝ
  noiseRadius : ℝ
  noiseRadius_nonneg : 0 ≤ noiseRadius
  potential_zero : potential 0 = 0
  mirrorMap_zero : mirrorMap 0 = 0
  potential_fderiv_eq :
    ∀ x,
      HasFDerivAt potential
        (pairing.toLinear (mirrorMap x)) x
  mirrorMap_continuous : Continuous mirrorMap
  mirrorMap_local_lipschitz :
    LocalLipschitzOnClosedBallUnderNormPair mirrorMap noiseRadius D
  norm_sq_le_two_potential_on_ball : ∀ x, ‖x‖ ≤ noiseRadius → ‖x‖ ^ 2 ≤ 2 * potential x

/--
`A` is a linear minimization oracle solution for the dual vector `X†` if it lies
in the unit primal ball and minimizes the pairing over that ball.
-/
def IsLMO
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (XDual : StrongDual ℝ V) (A : V) : Prop :=
  ‖A‖ ≤ 1 ∧ ∀ B, ‖B‖ ≤ 1 → XDual A ≤ XDual B

namespace Assumption4_LocalSmoothProxyPotential

variable {V VDual : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
variable {pairing : ContinuousDualPairingContext VDual V}

lemma D_pos
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) : 0 < P.D :=
  P.mirrorMap_local_lipschitz.pos

lemma D_nonneg
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) : 0 ≤ P.D :=
  P.mirrorMap_local_lipschitz.nonneg

lemma potential_continuous
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) :
    Continuous P.potential := by
  refine continuous_iff_continuousAt.mpr ?_
  intro x
  exact (P.potential_fderiv_eq x).continuousAt

lemma potential_nonneg_of_mem_noiseRadius
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) (x : VDual)
    (hx : ‖x‖ ≤ P.noiseRadius) :
    0 ≤ P.potential x := by
  have h := P.norm_sq_le_two_potential_on_ball x hx
  nlinarith [sq_nonneg ‖x‖]

lemma mirrorMap_norm_le_of_mem_noiseRadius
    (P : Assumption4_LocalSmoothProxyPotential V VDual pairing) (x : VDual)
    (hx : ‖x‖ ≤ P.noiseRadius) :
    ‖P.mirrorMap x‖ ≤ P.D * ‖x‖ := by
  have h :=
    P.mirrorMap_local_lipschitz.bound
      (show ‖(0 : VDual)‖ ≤ P.noiseRadius by simpa using P.noiseRadius_nonneg)
      hx
  simpa [P.mirrorMap_zero] using h

end Assumption4_LocalSmoothProxyPotential

/--
Assumption 12: `f` is star-convex at the designated reference point `W_*`.
-/
def Assumption12_StarConvexityAtReferencePoint
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (WStar : V) : Prop :=
  ∀ W α, 0 ≤ α → α ≤ 1 →
    f ((1 - α) • W + α • WStar) ≤ (1 - α) * f W + α * f WStar

namespace Assumption12_StarConvexityAtReferencePoint

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {f : V → ℝ} {WStar : V}

lemma star_convex (h : Assumption12_StarConvexityAtReferencePoint f WStar) :
    ∀ W α, 0 ≤ α → α ≤ 1 →
      f ((1 - α) • W + α • WStar) ≤ (1 - α) * f W + α * f WStar :=
  h

end Assumption12_StarConvexityAtReferencePoint

/--
Canonical geometric context for stochastic steepest descent with weight decay.

This is the single theorem-facing base carrier for Proposition 9, Lemma 13,
Corollaries 10/11, Proposition 6, Lemma 5 instantiation, and Theorem 14.

It is also the current global deterministic geometry-and-trajectory context used
by the formalization.

The theorem-facing stochastic model is a fresh-sampling oracle
`g(W_t; ζ_{t,i})` on the ambient probability space `Ω`. The derived noise
`ξ_{t,i} := ∇f(W_t) - g(W_t; ζ_{t,i})` is still exposed as a compatibility
layer because the current proofs of Lemma 5 and Proposition 6 remain noise-based
internally.

The iterate and momentum trajectories are still deterministic sequences
`W : ℕ → V` and `momentum : ℕ → StrongDual ℝ V`. Accordingly, Assumption 1 is
stated directly in terms of fresh sample draws rather than as a conditional
statement about a random iterate process.
-/
structure StochasticSteepestDescentGeometryContext
    (Ω V : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticSteepestDescentParameters where
  -- Objective f is differentiable and bounded below,
  f : V → ℝ
  fGrad : V → StrongDual ℝ V
  fderiv_eq :
    ∀ X, HasFDerivAt f (fGrad X) X
  pairing : ContinuousDualPairingContext (StrongDual ℝ V) V
  WStar : V
  WStar_optimality : ∀ W, f WStar ≤ f W
  WStar_bound : ‖WStar‖ ≤ 1 / lambda

  -- Deterministic trajectory/dynamics.
  W : ℕ → V
  W0_bound : ‖W 0‖ ≤ 1 / lambda
  -- Deterministic momentum trajectory.
  momentum : ℕ → StrongDual ℝ V
  momentum_zero : momentum 0 = 0
  momentum_succ :
    ∀ t,
      momentum (t + 1) =
        beta • momentum t + (1 - beta) • fGrad (W (t + 1))
  -- Update rule
  aStar : ℕ → V
  aStar_spec :
    ∀ t, IsLMO (beta • momentum t + (1 - beta) • fGrad (W t)) (aStar t)
  update_eq :
    ∀ t,
      W (t + 1) = ((1 - lambda * eta) • W t)
        + eta • aStar t

  -- Sampling/oracle data.
  Ξ : Type*
  sampleMeasurableSpace : MeasurableSpace Ξ
  drawProcess : PerSampleDrawProcess Ω Ξ batchSize sampleMeasurableSpace
  stochasticGradientOracle :
    StochasticGradientOracle V Ξ (StrongDual ℝ V) sampleMeasurableSpace

  -- Assumptions.
  assumption1_sampling :
    Assumption1_UnbiasedFreshBatchSampling
      Ω Ξ V (StrongDual ℝ V) batchSize sampleMeasurableSpace
      drawProcess stochasticGradientOracle W fGrad
  assumption2_secondMoment :
    Assumption2_PerSampleGradientNoiseSecondMomentBound
      Ω Ξ V (StrongDual ℝ V) batchSize sampleMeasurableSpace
      drawProcess stochasticGradientOracle W fGrad
  assumption3_fLocalSmoothness :
    Assumption3_FLocalSmoothness fGrad lambda
  assumption4_localProxyPotential :
    Assumption4_LocalSmoothProxyPotential V (StrongDual ℝ V) pairing
  assumption12_starConvexity :
    Assumption12_StarConvexityAtReferencePoint f WStar
  -- Almost-sure support condition connecting oracle noise to the proxy radius.
  oracle_sample_norm_le_noiseRadius_ae :
    ∀ t i, ∀ᵐ ω ∂drawProcess.μ,
      ‖fGrad (W t) - stochasticGradientOracle.g (W t) (drawProcess.draw t i ω)‖ ≤
        assumption4_localProxyPotential.noiseRadius

attribute [instance] StochasticSteepestDescentGeometryContext.sampleMeasurableSpace

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The probability measure carried by the concrete sample-draw process. -/
def μ (S : StochasticSteepestDescentGeometryContext Ω V) : Measure Ω :=
  S.drawProcess.μ

/-- The probability-measure witness carried by the concrete sample-draw process. -/
def prob (S : StochasticSteepestDescentGeometryContext Ω V) : IsProbabilityMeasure S.μ :=
  S.drawProcess.prob

/-- The true gradient sequence is defined from the smooth optimization data. -/
def grad (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : StrongDual ℝ V :=
  S.fGrad (S.W t)

/-- The concrete fresh sample draw `ζ_{t,i}`. -/
def sampleDraw (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (i : Fin S.batchSize) :
    Ω → S.Ξ :=
  S.drawProcess.draw t i

/--
The concrete stochastic gradient estimator sample at the deterministic visited
iterate `W_t`, namely `g(W_t; ζ_{t,i})`.
-/
def stochasticGradientSample
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (i : Fin S.batchSize)
    (ω : Ω) : StrongDual ℝ V :=
  S.stochasticGradientOracle.g (S.W t) (S.sampleDraw t i ω)

/--
The derived per-sample gradient noise
`ξ_{t,i} := ∇f(W_t) - g(W_t; ζ_{t,i})`.

This remains the compatibility interface used by the current proof stack, even
though the theorem-facing stochastic model is now oracle-first.
-/
def ξ (S : StochasticSteepestDescentGeometryContext Ω V) :
    ℕ → Fin S.batchSize → Ω → StrongDual ℝ V :=
  fun t i ω => S.grad t - S.stochasticGradientSample t i ω

/-- The concrete batch-valued noise draw at time `t`. -/
def batchNoise (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    Ω → Fin S.batchSize → StrongDual ℝ V :=
  fun ω i => S.ξ t i ω

/-- The Assumption-2 noise scale. -/
def sigma (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.assumption2_secondMoment.sigma

lemma sigma_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) : 0 ≤ S.sigma :=
  S.assumption2_secondMoment.sigma_nonneg

lemma sample_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, StronglyMeasurable (S.ξ t i) := by
  intro t i
  have hEstimatorMeas :
      Measurable (S.stochasticGradientSample t i) := by
    simpa [StochasticSteepestDescentGeometryContext.stochasticGradientSample,
      StochasticSteepestDescentGeometryContext.sampleDraw] using
      (S.stochasticGradientOracle.g_measurable (S.W t)).comp (S.drawProcess.draw_measurable t i)
  exact stronglyMeasurable_const.sub hEstimatorMeas.stronglyMeasurable

lemma withinBatch_iIndep
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, iIndepFun (fun i : Fin S.batchSize => S.ξ t i) S.μ := by
  intro t
  let h : ∀ i : Fin S.batchSize, S.Ξ → StrongDual ℝ V :=
    fun _ ζ => S.grad t - S.stochasticGradientOracle.g (S.W t) ζ
  have hh : ∀ i : Fin S.batchSize, Measurable (h i) := by
    intro i
    simpa [h] using measurable_const.sub (S.stochasticGradientOracle.g_measurable (S.W t))
  simpa [StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.stochasticGradientSample,
    StochasticSteepestDescentGeometryContext.sampleDraw,
    StochasticSteepestDescentGeometryContext.grad, h] using
    (S.assumption1_sampling.withinBatch_iIndep t).comp h hh

lemma freshBatch_iIndep
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    iIndepFun (fun t => S.batchNoise t) S.μ := by
  let h : ∀ t : ℕ, (Fin S.batchSize → S.Ξ) → (Fin S.batchSize → StrongDual ℝ V) :=
    fun t z i => S.grad t - S.stochasticGradientOracle.g (S.W t) (z i)
  have hh : ∀ t : ℕ, Measurable (h t) := by
    intro t
    rw [measurable_pi_iff]
    intro i
    simpa [h] using measurable_const.sub
      ((S.stochasticGradientOracle.g_measurable (S.W t)).comp (measurable_pi_apply i))
  simpa [StochasticSteepestDescentGeometryContext.batchNoise,
    StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.stochasticGradientSample,
    StochasticSteepestDescentGeometryContext.sampleDraw,
    StochasticSteepestDescentGeometryContext.grad, h] using
    S.assumption1_sampling.freshBatch_iIndep.comp h hh

lemma sample_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, Integrable (S.ξ t i) S.μ := by
  intro t i
  letI : IsProbabilityMeasure S.μ := S.prob
  have hConst : Integrable (fun _ : Ω => S.grad t) S.μ := integrable_const _
  exact hConst.sub (by
    simpa [StochasticSteepestDescentGeometryContext.μ,
      StochasticSteepestDescentGeometryContext.stochasticGradientSample,
      StochasticSteepestDescentGeometryContext.sampleDraw] using
      S.assumption1_sampling.estimator_integrable t i)

lemma sample_mean_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, ∫ ω, S.ξ t i ω ∂S.μ = 0 := by
  intro t i
  letI : IsProbabilityMeasure S.μ := S.prob
  have hEstInt :
      Integrable (S.stochasticGradientSample t i) S.μ := by
    simpa [StochasticSteepestDescentGeometryContext.μ,
      StochasticSteepestDescentGeometryContext.stochasticGradientSample,
      StochasticSteepestDescentGeometryContext.sampleDraw] using
      S.assumption1_sampling.estimator_integrable t i
  have hConst : Integrable (fun _ : Ω => S.grad t) S.μ := integrable_const _
  have hIntegralConst : ∫ ω, (fun _ : Ω => S.grad t) ω ∂S.μ = S.grad t := by
    rw [integral_const]
    simp
  have hEstimatorMean : ∫ ω, S.stochasticGradientSample t i ω ∂S.μ = S.grad t := by
    simpa [StochasticSteepestDescentGeometryContext.grad,
      StochasticSteepestDescentGeometryContext.stochasticGradientSample,
      StochasticSteepestDescentGeometryContext.sampleDraw,
      StochasticSteepestDescentGeometryContext.μ] using
      S.assumption1_sampling.estimator_mean_eq_grad t i
  change ∫ ω, (S.grad t - S.stochasticGradientSample t i ω) ∂S.μ = 0
  rw [integral_sub hConst hEstInt, hIntegralConst]
  rw [hEstimatorMean]
  simp

lemma second_moment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i,
      Integrable (fun ω => ‖S.ξ t i ω‖ ^ 2) S.μ ∧
        ∫ ω, ‖S.ξ t i ω‖ ^ 2 ∂S.μ ≤ S.sigma ^ 2 := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.μ,
    StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.grad,
    StochasticSteepestDescentGeometryContext.stochasticGradientSample,
    StochasticSteepestDescentGeometryContext.sampleDraw,
    StochasticSteepestDescentGeometryContext.sigma] using
    S.assumption2_secondMoment.second_moment_bound t i

/-- The Assumption-4 proxy potential `g`. -/
def potential (S : StochasticSteepestDescentGeometryContext Ω V) :
    StrongDual ℝ V → ℝ :=
  S.assumption4_localProxyPotential.potential

/-- The Assumption-4 mirror map `Φ`. -/
def mirrorMap (S : StochasticSteepestDescentGeometryContext Ω V) :
    StrongDual ℝ V → V :=
  S.assumption4_localProxyPotential.mirrorMap

/-- The Assumption-4 smoothness constant. -/
def D (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.assumption4_localProxyPotential.D

/-- The Assumption-4 noise support radius. -/
def noiseRadius (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.assumption4_localProxyPotential.noiseRadius

/-- The Assumption-3 local smoothness constant. -/
def L (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.assumption3_fLocalSmoothness.L

/-- The Assumption-3 smoothness constant is strictly positive. -/
lemma L_pos (S : StochasticSteepestDescentGeometryContext Ω V) : 0 < S.L :=
  S.assumption3_fLocalSmoothness.pos

lemma D_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) : 0 ≤ S.D :=
  S.assumption4_localProxyPotential.D_nonneg

lemma noiseRadius_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) :
    0 ≤ S.noiseRadius :=
  S.assumption4_localProxyPotential.noiseRadius_nonneg

lemma potential_zero (S : StochasticSteepestDescentGeometryContext Ω V) :
    S.potential 0 = 0 :=
  S.assumption4_localProxyPotential.potential_zero

lemma mirrorMap_zero (S : StochasticSteepestDescentGeometryContext Ω V) :
    S.mirrorMap 0 = 0 :=
  S.assumption4_localProxyPotential.mirrorMap_zero

lemma potential_fderiv_eq (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ x,
      HasFDerivAt S.potential
        (S.pairing.toLinear (S.mirrorMap x)) x :=
  S.assumption4_localProxyPotential.potential_fderiv_eq

lemma potential_continuous (S : StochasticSteepestDescentGeometryContext Ω V) :
    Continuous S.potential :=
  S.assumption4_localProxyPotential.potential_continuous

lemma mirrorMap_continuous (S : StochasticSteepestDescentGeometryContext Ω V) :
    Continuous S.mirrorMap :=
  S.assumption4_localProxyPotential.mirrorMap_continuous

lemma norm_sq_le_two_potential_of_mem_noiseRadius
    (S : StochasticSteepestDescentGeometryContext Ω V) (x : StrongDual ℝ V)
    (hx : ‖x‖ ≤ S.noiseRadius) :
    ‖x‖ ^ 2 ≤ 2 * S.potential x :=
  S.assumption4_localProxyPotential.norm_sq_le_two_potential_on_ball x hx

lemma potential_nonneg_of_mem_noiseRadius
    (S : StochasticSteepestDescentGeometryContext Ω V) (x : StrongDual ℝ V)
    (hx : ‖x‖ ≤ S.noiseRadius) :
    0 ≤ S.potential x :=
  Assumption4_LocalSmoothProxyPotential.potential_nonneg_of_mem_noiseRadius
    S.assumption4_localProxyPotential x hx

lemma mirrorMap_norm_le_of_mem_noiseRadius
    (S : StochasticSteepestDescentGeometryContext Ω V) (x : StrongDual ℝ V)
    (hx : ‖x‖ ≤ S.noiseRadius) :
    ‖S.mirrorMap x‖ ≤ S.D * ‖x‖ :=
  Assumption4_LocalSmoothProxyPotential.mirrorMap_norm_le_of_mem_noiseRadius
    S.assumption4_localProxyPotential x hx

lemma sample_norm_le_noiseRadius_ae
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, ∀ᵐ ω ∂S.μ, ‖S.ξ t i ω‖ ≤ S.noiseRadius := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.μ,
    StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.grad,
    StochasticSteepestDescentGeometryContext.stochasticGradientSample,
    StochasticSteepestDescentGeometryContext.sampleDraw,
    StochasticSteepestDescentGeometryContext.noiseRadius] using
    S.oracle_sample_norm_le_noiseRadius_ae t i

/-- The center of the radius-`η` feasible ball used by the update. -/
def stepCenter (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : V :=
  (1 - S.lambda * S.eta) • S.W t

/-- The point `X_t = (1 - λη) W_t + λη W_*`. -/
def interpolatedPoint (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : V :=
  S.stepCenter t + (S.lambda * S.eta) • S.WStar

/-- The suboptimality gap at time `t`. -/
def suboptimality (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  S.f (S.W t) - S.f S.WStar

/-- The concrete minibatch stochastic gradient estimator at time `t`. -/
def minibatchGradient
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  Finset.sum Finset.univ
    (fun i : Fin S.batchSize =>
      uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω)

/-- The derived stochastic-gradient sample is unbiased at each visited iterate. -/
theorem stochasticGradientSample_mean_eq_grad
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (i : Fin S.batchSize) :
    ∫ ω, S.stochasticGradientSample t i ω ∂S.μ = S.grad t := by
  simpa [StochasticSteepestDescentGeometryContext.grad,
    StochasticSteepestDescentGeometryContext.stochasticGradientSample,
    StochasticSteepestDescentGeometryContext.sampleDraw,
    StochasticSteepestDescentGeometryContext.μ] using
    S.assumption1_sampling.estimator_mean_eq_grad t i

/-- The derived minibatch stochastic-gradient estimator is unbiased. -/
theorem minibatchGradient_mean_eq_grad
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    ∫ ω, S.minibatchGradient t ω ∂S.μ = S.grad t := by
  letI : IsProbabilityMeasure S.μ := S.prob
  have hInt :
      ∀ i ∈ (Finset.univ : Finset (Fin S.batchSize)),
        Integrable (fun ω =>
          uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω) S.μ := by
    intro i hi
    have hEstimator :
        Integrable (S.stochasticGradientSample t i) S.μ := by
      simpa [StochasticSteepestDescentGeometryContext.μ,
        StochasticSteepestDescentGeometryContext.stochasticGradientSample,
        StochasticSteepestDescentGeometryContext.sampleDraw] using
        S.assumption1_sampling.estimator_integrable t i
    exact hEstimator.smul (uniformBatchWeight S.batchSize)
  have hCoeffSum :
      Finset.sum (Finset.univ : Finset (Fin S.batchSize))
        (fun _ : Fin S.batchSize => uniformBatchWeight S.batchSize) = 1 := by
    simpa [StochasticSteepestDescentParameters.batchSizeℝ] using
      uniformBatchWeight_sum_eq_one S.batchSize_pos
  calc
    ∫ ω, S.minibatchGradient t ω ∂S.μ
      = Finset.sum (Finset.univ : Finset (Fin S.batchSize))
          (fun i => ∫ ω, uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω ∂S.μ) := by
            simp [StochasticSteepestDescentGeometryContext.minibatchGradient,
              MeasureTheory.integral_finset_sum, hInt]
    _ = Finset.sum (Finset.univ : Finset (Fin S.batchSize))
          (fun i => uniformBatchWeight S.batchSize • S.grad t) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [integral_smul, S.stochasticGradientSample_mean_eq_grad t i]
    _ = (Finset.sum (Finset.univ : Finset (Fin S.batchSize))
          (fun _ : Fin S.batchSize => uniformBatchWeight S.batchSize)) • S.grad t := by
            rw [← Finset.sum_smul]
    _ = (1 : ℝ) • S.grad t := by rw [hCoeffSum]
    _ = S.grad t := by simp

/-- The momentum-corrected search dual `C_t`. -/
def C (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : StrongDual ℝ V :=
  S.beta • S.momentum t + (1 - S.beta) • S.grad t

/-- The initial gradient norm. -/
def initialGradNorm (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  ‖S.grad 0‖

/-- The deterministic mean of the concrete minibatch-average noise. -/
def minibatchNoise (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    StrongDual ℝ V :=
  ∫ ω, Finset.sum Finset.univ
      (fun i : Fin S.batchSize => uniformBatchWeight S.batchSize • S.ξ t i ω) ∂S.μ

/-- The norm of the deterministic minibatch-noise mean. -/
def minibatchNoiseNorm (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ‖S.minibatchNoise t‖

/-- The momentum error `E_t = ∇f(W_t) - M_t`. -/
def momentumError (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    StrongDual ℝ V :=
  S.grad t - S.momentum t

/-- The norm of the momentum error. -/
def momentumErrorNorm (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ‖S.momentumError t‖

/-- The gradient-splitting residual `∇f(W_t) - C_t`. -/
def nesterovError (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    StrongDual ℝ V :=
  S.grad t - S.C t

/-- The Nesterov error `‖∇f(W_t) - C_t‖`. -/
def nesterovErrorNorm (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ‖S.nesterovError t‖

/-- The Corollary-11 momentum-noise prefactor. -/
def momentumNoisePrefactor (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  Real.sqrt ((1 - S.beta) / (1 + S.beta)) * S.beta + (1 - S.beta)

/-- The drift component of the momentum error recursion. -/
def driftComponent (S : StochasticSteepestDescentGeometryContext Ω V) : ℕ → StrongDual ℝ V
  | 0 => S.grad 0
  | t + 1 => S.beta • S.driftComponent t + S.beta • (S.grad (t + 1) - S.grad t)

/-- The noise component of the momentum error recursion. -/
def noiseComponent (S : StochasticSteepestDescentGeometryContext Ω V) : ℕ → StrongDual ℝ V
  | 0 => 0
  | t + 1 => S.beta • S.noiseComponent t + (1 - S.beta) • S.minibatchNoise (t + 1)

/-- The norm of the noise component. -/
def noiseComponentNorm (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ‖S.noiseComponent t‖

/-- The Nesterov vector split is definitional from the concrete `C_t`. -/
lemma nesterovError_split (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    S.grad t = S.C t + S.nesterovError t := by
  simp [StochasticSteepestDescentGeometryContext.nesterovError, StochasticSteepestDescentGeometryContext.C,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The Nesterov error is a norm and is therefore nonnegative. -/
lemma nesterovErrorNorm_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    0 ≤ S.nesterovErrorNorm t := by
  simp [StochasticSteepestDescentGeometryContext.nesterovErrorNorm]

/-- The concrete Nesterov residual acts on vectors with the usual operator-norm bound. -/
lemma nesterovError_apply_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (v : V) :
    (S.nesterovError t) v ≤ S.nesterovErrorNorm t * ‖v‖ := by
  calc
    (S.nesterovError t) v ≤ ‖(S.nesterovError t) v‖ := le_abs_self _
    _ ≤ ‖S.nesterovError t‖ * ‖v‖ := by
      simpa using (S.nesterovError t).le_opNorm v
    _ = S.nesterovErrorNorm t * ‖v‖ := by
      simp [StochasticSteepestDescentGeometryContext.nesterovErrorNorm]

/-- The Corollary-11 momentum-noise prefactor is nonnegative. -/
lemma momentumNoisePrefactor_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) :
    0 ≤ S.momentumNoisePrefactor := by
  have hSqrtNonneg : 0 ≤ Real.sqrt ((1 - S.beta) / (1 + S.beta)) := Real.sqrt_nonneg _
  exact add_nonneg (mul_nonneg hSqrtNonneg S.beta_nonneg) S.one_sub_beta_pos.le

/-- `W_*` is optimal by Assumption 12. -/
lemma wStar_optimal (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ W, S.f S.WStar ≤ S.f W :=
  S.WStar_optimality

/-- The star-convex interpolation inequality from Assumption 12. -/
lemma star_convex_prop (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ W α, 0 ≤ α → α ≤ 1 →
      S.f ((1 - α) • W + α • S.WStar) ≤ (1 - α) * S.f W + α * S.f S.WStar :=
  Assumption12_StarConvexityAtReferencePoint.star_convex S.assumption12_starConvexity

end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
