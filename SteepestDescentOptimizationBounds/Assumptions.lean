import Mathlib

/-!
Core stochastic geometry and oracle assumptions for the steepest-descent and
Frank-Wolfe developments.

Upstream dependency:

- `Mathlib` supplies the linear-analytic and measure-theoretic infrastructure.

Downstream use:

- `WeightAndUpdateBounds.lean`, `StarConvex.lean`, and the Frank-Wolfe layers
  reuse the geometry contexts and the Assumptions 1--4 support lemmas.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

open MeasureTheory
open ProbabilityTheory

/--
Continuous realization of the abstract dual pairing.

This is the extra analytic structure needed to connect a normed dual variable
`X† : VDual` to a Fréchet derivative `V →L[ℝ] ℝ`.
-/
-- Public Geometry Contexts and Compatibility API

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

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

end StochasticSteepestDescentParameters

/-- Canonical uniform minibatch coefficient `1 / b`. -/
def uniformBatchWeight (b : ℕ) : ℝ :=
  1 / (b : ℝ)

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
Flatten the doubly indexed sample family `(t, i)` into a single natural index.

This lets the stochastic support layer talk about "all previously revealed
samples" using a single prefix sigma-algebra.
-/
def flatSample
    {Ω β : Type*}
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (sample : ℕ → Fin batchSize → Ω → β)
    (n : ℕ) : Ω → β :=
  fun ω =>
    sample (n / batchSize) ⟨n % batchSize, Nat.mod_lt _ hb⟩ ω

/-- Lexicographic flattening of the pair `(t, i)`. -/
def flatSampleIndex {batchSize : ℕ} (t : ℕ) (i : Fin batchSize) : ℕ :=
  t * batchSize + i.1

/--
Evaluating the flattened sample process at the lexicographic index of `(t, i)`
recovers the original sample `sample t i`.
-/
lemma flatSample_at_flatSampleIndex
    {Ω β : Type*}
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (sample : ℕ → Fin batchSize → Ω → β)
    (t : ℕ)
    (i : Fin batchSize) :
    flatSample hb sample (flatSampleIndex t i) = sample t i := by
  funext ω
  have hDiv : flatSampleIndex t i / batchSize = t := by
    unfold flatSampleIndex
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hb]
    simp [Nat.div_eq_of_lt i.2]
  have hMod : flatSampleIndex t i % batchSize = i.1 := by
    unfold flatSampleIndex
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt i.2
  simp [flatSample, hDiv, hMod]

/--
Tuple of all flattened samples strictly preceding `(t, i)`.

Conditioning on this tuple formalizes the "fresh sample" part of Assumption 1.
-/
def flatSamplePrefixTuple
    {Ω β : Type*}
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (sample : ℕ → Fin batchSize → Ω → β)
    (t : ℕ)
    (i : Fin batchSize) : Ω → Fin (flatSampleIndex t i) → β :=
  fun ω j => flatSample hb sample j ω

/-- The flattened sample process is globally measurable whenever each sample is. -/
lemma flatSample_measurable
    {Ω β : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace β]
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (sample : ℕ → Fin batchSize → Ω → β)
    (sample_measurable : ∀ t i, Measurable (sample t i))
    (j : ℕ) :
    Measurable (flatSample hb sample j) := by
  simpa [flatSample] using
    sample_measurable (j / batchSize) ⟨j % batchSize, Nat.mod_lt _ hb⟩

/--
Sigma-algebra generated by the current iterate `W_t` together with all samples
strictly preceding `(t, i)` in lexicographic order.
-/
def samplePrefixSigma
    {Ω β V : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace V]
    [MeasurableSpace β]
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (W : ℕ → Ω → V)
    (sample : ℕ → Fin batchSize → Ω → β)
    (t : ℕ)
    (i : Fin batchSize) : MeasurableSpace Ω :=
  MeasurableSpace.comap (W t) (inferInstance : MeasurableSpace V) ⊔
    MeasurableSpace.comap
      (flatSamplePrefixTuple hb sample t i)
      (inferInstance : MeasurableSpace (Fin (flatSampleIndex t i) → β))

/--
The prefix sigma-algebra is a sub-sigma-algebra of the ambient measurable
space whenever its generators are ambient-measurable.
-/
lemma samplePrefixSigma_le_of_measurable
    {Ω β V : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace V]
    [MeasurableSpace β]
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (W : ℕ → Ω → V)
    (sample : ℕ → Fin batchSize → Ω → β)
    (hSample : ∀ t i, @Measurable Ω β inferInstance inferInstance (sample t i))
    (t : ℕ)
    (hW : @Measurable Ω V inferInstance inferInstance (W t))
    (i : Fin batchSize) :
    samplePrefixSigma hb W sample t i ≤ inferInstanceAs (MeasurableSpace Ω) := by
  let tuple := flatSamplePrefixTuple hb sample t i
  have hTupleMeasurable : Measurable tuple := by
    exact measurable_pi_lambda tuple <| fun j =>
      flatSample_measurable hb sample hSample j
  exact sup_le hW.comap_le hTupleMeasurable.comap_le

/--
Every previously revealed flattened sample is measurable with respect to the
prefix sigma-algebra generated by `W_t` and that flattened sample table.
-/
lemma flatSample_measurable_of_lt
    {Ω β V : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace V]
    [MeasurableSpace β]
    {batchSize : ℕ}
    (hb : 0 < batchSize)
    (W : ℕ → Ω → V)
    (sample : ℕ → Fin batchSize → Ω → β)
    {t : ℕ} {i : Fin batchSize} {j : ℕ}
    (hj : j < flatSampleIndex t i) :
    Measurable[samplePrefixSigma hb W sample t i] (flatSample hb sample j) := by
  let tuple := flatSamplePrefixTuple hb sample t i
  have hTuple :
      Measurable[samplePrefixSigma hb W sample t i] tuple := by
    refine Measurable.of_comap_le ?_
    change
      MeasurableSpace.comap tuple
          (inferInstance : MeasurableSpace (Fin (flatSampleIndex t i) → β)) ≤
        MeasurableSpace.comap (W t) (inferInstance : MeasurableSpace V) ⊔
          MeasurableSpace.comap tuple
            (inferInstance : MeasurableSpace (Fin (flatSampleIndex t i) → β))
    exact le_sup_right
  let proj : (Fin (flatSampleIndex t i) → β) → β := fun z => z ⟨j, hj⟩
  have hProj : Measurable proj := measurable_pi_apply _
  simpa [flatSample, flatSamplePrefixTuple, tuple, proj] using hProj.comp hTuple

structure Assumption1_UnbiasedFreshBatchSampling
    (Ω Ξ V VDual : Type*)
    [MeasurableSpace Ω]
    [MeasurableSpace Ξ]
    [MeasurableSpace V] [TopologicalSpace V] [BorelSpace V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    [MeasurableSpace VDual] [BorelSpace VDual]
    [SecondCountableTopology VDual] [CompleteSpace VDual]
    (batchSize : ℕ)
    (μ : Measure Ω)
    (W : ℕ → Ω → V)
    (draw : ℕ → Fin batchSize → Ω → Ξ)
    (sample : ℕ → Fin batchSize → Ω → VDual)
    (grad : ℕ → Ω → VDual) where
  batchSize_pos : 0 < batchSize
  sample_measurable :
    ∀ t i, Measurable (sample t i)
  estimator_integrable :
    ∀ t i, Integrable (sample t i) μ
  estimator_condexp_eq_grad :
    ∀ t i,
      μ[sample t i | MeasurableSpace.comap (W t) inferInstance] =ᵐ[μ] grad t
  /--
  The theorem-facing freshness consequence of Assumption 1: after conditioning
  on the current iterate and every previously revealed sample, the next sample
  remains unbiased.
  -/
  estimator_condexp_eq_grad_of_prefix :
    ∀ t i,
      μ[sample t i | samplePrefixSigma batchSize_pos W sample t i] =ᵐ[μ] grad t
  /--
  Mutual independence of the underlying fresh draws across all time/sample
  indices.
  -/
  draw_iIndep :
    iIndepFun
      (fun p : ℕ × Fin batchSize => draw p.1 p.2) μ

/--
Assumption 2: a uniform conditional second-moment bound on the per-sample
noise `ξ_{t,i} := ∇f(W_t) - g_{t,i}`.

The current proof stack does not build a full conditional-independence theory
on top of this structure. Instead, the shared geometry context later packages
the minibatch expected-norm consequence it actually uses downstream.
-/
structure Assumption2_PerSampleGradientNoiseSecondMomentBound
    (Ω V VDual : Type*)
    [MeasurableSpace Ω]
    [MeasurableSpace V] [TopologicalSpace V] [BorelSpace V]
    [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]
    [MeasurableSpace VDual] [BorelSpace VDual]
    [SecondCountableTopology VDual] [CompleteSpace VDual]
    (batchSize : ℕ)
    (μ : Measure Ω)
    (W : ℕ → Ω → V)
    (sample : ℕ → Fin batchSize → Ω → VDual)
    (grad : ℕ → Ω → VDual) where
  sigma : ℝ
  sigma_nonneg : 0 ≤ sigma
  noise_sq_integrable :
    ∀ t i, Integrable (fun ω => ‖grad t ω - sample t i ω‖ ^ 2) μ
  cond_secondMoment_le :
    ∀ t i,
      μ[fun ω => ‖grad t ω - sample t i ω‖ ^ 2 |
          MeasurableSpace.comap (W t) inferInstance] ≤ᵐ[μ] fun _ => sigma ^ 2

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
Local smooth proxy potential on the closed dual ball `‖x‖ ≤ noiseRadius`.

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
Deterministic sample-path geometry for the decoupled weight-decay iteration.

This is the pathwise analytic core reused by the update/geometry, star-convex,
and Frank-Wolfe descent layers. The outer stochastic context later packages a
realized `Ω`-valued process and extracts this deterministic view along each
sample path.
-/
structure SteepestDescentPathGeometryContext
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticSteepestDescentParameters where
  f : V → ℝ
  fGrad : V → StrongDual ℝ V
  fderiv_eq : ∀ X, HasFDerivAt f (fGrad X) X
  pairing : ContinuousDualPairingContext (StrongDual ℝ V) V
  WStar : V
  WStar_optimality : ∀ W, f WStar ≤ f W
  W : ℕ → V
  W0_bound : ‖W 0‖ ≤ 1 / lambda
  minibatchGradient : ℕ → StrongDual ℝ V
  momentum : ℕ → StrongDual ℝ V
  momentum_succ :
    ∀ t,
      momentum (t + 1) =
        beta • momentum t + (1 - beta) • minibatchGradient (t + 1)
  C : ℕ → StrongDual ℝ V
  C_spec :
    ∀ t, C t = beta • momentum t + (1 - beta) • minibatchGradient t
  aStar : ℕ → V
  aStar_spec : ∀ t, IsLMO (C t) (aStar t)
  update_eq :
    ∀ t, W (t + 1) = ((1 - lambda * eta) • W t) + eta • aStar t
  assumption3_fLocalSmoothness : Assumption3_FLocalSmoothness fGrad lambda
  assumption4_localProxyPotential :
    Assumption4_LocalSmoothProxyPotential V (StrongDual ℝ V) pairing

/--
Deterministic path geometry specialized to the star-convex layer.
-/
structure StarConvexPathGeometryContext
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends SteepestDescentPathGeometryContext V where
  WStar_bound : ‖WStar‖ ≤ 1 / lambda
  assumption12_starConvexity :
    Assumption12_StarConvexityAtReferencePoint f WStar

/--
Frank-Wolfe KL assumption along a deterministic iterate sequence.
-/
structure AssumptionFrankWolfeKLAlongIterates
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ)
    (fGrad : V → StrongDual ℝ V)
    (WStar : V)
    (W : ℕ → V)
    (muFW lambda : ℝ) where
  gap_lower_bound :
    ∀ t,
      muFW * (f (W t) - f WStar) ≤
        sSup ((fun V => (fGrad (W t)) (W t - V)) '' Metric.closedBall (0 : V) (1 / lambda))

/--
Deterministic path geometry for the Frank-Wolfe gap layer.
-/
structure FrankWolfePathGeometryContext
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends SteepestDescentPathGeometryContext V

/--
Deterministic path geometry for the Frank-Wolfe expected-suboptimality layer.
-/
structure FrankWolfeKLPathGeometryContext
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends FrankWolfePathGeometryContext V where
  muFW : ℝ
  muFW_pos : 0 < muFW
  assumptionFrankWolfeKL :
    AssumptionFrankWolfeKLAlongIterates V f fGrad WStar W muFW lambda

/--
Common realized stochastic geometry context.

The optimization state is now a genuine `Ω`-valued process. The deterministic
analytic files work sample-pathwise via `S.path ω`, while the stochastic
expected-bound files integrate those pathwise inequalities.

The shared context stores only primitive stochastic/geometry data plus the
Assumptions 1--4 support package. Expected error bounds are derived later in
`MinibatchNoise.lean`, `MomentumBounds.lean`, and
`NesterovMomentumBounds.lean`.
-/
structure StochasticSteepestDescentGeometryContext
    (Ω V : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticSteepestDescentParameters where
  f : V → ℝ
  fGrad : V → StrongDual ℝ V
  fderiv_eq : ∀ X, HasFDerivAt f (fGrad X) X
  pairing : ContinuousDualPairingContext (StrongDual ℝ V) V
  W0 : V
  W0_bound : ‖W0‖ ≤ 1 / lambda
  W : ℕ → Ω → V
  W_zero : ∀ ω, W 0 ω = W0
  WStar : V
  WStar_optimality : ∀ W, f WStar ≤ f W

  -- Sampling/oracle data.
  Ξ : Type*
  sampleMeasurableSpace : MeasurableSpace Ξ
  drawProcess : PerSampleDrawProcess Ω Ξ batchSize sampleMeasurableSpace
  stochasticGradientOracle :
    StochasticGradientOracle V Ξ (StrongDual ℝ V) sampleMeasurableSpace
  stochasticGradientSample :
    ℕ → Fin batchSize → Ω → StrongDual ℝ V
  stochasticGradientSample_spec :
    ∀ t i ω,
      stochasticGradientSample t i ω =
        stochasticGradientOracle.g (W t ω) (drawProcess.draw t i ω)
  minibatchGradient :
    ℕ → Ω → StrongDual ℝ V
  minibatchGradient_spec :
    ∀ t ω,
      minibatchGradient t ω =
        Finset.sum Finset.univ
          (fun i : Fin batchSize =>
            uniformBatchWeight batchSize • stochasticGradientSample t i ω)

  -- Momentum / search dynamics driven by the realized minibatch gradient.
  momentum : ℕ → Ω → StrongDual ℝ V
  momentum_zero_eq_zero_or_minibatchGradient :
    (∀ ω, momentum 0 ω = 0) ∨ (∀ ω, momentum 0 ω = minibatchGradient 0 ω)
  momentum_succ :
    ∀ t ω,
      momentum (t + 1) ω =
        beta • momentum t ω + (1 - beta) • minibatchGradient (t + 1) ω
  lmo : StrongDual ℝ V → V
  lmo_measurable : Measurable lmo
  lmo_spec : ∀ x, IsLMO x (lmo x)
  update_eq :
    ∀ t ω,
      W (t + 1) ω =
        ((1 - lambda * eta) • W t ω) +
          eta • lmo (beta • momentum t ω + (1 - beta) • minibatchGradient t ω)

  -- Assumptions 1--4.
  assumption1_sampling :
    Assumption1_UnbiasedFreshBatchSampling
      Ω Ξ V (StrongDual ℝ V) batchSize drawProcess.μ
      W drawProcess.draw stochasticGradientSample (fun t ω => fGrad (W t ω))
  assumption2_secondMoment :
    Assumption2_PerSampleGradientNoiseSecondMomentBound
      Ω V (StrongDual ℝ V) batchSize drawProcess.μ
      W stochasticGradientSample (fun t ω => fGrad (W t ω))
  assumption3_fLocalSmoothness :
    Assumption3_FLocalSmoothness fGrad lambda
  assumption4_localProxyPotential :
    Assumption4_LocalSmoothProxyPotential V (StrongDual ℝ V) pairing
  oracle_sample_norm_le_noiseRadius_ae :
    ∀ t i, ∀ᵐ ω ∂drawProcess.μ,
      ‖fGrad (W t ω) - stochasticGradientSample t i ω‖ ≤
        assumption4_localProxyPotential.noiseRadius

/--
Realized stochastic geometry specialized to the star-convex layer.
-/
structure StochasticStarConvexGeometryContext
    (Ω V : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticSteepestDescentGeometryContext Ω V where
  WStar_bound : ‖WStar‖ ≤ 1 / lambda
  assumption12_starConvexity :
    Assumption12_StarConvexityAtReferencePoint f WStar

/--
Realized stochastic geometry for the Frank-Wolfe gap layer.
-/
structure StochasticFrankWolfeGeometryContext
    (Ω V : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticSteepestDescentGeometryContext Ω V where
  frankWolfeGap_integrable :
    ∀ t,
      Integrable
        (fun ω =>
          sSup
            ((fun V => (fGrad (W t ω)) (W t ω - V)) ''
              Metric.closedBall (0 : V) (1 / lambda)))
        drawProcess.μ

/--
Realized stochastic geometry for the Frank-Wolfe expected-suboptimality layer.
-/
structure StochasticFrankWolfeKLGeometryContext
    (Ω V : Type*)
    [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]
    extends StochasticFrankWolfeGeometryContext Ω V where
  muFW : ℝ
  muFW_pos : 0 < muFW
  assumptionFrankWolfeKL :
    ∀ t ω,
      muFW * (f (W t ω) - f WStar) ≤
        sSup ((fun V => (fGrad (W t ω)) (W t ω - V)) '' Metric.closedBall (0 : V) (1 / lambda))

attribute [instance] StochasticSteepestDescentGeometryContext.sampleMeasurableSpace

namespace SteepestDescentPathGeometryContext

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The true gradient along a deterministic sample path. -/
def grad (S : SteepestDescentPathGeometryContext V) (t : ℕ) : StrongDual ℝ V :=
  S.fGrad (S.W t)

/-- The Assumption-4 proxy potential `g` on a deterministic path. -/
def potential (S : SteepestDescentPathGeometryContext V) :
    StrongDual ℝ V → ℝ :=
  S.assumption4_localProxyPotential.potential

/-- The Assumption-4 mirror map `Φ` on a deterministic path. -/
def mirrorMap (S : SteepestDescentPathGeometryContext V) :
    StrongDual ℝ V → V :=
  S.assumption4_localProxyPotential.mirrorMap

/-- The Assumption-4 smoothness constant on a deterministic path. -/
def D (S : SteepestDescentPathGeometryContext V) : ℝ :=
  S.assumption4_localProxyPotential.D

/-- The Assumption-4 noise support radius on a deterministic path. -/
def noiseRadius (S : SteepestDescentPathGeometryContext V) : ℝ :=
  S.assumption4_localProxyPotential.noiseRadius

/-- The Assumption-3 local smoothness constant on a deterministic path. -/
def L (S : SteepestDescentPathGeometryContext V) : ℝ :=
  S.assumption3_fLocalSmoothness.L

lemma L_pos (S : SteepestDescentPathGeometryContext V) : 0 < S.L :=
  S.assumption3_fLocalSmoothness.pos

lemma D_nonneg (S : SteepestDescentPathGeometryContext V) : 0 ≤ S.D :=
  S.assumption4_localProxyPotential.D_nonneg

lemma noiseRadius_nonneg (S : SteepestDescentPathGeometryContext V) :
    0 ≤ S.noiseRadius :=
  S.assumption4_localProxyPotential.noiseRadius_nonneg

lemma potential_zero (S : SteepestDescentPathGeometryContext V) :
    S.potential 0 = 0 :=
  S.assumption4_localProxyPotential.potential_zero

lemma mirrorMap_zero (S : SteepestDescentPathGeometryContext V) :
    S.mirrorMap 0 = 0 :=
  S.assumption4_localProxyPotential.mirrorMap_zero

lemma potential_fderiv_eq (S : SteepestDescentPathGeometryContext V) :
    ∀ x,
      HasFDerivAt S.potential
        (S.pairing.toLinear (S.mirrorMap x)) x :=
  S.assumption4_localProxyPotential.potential_fderiv_eq

lemma potential_continuous (S : SteepestDescentPathGeometryContext V) :
    Continuous S.potential :=
  S.assumption4_localProxyPotential.potential_continuous

lemma mirrorMap_continuous (S : SteepestDescentPathGeometryContext V) :
    Continuous S.mirrorMap :=
  S.assumption4_localProxyPotential.mirrorMap_continuous

lemma norm_sq_le_two_potential_of_mem_noiseRadius
    (S : SteepestDescentPathGeometryContext V) (x : StrongDual ℝ V)
    (hx : ‖x‖ ≤ S.noiseRadius) :
    ‖x‖ ^ 2 ≤ 2 * S.potential x :=
  S.assumption4_localProxyPotential.norm_sq_le_two_potential_on_ball x hx

/-- The pathwise suboptimality gap. -/
def suboptimality (S : SteepestDescentPathGeometryContext V) (t : ℕ) : ℝ :=
  S.f (S.W t) - S.f S.WStar

end SteepestDescentPathGeometryContext

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- The probability measure carried by the realized sample process. -/
def μ (S : StochasticSteepestDescentGeometryContext Ω V) : Measure Ω :=
  S.drawProcess.μ

/-- The probability witness carried by the realized sample process. -/
def prob (S : StochasticSteepestDescentGeometryContext Ω V) : IsProbabilityMeasure S.μ :=
  S.drawProcess.prob

/-- The sigma-algebra generated by the current iterate `W_t`. -/
def iterateSigma (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (S.W t) inferInstance

/-- The true gradient process `∇f(W_t(ω))`. -/
def grad (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  S.fGrad (S.W t ω)

/-- The Nesterov search direction process `C_t = β m_t + (1 - β) g_t`. -/
def C (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) :
    StrongDual ℝ V :=
  S.beta • S.momentum t ω + (1 - S.beta) • S.minibatchGradient t ω

/-- The search direction process satisfies the defining Nesterov recursion. -/
lemma C_spec
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω,
      S.C t ω = S.beta • S.momentum t ω + (1 - S.beta) • S.minibatchGradient t ω := by
  intro t ω
  rfl

/-- The realized linear minimization oracle output. -/
def aStar (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : V :=
  S.lmo (S.C t ω)

/-- The realized linear minimization oracle satisfies the LMO condition pointwise. -/
lemma aStar_spec
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω, IsLMO (S.C t ω) (S.aStar t ω) := by
  intro t ω
  exact S.lmo_spec (S.C t ω)

/-- The realized per-sample gradient noise. -/
def ξ (S : StochasticSteepestDescentGeometryContext Ω V) :
    ℕ → Fin S.batchSize → Ω → StrongDual ℝ V :=
  fun t i ω => S.grad t ω - S.stochasticGradientSample t i ω

/-- The Assumption-2 noise scale. -/
def sigma (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.assumption2_secondMoment.sigma

lemma sigma_nonneg (S : StochasticSteepestDescentGeometryContext Ω V) : 0 ≤ S.sigma :=
  S.assumption2_secondMoment.sigma_nonneg

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

/-- The stochastic suboptimality gap along a realized sample path. -/
def suboptimality (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) (ω : Ω) : ℝ :=
  S.f (S.W t ω) - S.f S.WStar

/-- The deterministic initial suboptimality gap `f(W_0) - f(W_*)`. -/
def initialSuboptimality (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.f S.W0 - S.f S.WStar

/-- The expected suboptimality gap `E[f(W_t) - f(W_*)]`. -/
def expectedSuboptimality (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ) : ℝ :=
  ∫ ω, S.suboptimality t ω ∂S.μ

/-- The expected initial suboptimality `E[f(W_0) - f(W_*)]`. -/
def initialExpectedSuboptimality (S : StochasticSteepestDescentGeometryContext Ω V) : ℝ :=
  S.expectedSuboptimality 0

/-- The expected initial suboptimality equals the deterministic initial gap. -/
theorem initialExpectedSuboptimality_eq_initialSuboptimality
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    S.initialExpectedSuboptimality = S.initialSuboptimality := by
  letI := S.prob
  simp [initialExpectedSuboptimality, expectedSuboptimality, initialSuboptimality, suboptimality, S.W_zero]

/-- Deterministic sample-path view used by the analytic files. -/
def path (S : StochasticSteepestDescentGeometryContext Ω V) (ω : Ω) :
    SteepestDescentPathGeometryContext V where
  toStochasticSteepestDescentParameters := S.toStochasticSteepestDescentParameters
  f := S.f
  fGrad := S.fGrad
  fderiv_eq := S.fderiv_eq
  pairing := S.pairing
  WStar := S.WStar
  WStar_optimality := S.WStar_optimality
  W := fun t => S.W t ω
  W0_bound := by
    rw [S.W_zero ω]
    exact S.W0_bound
  minibatchGradient := fun t => S.minibatchGradient t ω
  momentum := fun t => S.momentum t ω
  momentum_succ := by
    intro t
    exact S.momentum_succ t ω
  C := fun t => S.C t ω
  C_spec := by
    intro t
    exact S.C_spec t ω
  aStar := fun t => S.aStar t ω
  aStar_spec := by
    intro t
    exact S.aStar_spec t ω
  update_eq := by
    intro t
    simpa using S.update_eq t ω
  assumption3_fLocalSmoothness := S.assumption3_fLocalSmoothness
  assumption4_localProxyPotential := S.assumption4_localProxyPotential

end StochasticSteepestDescentGeometryContext

namespace StochasticStarConvexGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Shared initial suboptimality exposed with star-convex dot notation. -/
abbrev initialSuboptimality (S : StochasticStarConvexGeometryContext Ω V) : ℝ :=
  S.toStochasticSteepestDescentGeometryContext.initialSuboptimality

/-- Shared expected suboptimality exposed with star-convex dot notation. -/
abbrev expectedSuboptimality (S : StochasticStarConvexGeometryContext Ω V) (t : ℕ) : ℝ :=
  S.toStochasticSteepestDescentGeometryContext.expectedSuboptimality t

/-- Star-convex deterministic sample-path view. -/
def path (S : StochasticStarConvexGeometryContext Ω V) (ω : Ω) :
    StarConvexPathGeometryContext V where
  toSteepestDescentPathGeometryContext :=
    S.toStochasticSteepestDescentGeometryContext.path ω
  WStar_bound := S.WStar_bound
  assumption12_starConvexity := S.assumption12_starConvexity

end StochasticStarConvexGeometryContext

namespace StochasticFrankWolfeGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Shared initial suboptimality exposed with Frank-Wolfe-gap dot notation. -/
abbrev initialSuboptimality (S : StochasticFrankWolfeGeometryContext Ω V) : ℝ :=
  S.toStochasticSteepestDescentGeometryContext.initialSuboptimality

/-- Shared expected suboptimality exposed with Frank-Wolfe-gap dot notation. -/
abbrev expectedSuboptimality (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) : ℝ :=
  S.toStochasticSteepestDescentGeometryContext.expectedSuboptimality t

/-- Frank-Wolfe deterministic sample-path view. -/
def path (S : StochasticFrankWolfeGeometryContext Ω V) (ω : Ω) :
    FrankWolfePathGeometryContext V where
  toSteepestDescentPathGeometryContext :=
    S.toStochasticSteepestDescentGeometryContext.path ω

end StochasticFrankWolfeGeometryContext

namespace StochasticFrankWolfeKLGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-- Shared initial suboptimality exposed with FW-KL dot notation. -/
abbrev initialSuboptimality (S : StochasticFrankWolfeKLGeometryContext Ω V) : ℝ :=
  S.toStochasticFrankWolfeGeometryContext.initialSuboptimality

/-- Shared expected suboptimality exposed with FW-KL dot notation. -/
abbrev expectedSuboptimality (S : StochasticFrankWolfeKLGeometryContext Ω V) (t : ℕ) : ℝ :=
  S.toStochasticFrankWolfeGeometryContext.expectedSuboptimality t

/-- Frank-Wolfe-KL deterministic sample-path view. -/
def path (S : StochasticFrankWolfeKLGeometryContext Ω V) (ω : Ω) :
    FrankWolfeKLPathGeometryContext V where
  toFrankWolfePathGeometryContext :=
    S.toStochasticFrankWolfeGeometryContext.path ω
  muFW := S.muFW
  muFW_pos := S.muFW_pos
  assumptionFrankWolfeKL := {
    gap_lower_bound := by
      intro t
      simpa using S.assumptionFrankWolfeKL t ω
  }

end StochasticFrankWolfeKLGeometryContext

end

end SteepestDescentOptimizationBounds
