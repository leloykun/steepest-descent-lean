import Mathlib
import SteepestDescentOptimizationBounds.Assumptions
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds

namespace SteepestDescentOptimizationBounds

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-!
Stochastic process support layer for the realized stochastic steepest-descent model.

Upstream dependencies:

- `Assumptions.lean` provides the stochastic geometry context, the primitive
  stochastic processes, and Assumptions 1--4.

Downstream use:

- `MinibatchNoise.lean` reuses the conditional-expectation and second-moment
  lemmas for the minibatch-noise process.
- `MomentumBounds.lean` reuses the measurability, integrability, and adaptedness
  lemmas for the momentum recursion.
- downstream expected-bound files use the iterate measurability and gradient
  integrability results.
-/

namespace StochasticSteepestDescentGeometryContext

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

section PrivateLemmas

/-- Restricting the codomain to a measurable set lets us compose a
`Measurable` map into that set with a measurable restricted target map. -/
private lemma measurable_comp_of_measurable_restrict
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {s : Set β} {f : α → β} {g : β → γ}
    (hf : Measurable f) (hfs : ∀ x, f x ∈ s)
    (hg : Measurable (s.restrict g)) :
    Measurable (fun x => g (f x)) := by
  have hcod : Measurable (s.codRestrict f hfs) := hf.subtype_mk
  simpa [Function.comp_def, Set.restrict_comp_codRestrict hfs] using hg.comp hcod

/-- The primal closed ball on which Assumption 3 controls the gradient map. -/
private def primalClosedBall
    (S : StochasticSteepestDescentGeometryContext Ω V) : Set V :=
  Metric.closedBall (0 : V) (1 / S.lambda)

/-- Assumption 3 gives a Lipschitz gradient map on the primal feasibility ball. -/
private lemma fGrad_lipschitzOn_primalClosedBall
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    LipschitzOnWith (Real.toNNReal S.L) S.fGrad S.primalClosedBall := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hx' : ‖x‖ ≤ 1 / S.lambda := by
    simpa [primalClosedBall, Metric.mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y‖ ≤ 1 / S.lambda := by
    simpa [primalClosedBall, Metric.mem_closedBall, dist_eq_norm] using hy
  have hBound := S.assumption3_fLocalSmoothness.bound hx' hy'
  simpa [dist_eq_norm, norm_sub_rev, Real.toNNReal_of_nonneg S.L_pos.le] using hBound

/-- The gradient map restricted to the primal feasibility ball is measurable. -/
private lemma fGrad_restrict_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    Measurable (S.primalClosedBall.restrict S.fGrad) := by
  exact
    (continuousOn_iff_continuous_restrict.1
      (S.fGrad_lipschitzOn_primalClosedBall.continuousOn)).measurable

/-- Every realized iterate stays inside the Assumption-3 primal ball. -/
private lemma W_mem_primalClosedBall
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t ω, S.W t ω ∈ S.primalClosedBall := by
  intro t ω
  simpa [primalClosedBall, Metric.mem_closedBall, dist_eq_norm] using
    S.weight_bound_from_feasible_step t ω

/-- Internal measurability proof for the realized minibatch gradient. -/
private lemma minibatchGradient_measurable_internal
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.minibatchGradient t) := by
  intro t
  have hEq :
      S.minibatchGradient t =
        fun ω =>
          Finset.sum Finset.univ
            (fun i : Fin S.batchSize =>
              uniformBatchWeight S.batchSize • S.stochasticGradientSample t i ω) := by
    funext ω
    exact S.minibatchGradient_spec t ω
  rw [hEq]
  exact Finset.measurable_fun_sum Finset.univ fun i _ =>
    (S.assumption1_sampling.sample_measurable t i).const_smul
      (uniformBatchWeight S.batchSize)

/-- Internal measurability proof for the initialized momentum process. -/
private lemma momentum_zero_measurable_internal
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    Measurable (S.momentum 0) := by
  rcases S.momentum_zero_eq_zero_or_minibatchGradient with hZero | hBatch
  · have hEq : S.momentum 0 = fun _ : Ω => (0 : StrongDual ℝ V) := by
      funext ω
      simp [hZero ω]
    rw [hEq]
    exact measurable_const
  · have hEq : S.momentum 0 = S.minibatchGradient 0 := by
      funext ω
      exact hBatch ω
    rw [hEq]
    exact S.minibatchGradient_measurable_internal 0

/-- Internal measurability proof for the momentum recursion. -/
private lemma momentum_measurable_internal
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.momentum t) := by
  intro t
  induction t with
  | zero =>
      simpa using S.momentum_zero_measurable_internal
  | succ t ih =>
      have hEq :
          S.momentum (t + 1) =
            fun ω =>
              S.beta • S.momentum t ω + (1 - S.beta) • S.minibatchGradient (t + 1) ω := by
        funext ω
        simpa using S.momentum_succ t ω
      rw [hEq]
      exact (ih.const_smul S.beta).add
        ((S.minibatchGradient_measurable_internal (t + 1)).const_smul (1 - S.beta))

private theorem flatSampleIndex_lt_of_lt_time
    (S : StochasticSteepestDescentGeometryContext Ω V)
    {s t : ℕ} (hst : s < t) (j : Fin S.batchSize) (i : Fin S.batchSize) :
    flatSampleIndex s j < flatSampleIndex t i := by
  calc
    flatSampleIndex s j = s * S.batchSize + j.1 := rfl
    _ < s * S.batchSize + S.batchSize := by
          exact Nat.add_lt_add_left j.2 _
    _ = (s + 1) * S.batchSize := by rw [Nat.succ_mul]
    _ ≤ t * S.batchSize := by
          exact Nat.mul_le_mul_right S.batchSize (Nat.succ_le_of_lt hst)
    _ ≤ t * S.batchSize + i.1 := Nat.le_add_right _ _
    _ = flatSampleIndex t i := rfl

private theorem sample_prefixMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) {s : ℕ}
    (hs : s < t) (j : Fin S.batchSize) :
    Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.stochasticGradientSample s j) := by
  have hlt : flatSampleIndex s j < flatSampleIndex t i :=
    S.flatSampleIndex_lt_of_lt_time hs j i
  have hFlat :
      Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        (flatSample S.batchSize_pos S.stochasticGradientSample (flatSampleIndex s j)) := by
    exact flatSample_measurable_of_lt
      S.batchSize_pos S.W S.stochasticGradientSample (t := t) (i := i) hlt
  simpa [flatSample_at_flatSampleIndex S.batchSize_pos S.stochasticGradientSample s j] using hFlat

private theorem minibatchGradient_prefixStronglyMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) {s : ℕ}
    (hs : s < t) :
    StronglyMeasurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.minibatchGradient s) := by
  have hEq :
      S.minibatchGradient s =
        fun ω =>
          Finset.sum Finset.univ
            (fun j : Fin S.batchSize =>
              uniformBatchWeight S.batchSize • S.stochasticGradientSample s j ω) := by
    funext ω
    exact S.minibatchGradient_spec s ω
  rw [hEq]
  have hMeas :
      Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        (fun ω =>
          Finset.sum Finset.univ
            (fun j : Fin S.batchSize =>
              uniformBatchWeight S.batchSize • S.stochasticGradientSample s j ω)) := by
    exact Finset.measurable_fun_sum Finset.univ fun j _ =>
      (S.sample_prefixMeasurable_before t i hs j).const_smul
        (uniformBatchWeight S.batchSize)
  exact hMeas.stronglyMeasurable

private theorem momentum_prefixStronglyMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s < t) :
    StronglyMeasurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.momentum s) := by
  revert hs
  induction s with
  | zero =>
      intro hs
      rcases S.momentum_zero_eq_zero_or_minibatchGradient with hZero | hBatch
      · have hEq : S.momentum 0 = fun _ : Ω => (0 : StrongDual ℝ V) := by
          funext ω
          simp [hZero ω]
        rw [hEq]
        exact stronglyMeasurable_const
      · have hEq : S.momentum 0 = S.minibatchGradient 0 := by
          funext ω
          exact hBatch ω
        rw [hEq]
        exact S.minibatchGradient_prefixStronglyMeasurable_before t i hs
  | succ s ih =>
      intro hs
      have hs' : s < t := Nat.lt_trans (Nat.lt_succ_self s) hs
      have hEq :
          S.momentum (s + 1) =
            fun ω =>
              S.beta • S.momentum s ω + (1 - S.beta) • S.minibatchGradient (s + 1) ω := by
        funext ω
        simpa using S.momentum_succ s ω
      rw [hEq]
      exact (ih hs').const_smul S.beta |>.add
        ((S.minibatchGradient_prefixStronglyMeasurable_before t i hs).const_smul
          (1 - S.beta))

private theorem C_prefixStronglyMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s < t) :
    StronglyMeasurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.C s) := by
  simpa [StochasticSteepestDescentGeometryContext.C] using
    ((S.momentum_prefixStronglyMeasurable_before t i s hs).const_smul S.beta).add
      ((S.minibatchGradient_prefixStronglyMeasurable_before t i hs).const_smul (1 - S.beta))

private theorem aStar_prefixStronglyMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s < t) :
    StronglyMeasurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.aStar s) := by
  have hMeas :
      Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        (S.aStar s) := by
    simpa [StochasticSteepestDescentGeometryContext.aStar] using
      S.lmo_measurable.comp (S.C_prefixStronglyMeasurable_before t i s hs).measurable
  exact hMeas.stronglyMeasurable

private theorem W_prefixMeasurable_before
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s < t) :
    Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.W s) := by
  revert hs
  induction s with
  | zero =>
      intro hs
      have hEq : S.W 0 = fun _ : Ω => S.W0 := by
        funext ω
        simpa using S.W_zero ω
      rw [hEq]
      exact measurable_const
  | succ s ih =>
      intro hs
      have hs' : s < t := Nat.lt_trans (Nat.lt_succ_self s) hs
      have hEq :
          S.W (s + 1) =
            fun ω => ((1 - S.lambda * S.eta) • S.W s ω) + S.eta • S.aStar s ω := by
        funext ω
        simpa [StochasticSteepestDescentGeometryContext.aStar,
          StochasticSteepestDescentGeometryContext.C] using S.update_eq s ω
      rw [hEq]
      exact (ih hs').const_smul (1 - S.lambda * S.eta) |>.add
        ((S.aStar_prefixStronglyMeasurable_before t i s hs').measurable.const_smul S.eta)

end PrivateLemmas

section PublicTheorems

/-- The realized minibatch gradient is measurable at each time. -/
lemma minibatchGradient_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.minibatchGradient t) := by
  exact S.minibatchGradient_measurable_internal

/-- The Nesterov search direction is measurable at each time. -/
lemma C_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.C t) := by
  intro t
  simpa [StochasticSteepestDescentGeometryContext.C] using
    ((S.momentum_measurable_internal t).const_smul S.beta).add
      ((S.minibatchGradient_measurable t).const_smul (1 - S.beta))

/-- The realized linear minimization oracle is measurable at each time. -/
lemma aStar_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.aStar t) := by
  intro t
  simpa [StochasticSteepestDescentGeometryContext.aStar] using
    S.lmo_measurable.comp (S.C_measurable t)

/-- The iterate process is measurable at each time. -/
lemma W_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.W t) := by
  intro t
  induction t with
  | zero =>
      have hEq : S.W 0 = fun _ : Ω => S.W0 := by
        funext ω
        simpa using S.W_zero ω
      rw [hEq]
      exact measurable_const
  | succ t ih =>
      have hEq :
          S.W (t + 1) =
            fun ω => ((1 - S.lambda * S.eta) • S.W t ω) + S.eta • S.aStar t ω := by
        funext ω
        simpa [StochasticSteepestDescentGeometryContext.aStar,
          StochasticSteepestDescentGeometryContext.C] using S.update_eq t ω
      rw [hEq]
      exact (ih.const_smul (1 - S.lambda * S.eta)).add
        ((S.aStar_measurable t).const_smul S.eta)

/-- The true gradient process is measurable at each time. -/
lemma grad_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Measurable (S.grad t) := by
  intro t
  exact measurable_comp_of_measurable_restrict
    (f := S.W t) (g := S.fGrad) (s := S.primalClosedBall)
    (S.W_measurable t) (S.W_mem_primalClosedBall t) S.fGrad_restrict_measurable

/-- The true gradient process is strongly measurable at each time. -/
lemma grad_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, StronglyMeasurable (S.grad t) := by
  intro t
  exact (S.grad_measurable t).stronglyMeasurable

/-- The current iterate is measurable with respect to its prefix filtration. -/
lemma current_iterate_prefixMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ)
    (i : Fin S.batchSize) :
    Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i] (S.W t) := by
  refine Measurable.of_comap_le ?_
  unfold samplePrefixSigma
  exact le_sup_left

/-- Every prefix filtration is a sub-sigma-algebra of the ambient measurable space. -/
lemma samplePrefixSigma_le
    (S : StochasticSteepestDescentGeometryContext Ω V) (t : ℕ)
    (i : Fin S.batchSize) :
    samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i ≤
      inferInstanceAs (MeasurableSpace Ω) := by
  exact samplePrefixSigma_le_of_measurable
    S.batchSize_pos S.W S.stochasticGradientSample
    S.assumption1_sampling.sample_measurable t (S.W_measurable t) i

/-- Earlier iterates are measurable with respect to any later prefix filtration. -/
lemma W_prefixMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s ≤ t) :
    Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (S.W s) := by
  by_cases hEq : s = t
  · subst hEq
    simpa using S.current_iterate_prefixMeasurable s i
  · exact S.W_prefixMeasurable_before t i s (lt_of_le_of_ne hs hEq)

/--
Earlier true gradients are strongly measurable with respect to any later prefix
filtration.
-/
lemma grad_prefixStronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V)
    (t : ℕ) (i : Fin S.batchSize) (s : ℕ)
    (hs : s ≤ t) :
    StronglyMeasurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      (fun ω => S.fGrad (S.W s ω)) := by
  have hWcod :
      Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        (S.primalClosedBall.codRestrict (S.W s) (S.W_mem_primalClosedBall s)) := by
    exact Measurable.subtype_mk (S.W_prefixMeasurable t i s hs)
  have hGrad :
      Measurable[samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        (fun ω => S.fGrad (S.W s ω)) := by
    simpa [Function.comp_def, Set.restrict_comp_codRestrict (S.W_mem_primalClosedBall s)] using
      S.fGrad_restrict_measurable.comp hWcod
  exact hGrad.stronglyMeasurable

/-- The realized stochastic-gradient samples are integrable. -/
lemma sample_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, Integrable (S.stochasticGradientSample t i) S.μ :=
  S.assumption1_sampling.estimator_integrable

/-- The realized stochastic-gradient samples are measurable. -/
lemma sample_measurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, Measurable (S.stochasticGradientSample t i) :=
  S.assumption1_sampling.sample_measurable

/-- The realized stochastic-gradient samples are strongly measurable. -/
lemma sample_stronglyMeasurable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, StronglyMeasurable (S.stochasticGradientSample t i) := by
  intro t i
  exact (S.sample_measurable t i).stronglyMeasurable

/-- Assumption 1 rewritten as a conditional-expectation identity on `iterateSigma`. -/
lemma sample_condexp_eq_grad
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, S.μ[S.stochasticGradientSample t i | S.iterateSigma t] =ᵐ[S.μ] S.grad t := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.iterateSigma,
    StochasticSteepestDescentGeometryContext.grad] using
    S.assumption1_sampling.estimator_condexp_eq_grad t i

/-- Assumption 1 rewritten on the refined prefix filtration. -/
lemma sample_condexp_eq_grad_of_prefix
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t (i : Fin S.batchSize),
      S.μ[S.stochasticGradientSample t i |
          samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        =ᵐ[S.μ] S.grad t := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.grad] using
    S.assumption1_sampling.estimator_condexp_eq_grad_of_prefix t i

/-- The true gradient process is integrable at each time. -/
lemma grad_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t, Integrable (S.grad t) S.μ := by
  intro t
  let i : Fin S.batchSize := ⟨0, S.batchSize_pos⟩
  have hCondInt :
      Integrable
        (S.μ[S.stochasticGradientSample t i | S.iterateSigma t]) S.μ := by
    simpa using
      (MeasureTheory.integrable_condExp
        (m := S.iterateSigma t)
        (μ := S.μ)
        (f := S.stochasticGradientSample t i))
  exact hCondInt.congr (by simpa using (S.sample_condexp_eq_grad t i))

/-- The refined per-sample noises have zero conditional expectation on the prefix filtration. -/
lemma ξ_condexp_eq_zero_of_prefix
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t (i : Fin S.batchSize),
      S.μ[S.ξ t i |
          samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
        =ᵐ[S.μ] 0 := by
  intro t i
  have hPrefixLe :
      samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i ≤
        inferInstanceAs (MeasurableSpace Ω) :=
    S.samplePrefixSigma_le t i
  letI := S.prob
  letI : IsFiniteMeasure S.μ := by
    refine ⟨by simp⟩
  letI : SigmaFinite (S.μ.trim hPrefixLe) := by infer_instance
  have hGradInt : Integrable (S.grad t) S.μ := S.grad_integrable t
  have hSampleInt : Integrable (S.stochasticGradientSample t i) S.μ := S.sample_integrable t i
  have hSub :=
    MeasureTheory.condExp_sub
      (μ := S.μ)
      (m := samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i)
      hGradInt hSampleInt
  calc
    S.μ[S.ξ t i | samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
      =ᵐ[S.μ]
        S.μ[S.grad t | samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i]
          - S.μ[S.stochasticGradientSample t i |
              samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i] := by
            simpa [StochasticSteepestDescentGeometryContext.ξ, Pi.sub_apply] using hSub
    _ =ᵐ[S.μ]
        S.grad t
          - S.μ[S.stochasticGradientSample t i |
              samplePrefixSigma S.batchSize_pos S.W S.stochasticGradientSample t i] := by
            refine Filter.EventuallyEq.sub ?_ Filter.EventuallyEq.rfl
            simpa using
              (Filter.EventuallyEq.of_eq
                (MeasureTheory.condExp_of_stronglyMeasurable
                  hPrefixLe
                  (S.grad_prefixStronglyMeasurable t i t le_rfl)
                  hGradInt))
    _ =ᵐ[S.μ] 0 := by
            filter_upwards [S.sample_condexp_eq_grad_of_prefix t i] with ω hω
            simp [hω]

/-- The per-sample noise second moment is integrable. -/
lemma second_moment_integrable
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, Integrable (fun ω => ‖S.ξ t i ω‖ ^ 2) S.μ := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.grad] using
    S.assumption2_secondMoment.noise_sq_integrable t i

/-- The conditional second moment of the per-sample noise is uniformly bounded. -/
lemma sample_cond_secondMoment_le
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i,
      S.μ[fun ω => ‖S.ξ t i ω‖ ^ 2 | S.iterateSigma t] ≤ᵐ[S.μ]
        fun _ => S.sigma ^ 2 := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.iterateSigma,
    StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.grad,
    StochasticSteepestDescentGeometryContext.sigma] using
    S.assumption2_secondMoment.cond_secondMoment_le t i

/-- Uniform second-moment bound for the per-sample gradient noise. -/
lemma second_moment_bound
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i,
      Integrable (fun ω => ‖S.ξ t i ω‖ ^ 2) S.μ ∧
        ∫ ω, ‖S.ξ t i ω‖ ^ 2 ∂S.μ ≤ S.sigma ^ 2 := by
  intro t i
  constructor
  · exact S.second_moment_integrable t i
  · have hCondInt :
        Integrable
          (S.μ[fun ω => ‖S.ξ t i ω‖ ^ 2 | S.iterateSigma t]) S.μ := by
      simpa using
        (MeasureTheory.integrable_condExp
          (m := S.iterateSigma t)
          (μ := S.μ)
          (f := fun ω => ‖S.ξ t i ω‖ ^ 2))
    letI := S.prob
    have hConst :
        Integrable (fun _ : Ω => S.sigma ^ 2) S.μ :=
      MeasureTheory.integrable_const _
    have hMono :
        ∫ ω, S.μ[fun ω => ‖S.ξ t i ω‖ ^ 2 | S.iterateSigma t] ω ∂S.μ ≤
          ∫ ω, S.sigma ^ 2 ∂S.μ := by
      exact
        MeasureTheory.integral_mono_ae hCondInt hConst
          (S.sample_cond_secondMoment_le t i)
    have hIterateSigma :
        S.iterateSigma t ≤ inferInstanceAs (MeasurableSpace Ω) := by
      simpa [StochasticSteepestDescentGeometryContext.iterateSigma] using
        (S.W_measurable t).comap_le
    calc
      ∫ ω, ‖S.ξ t i ω‖ ^ 2 ∂S.μ
        = ∫ ω, S.μ[fun ω => ‖S.ξ t i ω‖ ^ 2 | S.iterateSigma t] ω ∂S.μ := by
            symm
            exact
              MeasureTheory.integral_condExp
                (m := S.iterateSigma t)
                (μ := S.μ)
                (f := fun ω => ‖S.ξ t i ω‖ ^ 2)
                hIterateSigma
      _ ≤ ∫ ω, S.sigma ^ 2 ∂S.μ := hMono
      _ = S.sigma ^ 2 := by simp

/-- The per-sample gradient noise has zero mean. -/
lemma sample_mean_zero
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, ∫ ω, S.ξ t i ω ∂S.μ = 0 := by
  intro t i
  have hGradInt : Integrable (S.grad t) S.μ := S.grad_integrable t
  have hSampleInt : Integrable (S.stochasticGradientSample t i) S.μ := S.sample_integrable t i
  have hEq :
      ∫ ω, S.grad t ω ∂S.μ = ∫ ω, S.stochasticGradientSample t i ω ∂S.μ := by
    letI := S.prob
    have hIterateSigma :
        S.iterateSigma t ≤ inferInstanceAs (MeasurableSpace Ω) := by
      simpa [StochasticSteepestDescentGeometryContext.iterateSigma] using
        (S.W_measurable t).comap_le
    calc
      ∫ ω, S.grad t ω ∂S.μ
        = ∫ ω, S.μ[S.stochasticGradientSample t i | S.iterateSigma t] ω ∂S.μ := by
            refine integral_congr_ae ?_
            simpa using (S.sample_condexp_eq_grad t i).symm
      _ = ∫ ω, S.stochasticGradientSample t i ω ∂S.μ := by
            exact
              MeasureTheory.integral_condExp
                (m := S.iterateSigma t)
                (μ := S.μ)
                (f := S.stochasticGradientSample t i)
                hIterateSigma
  calc
    ∫ ω, S.ξ t i ω ∂S.μ
      = ∫ ω, S.grad t ω ∂S.μ - ∫ ω, S.stochasticGradientSample t i ω ∂S.μ := by
          simp [StochasticSteepestDescentGeometryContext.ξ,
            MeasureTheory.integral_sub hGradInt hSampleInt]
    _ = 0 := sub_eq_zero.mpr hEq

/-- The refined per-sample noise is almost surely supported in the Assumption-4 radius. -/
lemma sample_norm_le_noiseRadius_ae
    (S : StochasticSteepestDescentGeometryContext Ω V) :
    ∀ t i, ∀ᵐ ω ∂S.μ, ‖S.ξ t i ω‖ ≤ S.noiseRadius := by
  intro t i
  simpa [StochasticSteepestDescentGeometryContext.ξ,
    StochasticSteepestDescentGeometryContext.grad,
    StochasticSteepestDescentGeometryContext.noiseRadius] using
    S.oracle_sample_norm_le_noiseRadius_ae t i

end PublicTheorems

end StochasticSteepestDescentGeometryContext

end

end SteepestDescentOptimizationBounds
