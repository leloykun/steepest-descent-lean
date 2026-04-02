import Mathlib
import SteepestDescentOptimizationBounds.Assumptions
import SteepestDescentOptimizationBounds.DescentLemma
import SteepestDescentOptimizationBounds.WeightAndUpdateBounds
import SteepestDescentOptimizationBounds.NesterovMomentumBounds

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

/-!
This file contains the deterministic Frank-Wolfe-gap layer for the decoupled
weight-decay geometry already packaged in
`StochasticFrankWolfeGeometryContext`.

Upstream dependencies:

- `Assumptions.lean` provides the geometry context, gradients, and LMO data.
- `DescentLemma.lean` provides the local Taylor bound.
- `WeightAndUpdateBounds.lean` provides Proposition 9, which replaces the
  ball-invariance and displacement lemmas from the Frank-Wolfe note.
- `NesterovMomentumBounds.lean` provides the shared Nesterov split and
  operator-norm helper lemmas used to compare the approximate LMO direction to
  the exact Frank-Wolfe gap.

Downstream use:

- `FrankWolfeExpectedGap.lean` imports this file to instantiate the generic
  averaged Frank-Wolfe gap theorem with Corollary 11 and derive the
  best-iterate corollary.
- `FrankWolfeExpectedSuboptimality.lean` imports this file directly to reuse
  the deterministic Frank-Wolfe descent theorem.
- `StarConvexExpectedSuboptimality.lean` remains independent; this file does not
  depend on Theorem 14.
-/

namespace StochasticFrankWolfeGeometryContext

section PublicDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- The radius-`1 / λ` primal ball used in the Frank-Wolfe-gap definition. -/
def constraintBall (S : StochasticFrankWolfeGeometryContext Ω V) : Set V :=
  Metric.closedBall 0 (1 / S.lambda)

/-- The LMO direction rescaled to the primal radius `1 / λ` ball. -/
def scaledLMOPoint
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) : V :=
  (1 / S.lambda) • S.aStar t

/--
The Frank-Wolfe gap at a point, defined theorem-first as the supremum of the
linearization over the radius-`1 / λ` ball.
-/
def frankWolfeGapAt
    (S : StochasticFrankWolfeGeometryContext Ω V) (X : V) : ℝ :=
  sSup ((fun V => (S.fGrad X) (X - V)) '' S.constraintBall)

/-- The iterate-wise Frank-Wolfe gap. -/
def frankWolfeGap
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) : ℝ :=
  S.frankWolfeGapAt (S.W t)

end PublicDefinitions

section PrivateDefinitions

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

/-- Canonical pairing context for the actual continuous dual. -/
private def continuousDualPairing :
    ContinuousDualPairingContext V (StrongDual ℝ V) where
  toLinear := by
    simpa using (ContinuousLinearMap.id ℝ (StrongDual ℝ V))
  opNorm_le := by
    intro xDual
    simp

end PrivateDefinitions

section PrivateLemmas

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

/-- Controls an `L/2 * n^2` term whenever `n ≤ 2η`. -/
private lemma quadratic_two_eta_bound
    (L η n : ℝ)
    (hL : 0 ≤ L) (hn : 0 ≤ n) (h : n ≤ 2 * η) :
    (L / 2) * n ^ 2 ≤ 2 * L * η ^ 2 := by
  have hSquare : n ^ 2 ≤ (2 * η) ^ 2 := by
    nlinarith
  calc
    (L / 2) * n ^ 2 ≤ (L / 2) * (2 * η) ^ 2 := by
      gcongr
    _ = 2 * L * η ^ 2 := by
      ring

/-- Unpacks the decomposition `∇f(W_t) = C_t + error_t` on a concrete vector. -/
private lemma grad_split_apply
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) (v : V) :
    (S.grad t) v = (S.C t) v + S.nesterovError t v := by
  have h := congrArg (fun f : StrongDual ℝ V => f v) (S.nesterovError_split t)
  simpa [StochasticSteepestDescentGeometryContext.grad] using h

private lemma scaledLMOPoint_mem_constraintBall
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    S.scaledLMOPoint t ∈ S.constraintBall := by
  have hInvNonneg : 0 ≤ 1 / S.lambda := one_div_nonneg.mpr S.lambda_pos.le
  have hNorm :
      ‖S.scaledLMOPoint t‖ ≤ 1 / S.lambda := by
    calc
      ‖S.scaledLMOPoint t‖
          = (1 / S.lambda) * ‖S.aStar t‖ := by
              rw [StochasticFrankWolfeGeometryContext.scaledLMOPoint, norm_smul,
                Real.norm_of_nonneg hInvNonneg]
      _ ≤ (1 / S.lambda) * 1 := by
            exact mul_le_mul_of_nonneg_left (S.aStar_norm_le t) hInvNonneg
      _ = 1 / S.lambda := by ring
  simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
    using hNorm

private lemma scaledLMOPoint_optimal_on_constraintBall
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    ∀ x ∈ S.constraintBall, (S.C t) (S.scaledLMOPoint t) ≤ (S.C t) x := by
  intro x hx
  have hxNorm : ‖x‖ ≤ 1 / S.lambda := by
    simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
      using hx
  let A : V := S.lambda • x
  have hANorm : ‖A‖ ≤ 1 := by
    calc
      ‖A‖ = S.lambda * ‖x‖ := by
        dsimp [A]
        simp [norm_smul, Real.norm_of_nonneg S.lambda_pos.le]
      _ ≤ S.lambda * (1 / S.lambda) := by
        exact mul_le_mul_of_nonneg_left hxNorm S.lambda_pos.le
      _ = 1 := by
        field_simp [S.lambda_pos.ne']
  have hOpt := S.aStar_optimal t A hANorm
  calc
    (S.C t) (S.scaledLMOPoint t)
        = (1 / S.lambda) * (S.C t) (S.aStar t) := by
            simp [StochasticFrankWolfeGeometryContext.scaledLMOPoint, smul_eq_mul]
    _ ≤ (1 / S.lambda) * (S.C t) A := by
          exact mul_le_mul_of_nonneg_left hOpt (one_div_nonneg.mpr S.lambda_pos.le)
    _ = (S.C t) x := by
          dsimp [A]
          rw [ContinuousLinearMap.map_smul]
          simp [smul_eq_mul]
          field_simp [S.lambda_pos.ne']

private lemma scaledLMOPoint_sub_weight_eq
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    S.W (t + 1) - S.W t = (S.lambda * S.eta) • (S.scaledLMOPoint t - S.W t) := by
  have hScale :
      S.eta • S.aStar t = (S.lambda * S.eta) • S.scaledLMOPoint t := by
    rw [StochasticFrankWolfeGeometryContext.scaledLMOPoint, smul_smul]
    field_simp [S.lambda_pos.ne']
  calc
    S.W (t + 1) - S.W t
        = S.eta • S.aStar t - (S.lambda * S.eta) • S.W t := by
            rw [S.update_eq t]
            simp [sub_eq_add_neg, one_smul, add_smul, add_assoc, add_left_comm, add_comm]
    _ = (S.lambda * S.eta) • S.scaledLMOPoint t - (S.lambda * S.eta) • S.W t := by
          rw [hScale]
    _ = (S.lambda * S.eta) • (S.scaledLMOPoint t - S.W t) := by
          rw [smul_sub]

private lemma scaledLMOPoint_sub_feasible_bound
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ)
    {V : V} (hV : V ∈ S.constraintBall) :
    ‖S.scaledLMOPoint t - V‖ ≤ 2 / S.lambda := by
  have hScaled :
      ‖S.scaledLMOPoint t‖ ≤ 1 / S.lambda := by
    simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
      using S.scaledLMOPoint_mem_constraintBall t
  have hVNorm : ‖V‖ ≤ 1 / S.lambda := by
    simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
      using hV
  calc
    ‖S.scaledLMOPoint t - V‖ ≤ ‖S.scaledLMOPoint t‖ + ‖V‖ := norm_sub_le _ _
    _ ≤ 1 / S.lambda + 1 / S.lambda := by
          gcongr
    _ = 2 / S.lambda := by ring

omit [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
  [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)] in
private lemma exists_lt_neg_apply_closedBall_of_lt
    (f : StrongDual ℝ V) {r w : ℝ} (hr : 0 < r) (hw : w < r * ‖f‖) :
    ∃ x ∈ Metric.closedBall (0 : V) r, w < -f x := by
  by_cases hwNeg : w < 0
  · refine ⟨0, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hr.le
    · simpa using hwNeg
  have hwNonneg : 0 ≤ w := le_of_not_gt hwNeg
  have hdiv : w / r < ‖f‖ := by
    exact (div_lt_iff₀ hr).2 (by simpa [mul_comm] using hw)
  obtain ⟨x, hxNorm, hfxNorm⟩ := f.exists_lt_apply_of_lt_opNorm hdiv
  have hfxAbs : w / r < |f x| := by
    simpa [Real.norm_eq_abs] using hfxNorm
  by_cases hfxNonneg : 0 ≤ f x
  · refine ⟨-(r • x), ?_, ?_⟩
    · have hMem : ‖r • x‖ < r := by
        rw [norm_smul, Real.norm_of_nonneg hr.le]
        nlinarith
      simpa [Metric.mem_closedBall, dist_eq_norm] using hMem.le
    · have hlt : w / r < f x := by
        simpa [abs_of_nonneg hfxNonneg] using hfxAbs
      have hmul : w < r * f x := by
        have := (div_lt_iff₀ hr).1 hlt
        simpa [mul_comm] using this
      simpa [ContinuousLinearMap.map_neg, ContinuousLinearMap.map_smul, smul_eq_mul] using hmul
  · have hfxNeg : f x < 0 := lt_of_not_ge hfxNonneg
    refine ⟨r • x, ?_, ?_⟩
    · have hMem : ‖r • x‖ < r := by
        rw [norm_smul, Real.norm_of_nonneg hr.le]
        nlinarith
      simpa [Metric.mem_closedBall, dist_eq_norm] using hMem.le
    · have hlt : w / r < -f x := by
        simpa [abs_of_neg hfxNeg] using hfxAbs
      have hmul : w < r * (-f x) := by
        have := (div_lt_iff₀ hr).1 hlt
        simpa [mul_comm] using this
      simpa [ContinuousLinearMap.map_smul, smul_eq_mul] using hmul

omit [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)] in
private lemma sSup_neg_apply_closedBall_eq
    (f : StrongDual ℝ V) {r : ℝ} (hr : 0 < r) :
    sSup ((fun x : V => -f x) '' Metric.closedBall (0 : V) r) = r * ‖f‖ := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · exact (Metric.nonempty_closedBall.mpr hr.le).image _
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxNorm : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hOp : ‖f x‖ ≤ ‖f‖ * r := by
      simpa using f.le_opNorm_of_le hxNorm
    exact (le_abs_self _).trans (by simpa [mul_comm] using hOp)
  · intro w hw
    rcases exists_lt_neg_apply_closedBall_of_lt f hr hw with ⟨x, hx, hxlt⟩
    exact ⟨-f x, ⟨x, hx, rfl⟩, hxlt⟩

private lemma frankWolfeGap_values_nonempty
    (S : StochasticFrankWolfeGeometryContext Ω V) (X : V) :
    (((fun V => (S.fGrad X) (X - V)) '' S.constraintBall) : Set ℝ).Nonempty := by
  refine ⟨(S.fGrad X) (X - 0), ?_⟩
  refine ⟨0, ?_, rfl⟩
  simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
    using (show ‖(0 : V)‖ ≤ 1 / S.lambda by simp [S.lambda_pos.le])

private lemma fwGapInf_set_eq_neg
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    sInf ((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall) = -S.frankWolfeGap t := by
  have hSet :
      ((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall) =
        -(((fun V => (S.grad t) (S.W t - V)) '' S.constraintBall) : Set ℝ) := by
    have hFun :
        (fun V => (S.grad t) (V - S.W t)) =
          fun V => -((S.grad t) (S.W t - V)) := by
      funext x
      have hVec : x - S.W t = -(S.W t - x) := by
        abel_nf
      rw [hVec, map_neg]
    rw [hFun, ← Set.image_image, Set.image_neg_eq_neg]
  calc
    sInf ((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall)
        = sInf (-(((fun V => (S.grad t) (S.W t - V)) '' S.constraintBall) : Set ℝ)) := by
            rw [hSet]
    _ = -sSup (((fun V => (S.grad t) (S.W t - V)) '' S.constraintBall) : Set ℝ) := by
          rw [Real.sInf_neg]
    _ = -S.frankWolfeGap t := by
          simp [StochasticFrankWolfeGeometryContext.frankWolfeGap,
            StochasticFrankWolfeGeometryContext.frankWolfeGapAt,
            StochasticSteepestDescentGeometryContext.grad]

private lemma sum_range_fwGap_telescope
    (S : StochasticFrankWolfeGeometryContext Ω V) :
    ∀ T,
      Finset.sum (Finset.range T) (fun t => S.f (S.W t) - S.f (S.W (t + 1))) =
        S.f (S.W 0) - S.f (S.W T)
  | 0 => by simp
  | T + 1 => by
      rw [Finset.sum_range_succ, sum_range_fwGap_telescope S T]
      ring

end PrivateLemmas

section PublicTheorems

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

/--
The scaled LMO point lies in the radius-`1 / λ` ball and minimizes the linear
surrogate `C_t` over that ball.
-/
theorem lmo_scaled_properties
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    ‖S.scaledLMOPoint t‖ ≤ 1 / S.lambda ∧
      ∀ V ∈ S.constraintBall, (S.C t) (S.scaledLMOPoint t) ≤ (S.C t) V := by
  refine ⟨?_, S.scaledLMOPoint_optimal_on_constraintBall t⟩
  simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
    using S.scaledLMOPoint_mem_constraintBall t

/--
The Frank-Wolfe gap over the radius-`1 / λ` ball has the expected closed form.
-/
theorem fwGap_ball_formula
    (S : StochasticFrankWolfeGeometryContext Ω V) (X : V) :
    S.frankWolfeGapAt X = (S.fGrad X) X + (1 / S.lambda) * ‖S.fGrad X‖ := by
  let targetSet : Set ℝ :=
    ((fun V => (S.fGrad X) (X - V)) '' S.constraintBall)
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ ?_
  · simpa [targetSet] using S.frankWolfeGap_values_nonempty X
  · intro y hy
    rcases hy with ⟨V, hV, rfl⟩
    have hUpper :
        -(S.fGrad X) V ≤ (1 / S.lambda) * ‖S.fGrad X‖ := by
      have hVNorm : ‖V‖ ≤ 1 / S.lambda := by
        simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
          using hV
      have hOp : ‖(S.fGrad X) V‖ ≤ ‖S.fGrad X‖ * (1 / S.lambda) := by
        simpa using (S.fGrad X).le_opNorm_of_le hVNorm
      exact (le_abs_self _).trans (by simpa [mul_comm] using hOp)
    calc
      (S.fGrad X) (X - V) = (S.fGrad X) X + (-(S.fGrad X) V) := by
        rw [map_sub]
        ring
      _ ≤ (S.fGrad X) X + (1 / S.lambda) * ‖S.fGrad X‖ := by
        linarith
  · intro w hw
    obtain ⟨V, hV, hLt⟩ :=
      exists_lt_neg_apply_closedBall_of_lt
        (f := S.fGrad X)
        (hr := one_div_pos.mpr S.lambda_pos)
        (w := w - (S.fGrad X) X)
        (by simpa [sub_lt_iff_lt_add, add_comm, add_left_comm, add_assoc, mul_comm] using hw)
    refine ⟨(S.fGrad X) (X - V), ?_, ?_⟩
    · exact ⟨V, hV, rfl⟩
    · calc
        w < (S.fGrad X) X + (-(S.fGrad X) V) := by
          linarith
        _ = (S.fGrad X) (X - V) := by
              rw [map_sub]
              ring

/--
The LMO step computed from `C_t` is an approximate Frank-Wolfe step for the
true gradient, with error controlled by the Nesterov residual.
-/
theorem approx_lmo_fwGap_inner_bound
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    (S.grad t) (S.scaledLMOPoint t - S.W t) ≤
      -S.frankWolfeGap t + (2 / S.lambda) * S.nesterovErrorNorm t := by
  let c : ℝ := (2 / S.lambda) * S.nesterovErrorNorm t
  have hScaledOpt := (S.lmo_scaled_properties t).2
  have hLower :
      ∀ a ∈ ((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall),
        (S.grad t) (S.scaledLMOPoint t - S.W t) - c ≤ a := by
    intro a ha
    rcases ha with ⟨V, hV, rfl⟩
    have hC :
        (S.C t) (S.scaledLMOPoint t - S.W t) ≤ (S.C t) (V - S.W t) := by
      have hOpt := hScaledOpt V hV
      rw [map_sub, map_sub]
      linarith
    have hErr :
        S.nesterovError t (S.scaledLMOPoint t - V) ≤ c := by
      have hApply :=
        S.nesterovError_apply_le t (S.scaledLMOPoint t - V)
      have hNorm :
          ‖S.scaledLMOPoint t - V‖ ≤ 2 / S.lambda :=
        S.scaledLMOPoint_sub_feasible_bound t hV
      nlinarith [hApply, hNorm, S.nesterovErrorNorm_nonneg t, S.lambda_pos]
    have hDecomp :
        (S.grad t) (S.scaledLMOPoint t - S.W t) ≤
          (S.grad t) (V - S.W t) + S.nesterovError t (S.scaledLMOPoint t - V) := by
      calc
        (S.grad t) (S.scaledLMOPoint t - S.W t)
            = (S.C t) (S.scaledLMOPoint t - S.W t)
                + S.nesterovError t (S.scaledLMOPoint t - S.W t) := by
                    rw [S.grad_split_apply t]
        _ ≤ (S.C t) (V - S.W t)
              + S.nesterovError t (S.scaledLMOPoint t - S.W t) := by
                gcongr
        _ = (S.grad t) (V - S.W t) + S.nesterovError t (S.scaledLMOPoint t - V) := by
              rw [S.grad_split_apply t]
              have hSplit :
                  S.nesterovError t (S.scaledLMOPoint t - S.W t)
                    = S.nesterovError t (V - S.W t)
                        + S.nesterovError t (S.scaledLMOPoint t - V) := by
                  have hEq :
                      S.scaledLMOPoint t - S.W t =
                        (V - S.W t) + (S.scaledLMOPoint t - V) := by
                    abel_nf
                  rw [hEq, map_add]
              linarith
    linarith
  have hNonempty :
      (((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall) : Set ℝ).Nonempty := by
    refine ⟨(S.grad t) (0 - S.W t), ?_⟩
    refine ⟨0, ?_, rfl⟩
    simpa [StochasticFrankWolfeGeometryContext.constraintBall, Metric.mem_closedBall, dist_eq_norm]
      using (show ‖(0 : V)‖ ≤ 1 / S.lambda by simp [S.lambda_pos.le])
  have hInf :
      (S.grad t) (S.scaledLMOPoint t - S.W t) - c ≤
        sInf ((fun V => (S.grad t) (V - S.W t)) '' S.constraintBall) :=
    le_csInf hNonempty hLower
  rw [S.fwGapInf_set_eq_neg t] at hInf
  linarith

/--
Deterministic one-step Frank-Wolfe-gap descent for the decoupled weight-decay
update.
-/
theorem one_step_descent_fwGap
    (S : StochasticFrankWolfeGeometryContext Ω V) (t : ℕ) :
    S.f (S.W (t + 1)) ≤
      S.f (S.W t)
        - S.lambda * S.eta * S.frankWolfeGap t
        + 2 * S.eta * S.nesterovErrorNorm t
        + 2 * S.L * S.eta ^ 2 := by
  have hProp9 := S.proposition9_weight_and_update_bounds t
  rcases hProp9 with ⟨hWeight, hUpdateBound⟩
  have hNextWeight : ‖S.W (t + 1)‖ ≤ 1 / S.lambda :=
    S.weight_bound_from_feasible_step (t + 1)
  have hTaylor :=
    taylor_bound_of_LSmoothOnClosedBallUnderPair
      (continuousDualPairing (V := V))
      (f := S.f)
      (grad := S.fGrad)
      (L := S.L)
      (R := 1 / S.lambda)
      S.fderiv_eq
      S.assumption3_fLocalSmoothness.local_lipschitz
      hWeight
      hNextWeight
  have h0 : 0 ≤ ‖S.W (t + 1) - S.W t‖ := norm_nonneg _
  have hQuad :=
    quadratic_two_eta_bound
      S.L S.eta ‖S.W (t + 1) - S.W t‖
      S.assumption3_fLocalSmoothness.nonneg h0 hUpdateBound
  have hStepRightRaw := (abs_le.mp hTaylor).2
  have hLinearNext :
      (S.grad t) (S.W (t + 1) - S.W t) =
        (S.fGrad (S.W t)) (S.W (t + 1)) - (S.fGrad (S.W t)) (S.W t) := by
    simp [StochasticSteepestDescentGeometryContext.grad]
  have hSmoothStep :
      S.f (S.W (t + 1)) ≤
        S.f (S.W t) + (S.grad t) (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := by
    have hStepRight :
        S.f (S.W (t + 1)) ≤
          S.f (S.W t)
            + (S.grad t) (S.W (t + 1) - S.W t)
            + S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
      rw [hLinearNext]
      have hTmp :
          S.f (S.W (t + 1)) -
              (S.f (S.W t)
                + ((S.fGrad (S.W t)) (S.W (t + 1)) - (S.fGrad (S.W t)) (S.W t))) ≤
            S.L / 2 * ‖S.W (t + 1) - S.W t‖ ^ 2 := by
        simpa [continuousDualPairing, StochasticSteepestDescentGeometryContext.grad] using hStepRightRaw
      linarith
    linarith
  have hStepVec := S.scaledLMOPoint_sub_weight_eq t
  have hGradStep :
      (S.grad t) (S.W (t + 1) - S.W t) =
        (S.lambda * S.eta) * (S.grad t) (S.scaledLMOPoint t - S.W t) := by
    rw [hStepVec, ContinuousLinearMap.map_smul]
    simp [smul_eq_mul]
  have hApprox := S.approx_lmo_fwGap_inner_bound t
  calc
    S.f (S.W (t + 1))
        ≤ S.f (S.W t) + (S.grad t) (S.W (t + 1) - S.W t) + 2 * S.L * S.eta ^ 2 := hSmoothStep
    _ = S.f (S.W t)
          + (S.lambda * S.eta) * (S.grad t) (S.scaledLMOPoint t - S.W t)
          + 2 * S.L * S.eta ^ 2 := by rw [hGradStep]
    _ ≤ S.f (S.W t)
          + (S.lambda * S.eta) *
              (-S.frankWolfeGap t + (2 / S.lambda) * S.nesterovErrorNorm t)
          + 2 * S.L * S.eta ^ 2 := by
            gcongr
            exact S.lambda_eta_nonneg
    _ = S.f (S.W t)
          - S.lambda * S.eta * S.frankWolfeGap t
          + 2 * S.eta * S.nesterovErrorNorm t
          + 2 * S.L * S.eta ^ 2 := by
            field_simp [S.lambda_pos.ne']
            ring

/--
Generic averaged Frank-Wolfe-gap bound under a pointwise tracking envelope.
-/
theorem avg_frankWolfeGap_bound_of_tracking_bound
    (S : StochasticFrankWolfeGeometryContext Ω V)
    (fInf : ℝ)
    (err : ℕ → ℝ)
    (hInf : ∀ t, fInf ≤ S.f (S.W t))
    (hErr : ∀ t, S.nesterovErrorNorm t ≤ err t) :
    ∀ T, 0 < T →
      (Finset.sum (Finset.range T) fun t => S.frankWolfeGap t) / (T : ℝ) ≤
        (S.f (S.W 0) - fInf) / (S.lambda * S.eta * T)
          + (2 / (S.lambda * T)) * (Finset.sum (Finset.range T) err)
          + 2 * S.L * S.eta / S.lambda := by
  intro T hT
  let sumGap : ℝ := Finset.sum (Finset.range T) fun t => S.frankWolfeGap t
  let sumErr : ℝ := Finset.sum (Finset.range T) err
  have hT' : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hSum :
      (S.lambda * S.eta) * sumGap ≤
        Finset.sum (Finset.range T) (fun t => S.f (S.W t) - S.f (S.W (t + 1)))
          + 2 * S.eta * sumErr
          + (T : ℝ) * (2 * S.L * S.eta ^ 2) := by
    calc
      (S.lambda * S.eta) * sumGap
          = Finset.sum (Finset.range T) (fun t => S.lambda * S.eta * S.frankWolfeGap t) := by
              simp [sumGap, Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range T)
            (fun t => (S.f (S.W t) - S.f (S.W (t + 1))) + 2 * S.eta * err t + 2 * S.L * S.eta ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro t ht
              have hOne := S.one_step_descent_fwGap t
              have hScaledErr :
                  2 * S.eta * S.nesterovErrorNorm t ≤ 2 * S.eta * err t := by
                exact mul_le_mul_of_nonneg_left (hErr t) (by nlinarith [S.eta_pos])
              linarith [hOne, hScaledErr]
      _ = Finset.sum (Finset.range T) (fun t => S.f (S.W t) - S.f (S.W (t + 1)))
            + 2 * S.eta * sumErr
            + (T : ℝ) * (2 * S.L * S.eta ^ 2) := by
              simp [sumErr, Finset.sum_add_distrib, Finset.mul_sum, add_left_comm, add_comm]
  have hTel := S.sum_range_fwGap_telescope T
  have hLower :
      S.f (S.W 0) - S.f (S.W T) ≤ S.f (S.W 0) - fInf := by
    linarith [hInf T]
  have hSum' :
      (S.lambda * S.eta) * sumGap ≤
        S.f (S.W 0) - fInf + 2 * S.eta * sumErr + (T : ℝ) * (2 * S.L * S.eta ^ 2) := by
    linarith [hSum, hTel, hLower]
  have hDiv :
      sumGap ≤
        (S.f (S.W 0) - fInf) / (S.lambda * S.eta)
          + (2 / S.lambda) * sumErr
          + (T : ℝ) * (2 * S.L * S.eta / S.lambda) := by
    have hRaw :
        sumGap ≤
          (S.f (S.W 0) - fInf + 2 * S.eta * sumErr + (T : ℝ) * (2 * S.L * S.eta ^ 2)) /
            (S.lambda * S.eta) := by
      have hMul :
          sumGap * (S.lambda * S.eta) ≤
            S.f (S.W 0) - fInf + 2 * S.eta * sumErr + (T : ℝ) * (2 * S.L * S.eta ^ 2) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hSum'
      exact (le_div_iff₀ S.lambda_eta_pos).2 hMul
    calc
      sumGap ≤
          (S.f (S.W 0) - fInf + 2 * S.eta * sumErr + (T : ℝ) * (2 * S.L * S.eta ^ 2)) /
            (S.lambda * S.eta) := hRaw
      _ =
          (S.f (S.W 0) - fInf) / (S.lambda * S.eta)
            + (2 / S.lambda) * sumErr
            + (T : ℝ) * (2 * S.L * S.eta / S.lambda) := by
              field_simp [S.lambda_eta_ne_zero, S.lambda_pos.ne', S.eta_pos.ne']
  have hAvgRaw :
      sumGap / (T : ℝ) ≤
        ((S.f (S.W 0) - fInf) / (S.lambda * S.eta)
          + (2 / S.lambda) * sumErr
          + (T : ℝ) * (2 * S.L * S.eta / S.lambda)) / (T : ℝ) := by
    exact div_le_div_of_nonneg_right hDiv hT'.le
  calc
    sumGap / (T : ℝ)
      ≤ ((S.f (S.W 0) - fInf) / (S.lambda * S.eta)
          + (2 / S.lambda) * sumErr
          + (T : ℝ) * (2 * S.L * S.eta / S.lambda)) / (T : ℝ) := hAvgRaw
    _ = (S.f (S.W 0) - fInf) / (S.lambda * S.eta * T)
          + (2 / (S.lambda * T)) * sumErr
          + 2 * S.L * S.eta / S.lambda := by
            field_simp [S.lambda_eta_ne_zero, S.lambda_pos.ne', S.eta_pos.ne', hT'.ne']

end PublicTheorems

end StochasticFrankWolfeGeometryContext

end

end SteepestDescentOptimizationBounds
