import Mathlib
import SteepestDescentOptimizationBounds.Assumptions

/-!
Analytic descent-lemma toolkit for the project.

Upstream dependency:

- `Mathlib` provides the Taylor, derivative, and convexity infrastructure.

Downstream use:

- `StarConvex.lean` and the Frank-Wolfe layers use these one-step and
  closed-ball descent inequalities.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

section GeneralNormDescent

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem taylor_bound_of_lipschitz_fderiv_on_convex_of_localFDeriv
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {L : ℝ} {s : Set V}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hLipschitz : ∀ x ∈ s, ∀ y ∈ s, ‖f' y - f' x‖ ≤ L * ‖y - x‖)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    |f y - (f x + f' x (y - x))| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  let v : V := y - x
  let γ : ℝ → V := AffineMap.lineMap x y
  let u : ℝ → ℝ := fun t => f (γ t) - (f x + t * f' x v)
  let q : ℝ → ℝ := fun t => u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  let r : ℝ → ℝ := fun t => -u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  let D : Set ℝ := Set.Icc 0 1
  have hγ_sub : ∀ t : ℝ, γ t - x = t • v := by
    intro t
    dsimp [γ, v]
    simp [AffineMap.lineMap_apply]
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ v t := by
    intro t
    simpa [γ, v] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
  have hγ_mem : ∀ t ∈ D, γ t ∈ s := by
    intro t ht
    have hSeg : γ t ∈ segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    exact hs.segment_subset hx hy hSeg
  have hu_deriv :
      ∀ t ∈ D, HasDerivWithinAt u ((f' (γ t) - f' x) v) D t := by
    intro t ht
    have hComp :
        HasDerivWithinAt (fun s : ℝ => f (γ s)) (f' (γ t) v) D t := by
      simpa [γ, v] using
        (hf (γ t) (hγ_mem t ht)).comp_hasDerivWithinAt t ((hγ_deriv t).hasDerivWithinAt)
    have hAff :
        HasDerivWithinAt (fun s : ℝ => f x + s * f' x v) (f' x v) D t := by
      simpa using (((hasDerivAt_mul_const (f' x v) (x := t)).const_add (f x)).hasDerivWithinAt)
    convert hComp.sub hAff using 1
  have hQuad_deriv :
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
    intro t
    convert (((hasDerivAt_id t).pow 2).const_mul ((L / 2) * ‖v‖ ^ 2)) using 1
    · ext s
      simp [pow_two]
      ring_nf
    · simp
      ring
  have hq_deriv :
      ∀ t ∈ D, HasDerivWithinAt q (((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2) D t := by
    intro t ht
    simpa [q] using (hu_deriv t ht).sub ((hQuad_deriv t).hasDerivWithinAt)
  have hr_deriv :
      ∀ t ∈ D, HasDerivWithinAt r (-(f' (γ t) - f' x) v - L * t * ‖v‖ ^ 2) D t := by
    intro t ht
    simpa [r] using ((hu_deriv t ht).neg).sub ((hQuad_deriv t).hasDerivWithinAt)
  have hq_cont : ContinuousOn q D := by
    intro t ht
    exact (hq_deriv t ht).continuousWithinAt
  have hr_cont : ContinuousOn r D := by
    intro t ht
    exact (hr_deriv t ht).continuousWithinAt
  have hEval_bound :
      ∀ t ∈ interior D, |(f' (γ t) - f' x) v| ≤ L * t * ‖v‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [D] using ht
    have hD : t ∈ D := interior_subset ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht'.1
    have hSegNorm : ‖γ t - x‖ = t * ‖v‖ := by
      rw [hγ_sub t, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hBound :
        ‖(f' (γ t) - f' x) v‖ ≤ L * t * ‖v‖ ^ 2 := by
      have hLipMul :
          ‖f' (γ t) - f' x‖ * ‖v‖ ≤ (L * ‖γ t - x‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (hLipschitz x hx (γ t) (hγ_mem t hD)) (norm_nonneg v)
      calc
        ‖(f' (γ t) - f' x) v‖ ≤ ‖f' (γ t) - f' x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖γ t - x‖) * ‖v‖ := hLipMul
        _ = L * t * ‖v‖ ^ 2 := by
          rw [hSegNorm]
          ring
    simpa [Real.norm_eq_abs] using hBound
  have hq_antitone : AntitoneOn q D := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := D)
        (f := q)
        (f' := fun t => ((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hq_cont
        ?_
        ?_
    · intro t ht
      exact
        (hq_deriv t (interior_subset ht)).mono_of_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds
            (show D ∈ nhds t from mem_interior_iff_mem_nhds.mp ht))
    · intro t ht
      have hUpper : (f' (γ t) - f' x) v ≤ L * t * ‖v‖ ^ 2 := (abs_le.mp (hEval_bound t ht)).2
      linarith
  have hr_antitone : AntitoneOn r D := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := D)
        (f := r)
        (f' := fun t => (-(f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hr_cont
        ?_
        ?_
    · intro t ht
      exact
        (hr_deriv t (interior_subset ht)).mono_of_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds
            (show D ∈ nhds t from mem_interior_iff_mem_nhds.mp ht))
    · intro t ht
      have hLower : -(L * t * ‖v‖ ^ 2) ≤ (f' (γ t) - f' x) v := (abs_le.mp (hEval_bound t ht)).1
      linarith
  have hq10 : q 1 ≤ q 0 := by
    exact hq_antitone (by simp [D]) (by simp [D]) (by norm_num)
  have hr10 : r 1 ≤ r 0 := by
    exact hr_antitone (by simp [D]) (by simp [D]) (by norm_num)
  have hUpper :
      f y - (f x + f' x v) ≤ (L / 2) * ‖v‖ ^ 2 := by
    have hq0 : q 0 = 0 := by
      simp [q, u, γ, v]
    have hq1 : q 1 = f y - (f x + f' x v) - (L / 2) * ‖v‖ ^ 2 := by
      simp [q, u, γ, v]
    linarith [hq10, hq0, hq1]
  have hLower :
      -(L / 2) * ‖v‖ ^ 2 ≤ f y - (f x + f' x v) := by
    have hr0 : r 0 = 0 := by
      simp [r, u, γ, v]
    have hr1 : r 1 = -(f y - (f x + f' x v)) - (L / 2) * ‖v‖ ^ 2 := by
      simp [r, u, γ, v]
    linarith [hr10, hr0, hr1]
  have hLower' : -(L / 2 * ‖v‖ ^ 2) ≤ f y - (f x + f' x v) := by
    simpa [mul_assoc] using hLower
  simpa [v] using abs_le.mpr ⟨hLower', hUpper⟩

/--
Local version of the sharp descent lemma on a convex set.

This is the form needed to use the local smooth proxy potential on the closed noise ball from the
closed-ball formulation: the derivative only needs to be `L`-Lipschitz on the convex region
containing the segment between `x` and `y`.
-/
private theorem taylor_bound_of_lipschitz_fderiv_on_convex
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {L : ℝ} {s : Set V}
    (hs : Convex ℝ s)
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hLipschitz : ∀ x ∈ s, ∀ y ∈ s, ‖f' y - f' x‖ ≤ L * ‖y - x‖)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    |f y - (f x + f' x (y - x))| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  exact
    taylor_bound_of_lipschitz_fderiv_on_convex_of_localFDeriv
      hs
      (fun z _ => hf z)
      hLipschitz
      hx
      hy

/--
Sharp descent lemma on an arbitrary real normed space.

If the Fréchet derivative of `f` is `L`-Lipschitz in operator norm, then the
first-order Taylor remainder is bounded by `(L / 2) * ‖y - x‖²`.
-/
private theorem taylor_bound_of_lipschitz_fderiv
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hLipschitz : ∀ x y, ‖f' y - f' x‖ ≤ L * ‖y - x‖) :
    ∀ x y, |f y - (f x + f' x (y - x))| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  simpa using
    (taylor_bound_of_lipschitz_fderiv_on_convex_of_localFDeriv
      (s := Set.univ)
      (hs := convex_univ)
      (hf := fun z _ => hf z)
      (hLipschitz := fun z _ w _ => hLipschitz z w)
      (hx := by simp)
      (hy := by simp)
      (x := x)
      (y := y))

end GeneralNormDescent

section StrongDualBridge

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ------------------------------------------------------------------------
Closed-Ball Strong-Dual Bridge With Local Derivatives
------------------------------------------------------------------------ -/

/--
Local convex-set descent lemma when the derivative is only known on the convex
region itself and gradients are represented in the continuous dual.
-/
theorem taylor_bound_of_LSmoothOnConvexSetUnderStrongDual_of_localFDeriv
    {f : V → ℝ} {grad : V → StrongDual ℝ V} {L : ℝ} {s : Set V}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (grad x) x)
    (hLipschitz : ∀ x ∈ s, ∀ y ∈ s, ‖grad y - grad x‖ ≤ L * ‖y - x‖)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    |f y - (f x + grad x (y - x))| ≤
      (L / 2) * ‖y - x‖ ^ 2 := by
  exact
    taylor_bound_of_lipschitz_fderiv_on_convex_of_localFDeriv
      (f := f)
      (f' := grad)
      hs
      hf
      hLipschitz
      hx
      hy

/--
Closed-ball specialization of the local `StrongDual` descent lemma.
-/
theorem taylor_bound_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
    {f : V → ℝ} {grad : V → StrongDual ℝ V} {L R : ℝ}
    (hf : ∀ x, ‖x‖ ≤ R → HasFDerivAt f (grad x) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    {x y : V} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |f y - (f x + grad x (y - x))| ≤
      (L / 2) * ‖y - x‖ ^ 2 := by
  refine
    taylor_bound_of_LSmoothOnConvexSetUnderStrongDual_of_localFDeriv
      (f := f)
      (grad := grad)
      (L := L)
      (s := Metric.closedBall (0 : V) R)
      (convex_closedBall (0 : V) R)
      ?_
      ?_
      ?_
      ?_
  · intro z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using
      hf z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  · intro z hz w hw
    exact
      hLipschitz.bound
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)
  · simpa [mem_closedBall_zero_iff] using hx
  · simpa [mem_closedBall_zero_iff] using hy

/--
Comparison form specialized to the canonical `StrongDual` pairing.
-/
theorem taylor_compare_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
    {f : V → ℝ} {grad : V → StrongDual ℝ V} {L R : ℝ}
    (hf : ∀ x, ‖x‖ ≤ R → HasFDerivAt f (grad x) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    {x y : V} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    f x + grad x (y - x) ≤ f y + (L / 2) * ‖y - x‖ ^ 2 := by
  have h :=
    taylor_bound_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
      (f := f)
      (grad := grad)
      (L := L)
      (R := R)
      hf
      hLipschitz
      hx
      hy
  have hLower := (abs_le.mp h).1
  linarith

/--
One-step closed-ball descent lemma specialized to the canonical `StrongDual`
pairing.
-/
theorem step_upper_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
    {f : V → ℝ} {grad : V → StrongDual ℝ V} {L R α : ℝ}
    (hf : ∀ x, ‖x‖ ≤ R → HasFDerivAt f (grad x) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    (hα_nonneg : 0 ≤ α)
    {x ξ : V} (hx : ‖x‖ ≤ R) (hNext : ‖x + α • ξ‖ ≤ R) :
    f (x + α • ξ) ≤
      f x + α * grad x ξ + (L / 2) * α ^ 2 * ‖ξ‖ ^ 2 := by
  have h :=
    taylor_bound_of_LSmoothOnClosedBallUnderStrongDual_of_localFDeriv
      (f := f)
      (grad := grad)
      (L := L)
      (R := R)
      hf
      hLipschitz
      hx
      hNext
  have hStep : x + α • ξ - x = α • ξ := by
    abel_nf
  have hUpper := (abs_le.mp h).2
  rw [hStep, ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hα_nonneg] at hUpper
  have hUpper'' :
      f (x + α • ξ) - f x - α * grad x ξ ≤
        (L / 2) * (α * ‖ξ‖) ^ 2 := by
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hUpper
  have hUpper' :
      f (x + α • ξ) - f x - α * grad x ξ ≤
        L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
    have hEq : (L / 2) * (α * ‖ξ‖) ^ 2 = L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
      ring
    rw [hEq] at hUpper''
    exact hUpper''
  linarith

end StrongDualBridge

section StrongDualBidualBridge

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Closed-ball descent lemma for functions on `StrongDual ℝ V` whose derivative
is represented by the canonical bidual embedding of a primal-valued mirror map. -/
theorem step_upper_of_LSmoothOnClosedBallUnderStrongDualBidual_of_localFDeriv
    {f : StrongDual ℝ V → ℝ} {grad : StrongDual ℝ V → V} {L R α : ℝ}
    (hf : ∀ x, ‖x‖ ≤ R → HasFDerivAt f ((strongDualBidual V) (grad x)) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    (hα_nonneg : 0 ≤ α)
    {x ξ : StrongDual ℝ V} (hx : ‖x‖ ≤ R) (hNext : ‖x + α • ξ‖ ≤ R) :
    f (x + α • ξ) ≤
      f x + α * (strongDualBidual V (grad x)) ξ + (L / 2) * α ^ 2 * ‖ξ‖ ^ 2 := by
  have h :=
    taylor_bound_of_lipschitz_fderiv_on_convex_of_localFDeriv
      (V := StrongDual ℝ V)
      (f := f)
      (f' := fun x => (strongDualBidual V) (grad x))
      (L := L)
      (s := Metric.closedBall (0 : StrongDual ℝ V) R)
      (hs := convex_closedBall (0 : StrongDual ℝ V) R)
      (hf := by
        intro z hz
        simpa [Metric.mem_closedBall, dist_eq_norm] using
          hf z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz))
      (hLipschitz := by
        intro z hz w hw
        have hEmbed :
            ‖(strongDualBidual V) (grad w) - (strongDualBidual V) (grad z)‖ ≤
              ‖grad w - grad z‖ := by
          have hEmbed' : ‖(strongDualBidual V) (grad w - grad z)‖ ≤ ‖grad w - grad z‖ := by
            refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
            intro φ
            simpa [strongDualBidual, mul_comm] using
              (ContinuousLinearMap.le_opNorm φ (grad w - grad z))
          simpa [map_sub] using hEmbed'
        exact hEmbed.trans <|
          hLipschitz.bound
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
            (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw))
      (hx := by simpa [mem_closedBall_zero_iff] using hx)
      (hy := by simpa [mem_closedBall_zero_iff] using hNext)
  have hStep : x + α • ξ - x = α • ξ := by
    abel_nf
  have hUpper := (abs_le.mp h).2
  rw [hStep, ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hα_nonneg] at hUpper
  have hUpper'' :
      f (x + α • ξ) - f x - α * (strongDualBidual V (grad x)) ξ ≤
        (L / 2) * (α * ‖ξ‖) ^ 2 := by
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hUpper
  have hUpper' :
      f (x + α • ξ) - f x - α * (strongDualBidual V (grad x)) ξ ≤
        L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
    have hEq : (L / 2) * (α * ‖ξ‖) ^ 2 = L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
      ring
    rw [hEq] at hUpper''
    exact hUpper''
  linarith

end StrongDualBidualBridge

end

end SteepestDescentOptimizationBounds
