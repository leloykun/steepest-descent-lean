import Mathlib
import SteepestDescentOptimizationBounds.Assumptions

namespace SteepestDescentOptimizationBounds

noncomputable section

section GeneralNormDescent

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
Sharp descent lemma on an arbitrary real normed space.

If the Fréchet derivative of `f` is `L`-Lipschitz in operator norm, then the
first-order Taylor remainder is bounded by `(L / 2) * ‖y - x‖²`.
-/
theorem taylor_bound_of_lipschitz_fderiv
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hLipschitz : ∀ x y, ‖f' y - f' x‖ ≤ L * ‖y - x‖) :
    ∀ x y, |f y - (f x + f' x (y - x))| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  let v : V := y - x
  let γ : ℝ → V := AffineMap.lineMap x y
  let u : ℝ → ℝ := fun t => f (γ t) - (f x + t * f' x v)
  let q : ℝ → ℝ := fun t => u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  let r : ℝ → ℝ := fun t => -u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  have hγ_sub : ∀ t : ℝ, γ t - x = t • v := by
    intro t
    dsimp [γ, v]
    simp [AffineMap.lineMap_apply]
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ v t := by
    intro t
    simpa [γ, v] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
  have hu_deriv : ∀ t : ℝ, HasDerivAt u ((f' (γ t) - f' x) v) t := by
    intro t
    have hComp : HasDerivAt (fun s : ℝ => f (γ s)) (f' (γ t) v) t := by
      simpa [γ, v] using (hf (γ t)).comp_hasDerivAt t (hγ_deriv t)
    have hAff : HasDerivAt (fun s : ℝ => f x + s * f' x v) (f' x v) t := by
      simpa using (hasDerivAt_mul_const (f' x v) (x := t)).const_add (f x)
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
      ∀ t : ℝ, HasDerivAt q (((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2) t := by
    intro t
    simpa [q] using (hu_deriv t).sub (hQuad_deriv t)
  have hr_deriv :
      ∀ t : ℝ, HasDerivAt r (-(f' (γ t) - f' x) v - L * t * ‖v‖ ^ 2) t := by
    intro t
    simpa [r] using ((hu_deriv t).neg).sub (hQuad_deriv t)
  have hq_cont : Continuous q := by
    refine continuous_iff_continuousAt.mpr ?_
    intro t
    exact (hq_deriv t).continuousAt
  have hr_cont : Continuous r := by
    refine continuous_iff_continuousAt.mpr ?_
    intro t
    exact (hr_deriv t).continuousAt
  have hEval_bound :
      ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), |(f' (γ t) - f' x) v| ≤ L * t * ‖v‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht'.1
    have hSegNorm : ‖γ t - x‖ = t * ‖v‖ := by
      rw [hγ_sub t, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hBound :
        ‖(f' (γ t) - f' x) v‖ ≤ L * t * ‖v‖ ^ 2 := by
      have hLipMul :
          ‖f' (γ t) - f' x‖ * ‖v‖ ≤ (L * ‖γ t - x‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (hLipschitz x (γ t)) (norm_nonneg v)
      calc
        ‖(f' (γ t) - f' x) v‖ ≤ ‖f' (γ t) - f' x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖γ t - x‖) * ‖v‖ := hLipMul
        _ = L * t * ‖v‖ ^ 2 := by
          rw [hSegNorm]
          ring
    simpa [Real.norm_eq_abs] using hBound
  have hq_antitone : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (0 : ℝ) 1)
        (f := q)
        (f' := fun t => ((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hq_cont.continuousOn
        ?_
        ?_
    · intro t ht
      exact (hq_deriv t).hasDerivWithinAt
    · intro t ht
      have hUpper : (f' (γ t) - f' x) v ≤ L * t * ‖v‖ ^ 2 := (abs_le.mp (hEval_bound t ht)).2
      linarith
  have hr_antitone : AntitoneOn r (Set.Icc (0 : ℝ) 1) := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (0 : ℝ) 1)
        (f := r)
        (f' := fun t => (-(f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hr_cont.continuousOn
        ?_
        ?_
    · intro t ht
      exact (hr_deriv t).hasDerivWithinAt
    · intro t ht
      have hLower : -(L * t * ‖v‖ ^ 2) ≤ (f' (γ t) - f' x) v := (abs_le.mp (hEval_bound t ht)).1
      linarith
  have hq10 :
      q 1 ≤ q 0 := by
    exact hq_antitone (by norm_num) (by norm_num) (by norm_num)
  have hr10 :
      r 1 ≤ r 0 := by
    exact hr_antitone (by norm_num) (by norm_num) (by norm_num)
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

This is the form needed to use Assumption 4 on the closed noise ball from the
closed-ball formulation: the derivative only needs to be `L`-Lipschitz on the convex region
containing the segment between `x` and `y`.
-/
theorem taylor_bound_of_lipschitz_fderiv_on_convex
    {f : V → ℝ} {f' : V → V →L[ℝ] ℝ} {L : ℝ} {s : Set V}
    (hs : Convex ℝ s)
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hLipschitz : ∀ x ∈ s, ∀ y ∈ s, ‖f' y - f' x‖ ≤ L * ‖y - x‖)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    |f y - (f x + f' x (y - x))| ≤ (L / 2) * ‖y - x‖ ^ 2 := by
  let v : V := y - x
  let γ : ℝ → V := AffineMap.lineMap x y
  let u : ℝ → ℝ := fun t => f (γ t) - (f x + t * f' x v)
  let q : ℝ → ℝ := fun t => u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  let r : ℝ → ℝ := fun t => -u t - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  have hγ_sub : ∀ t : ℝ, γ t - x = t • v := by
    intro t
    dsimp [γ, v]
    simp [AffineMap.lineMap_apply]
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ v t := by
    intro t
    simpa [γ, v] using (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
  have hγ_mem : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), γ t ∈ s := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using ht
    have hOpenSeg : γ t ∈ openSegment ℝ x y := by
      simpa [γ] using lineMap_mem_openSegment (𝕜 := ℝ) x y ht'
    exact hs.segment_subset hx hy ((openSegment_subset_segment ℝ x y) hOpenSeg)
  have hu_deriv : ∀ t : ℝ, HasDerivAt u ((f' (γ t) - f' x) v) t := by
    intro t
    have hComp : HasDerivAt (fun s : ℝ => f (γ s)) (f' (γ t) v) t := by
      simpa [γ, v] using (hf (γ t)).comp_hasDerivAt t (hγ_deriv t)
    have hAff : HasDerivAt (fun s : ℝ => f x + s * f' x v) (f' x v) t := by
      simpa using (hasDerivAt_mul_const (f' x v) (x := t)).const_add (f x)
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
      ∀ t : ℝ, HasDerivAt q (((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2) t := by
    intro t
    simpa [q] using (hu_deriv t).sub (hQuad_deriv t)
  have hr_deriv :
      ∀ t : ℝ, HasDerivAt r (-(f' (γ t) - f' x) v - L * t * ‖v‖ ^ 2) t := by
    intro t
    simpa [r] using ((hu_deriv t).neg).sub (hQuad_deriv t)
  have hq_cont : Continuous q := by
    refine continuous_iff_continuousAt.mpr ?_
    intro t
    exact (hq_deriv t).continuousAt
  have hr_cont : Continuous r := by
    refine continuous_iff_continuousAt.mpr ?_
    intro t
    exact (hr_deriv t).continuousAt
  have hEval_bound :
      ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), |(f' (γ t) - f' x) v| ≤ L * t * ‖v‖ ^ 2 := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using ht
    have ht_nonneg : 0 ≤ t := le_of_lt ht'.1
    have hSegNorm : ‖γ t - x‖ = t * ‖v‖ := by
      rw [hγ_sub t, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hBound :
        ‖(f' (γ t) - f' x) v‖ ≤ L * t * ‖v‖ ^ 2 := by
      have hLipMul :
          ‖f' (γ t) - f' x‖ * ‖v‖ ≤ (L * ‖γ t - x‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (hLipschitz x hx (γ t) (hγ_mem t ht)) (norm_nonneg v)
      calc
        ‖(f' (γ t) - f' x) v‖ ≤ ‖f' (γ t) - f' x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖γ t - x‖) * ‖v‖ := hLipMul
        _ = L * t * ‖v‖ ^ 2 := by
          rw [hSegNorm]
          ring
    simpa [Real.norm_eq_abs] using hBound
  have hq_antitone : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (0 : ℝ) 1)
        (f := q)
        (f' := fun t => ((f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hq_cont.continuousOn
        ?_
        ?_
    · intro t ht
      exact (hq_deriv t).hasDerivWithinAt
    · intro t ht
      have hUpper : (f' (γ t) - f' x) v ≤ L * t * ‖v‖ ^ 2 := (abs_le.mp (hEval_bound t ht)).2
      linarith
  have hr_antitone : AntitoneOn r (Set.Icc (0 : ℝ) 1) := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (0 : ℝ) 1)
        (f := r)
        (f' := fun t => (-(f' (γ t) - f' x) v) - L * t * ‖v‖ ^ 2)
        (convex_Icc (0 : ℝ) 1)
        hr_cont.continuousOn
        ?_
        ?_
    · intro t ht
      exact (hr_deriv t).hasDerivWithinAt
    · intro t ht
      have hLower : -(L * t * ‖v‖ ^ 2) ≤ (f' (γ t) - f' x) v := (abs_le.mp (hEval_bound t ht)).1
      linarith
  have hq10 : q 1 ≤ q 0 := by
    exact hq_antitone (by norm_num) (by norm_num) (by norm_num)
  have hr10 : r 1 ≤ r 0 := by
    exact hr_antitone (by norm_num) (by norm_num) (by norm_num)
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

end GeneralNormDescent

section DualPairBridge

variable {V VDual : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup VDual] [NormedSpace ℝ VDual]

/--
Descent lemma under an arbitrary norm / dual-norm setup, once the dual
pairing is realized as a continuous linear functional map.
-/
theorem taylor_bound_of_LSmoothUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : GlobalLipschitzUnderNormPair grad L) :
    ∀ x y,
      |f y - (f x + P.toLinear (grad x) (y - x))| ≤
        (L / 2) * ‖y - x‖ ^ 2 := by
  have _ : 0 ≤ L := hLipschitz.nonneg
  refine
    taylor_bound_of_lipschitz_fderiv
      (f := f) (f' := fun x => P.toLinear (grad x)) hf ?_
  intro x y
  calc
    ‖P.toLinear (grad y) - P.toLinear (grad x)‖ ≤ ‖grad y - grad x‖ :=
      P.opNorm_sub_le (grad x) (grad y)
    _ ≤ L * ‖y - x‖ := hLipschitz.bound x y

/--
Local descent lemma under an arbitrary norm / dual-norm setup on a
convex region.
-/
theorem taylor_bound_of_LSmoothOnConvexSetUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L : ℝ} {s : Set V}
    (hs : Convex ℝ s)
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : ∀ x ∈ s, ∀ y ∈ s, ‖grad y - grad x‖ ≤ L * ‖y - x‖)
    {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    |f y - (f x + P.toLinear (grad x) (y - x))| ≤
      (L / 2) * ‖y - x‖ ^ 2 := by
  refine
    taylor_bound_of_lipschitz_fderiv_on_convex
      (f := f) (f' := fun x => P.toLinear (grad x))
      hs hf ?_ hx hy
  intro x hx y hy
  calc
    ‖P.toLinear (grad y) - P.toLinear (grad x)‖ ≤ ‖grad y - grad x‖ :=
      P.opNorm_sub_le (grad x) (grad y)
    _ ≤ L * ‖y - x‖ := hLipschitz x hx y hy

/--
Closed-ball specialization of the local dual-pairing descent lemma, matching
the local Assumption-4 formulation.
-/
theorem taylor_bound_of_LSmoothOnClosedBallUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L R : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    {x y : V} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |f y - (f x + P.toLinear (grad x) (y - x))| ≤
      (L / 2) * ‖y - x‖ ^ 2 := by
  refine
    taylor_bound_of_LSmoothOnConvexSetUnderPair
      P
      (s := Metric.closedBall (0 : V) R)
      (convex_closedBall (0 : V) R)
      hf
      ?_
      ?_
      ?_
  · intro x _ y _
    exact
      hLipschitz.bound
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using ‹x ∈ Metric.closedBall (0 : V) R›)
        (by simpa [Metric.mem_closedBall, dist_eq_norm] using ‹y ∈ Metric.closedBall (0 : V) R›)
  · simpa [mem_closedBall_zero_iff] using hx
  · simpa [mem_closedBall_zero_iff] using hy

/-- One-sided descent-lemma form derived from `taylor_bound_of_LSmoothUnderPair`. -/
theorem taylor_upper_of_LSmoothUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : GlobalLipschitzUnderNormPair grad L) :
    ∀ x y,
      f y ≤ f x + P.toLinear (grad x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  have h := taylor_bound_of_LSmoothUnderPair P hf hLipschitz x y
  have hUpper := (abs_le.mp h).2
  linarith

/-- Comparison form derived from `taylor_bound_of_LSmoothUnderPair`. -/
theorem taylor_compare_of_LSmoothUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : GlobalLipschitzUnderNormPair grad L) :
    ∀ x y,
      f x + P.toLinear (grad x) (y - x) ≤ f y + (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  have h := taylor_bound_of_LSmoothUnderPair P hf hLipschitz x y
  have hLower := (abs_le.mp h).1
  linarith

/--
One-step descent-lemma form specialized to a nonnegative scaled increment
`α • ξ`. This is the exact analytic inequality used in Lemma 5.
-/
theorem step_upper_of_LSmoothUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L α : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : GlobalLipschitzUnderNormPair grad L)
    (hα_nonneg : 0 ≤ α) :
    ∀ x ξ,
      f (x + α • ξ) ≤
        f x + α * P.toLinear (grad x) ξ + (L / 2) * α ^ 2 * ‖ξ‖ ^ 2 := by
  intro x ξ
  have h :=
    taylor_upper_of_LSmoothUnderPair
      P
      (f := f)
      (grad := grad)
      (L := L)
      hf
      hLipschitz
      x
      (x + α • ξ)
  have hStep : x + α • ξ - x = α • ξ := by
    abel_nf
  rw [hStep, ContinuousLinearMap.map_smul, norm_smul, Real.norm_of_nonneg hα_nonneg] at h
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

/--
Local one-step descent lemma on the Assumption-4 closed noise ball.
-/
theorem step_upper_of_LSmoothOnClosedBallUnderPair
    (P : ContinuousDualPairingContext V VDual)
    {f : V → ℝ} {grad : V → VDual} {L R α : ℝ}
    (hf : ∀ x, HasFDerivAt f (P.toLinear (grad x)) x)
    (hLipschitz : LocalLipschitzOnClosedBallUnderNormPair grad R L)
    (hα_nonneg : 0 ≤ α)
    {x ξ : V} (hx : ‖x‖ ≤ R) (hNext : ‖x + α • ξ‖ ≤ R) :
    f (x + α • ξ) ≤
      f x + α * P.toLinear (grad x) ξ + (L / 2) * α ^ 2 * ‖ξ‖ ^ 2 := by
  have h :=
    taylor_bound_of_LSmoothOnClosedBallUnderPair
      P
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
      f (x + α • ξ) - f x - α * P.toLinear (grad x) ξ ≤
        (L / 2) * (α * ‖ξ‖) ^ 2 := by
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hUpper
  have hUpper' :
      f (x + α • ξ) - f x - α * P.toLinear (grad x) ξ ≤
        L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
    have hEq : (L / 2) * (α * ‖ξ‖) ^ 2 = L * α ^ 2 * ‖ξ‖ ^ 2 * (1 / 2) := by
      ring
    rw [hEq] at hUpper''
    exact hUpper''
  linarith

end DualPairBridge

end

end SteepestDescentOptimizationBounds
