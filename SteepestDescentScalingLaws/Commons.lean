import SteepestDescentOptimizationBounds.StarConvex

/-!
Common asymptotic and algebraic lemmas for the scaling-law modules.

Upstream: `SteepestDescentOptimizationBounds.StarConvex` and the shared
optimization-bounds layer.
Downstream: all star-convex and Frank-Wolfe scaling-law theorem files.
-/

namespace SteepestDescentOptimizationBounds

noncomputable section

variable {Ω V : Type*}
variable [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
variable [SecondCountableTopology (StrongDual ℝ V)] [CompleteSpace (StrongDual ℝ V)]

/-! ------------------------------------------------------------------------
Shared Scaling-Law Helpers
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Private Definitions
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

/-! ------------------------------------------------------------------------
Public Lemmas and Theorems
------------------------------------------------------------------------ -/

theorem eventually_large_log_pos {x x0 : ℝ}
    (hx0 : Real.exp 1 ≤ x0) (hx : x0 ≤ x) : 0 < Real.log x := by
  have hOneLtExp : 1 < Real.exp 1 := by simp
  have hOneLtX : 1 < x := lt_of_lt_of_le hOneLtExp (le_trans hx0 hx)
  exact Real.log_pos hOneLtX

theorem pow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  calc
    x ^ (3 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by norm_num]
      rw [Real.rpow_add' hx]
      norm_num
    _ = x * Real.sqrt x := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

theorem rpow_two_thirds_pow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_mul hx (3 / 2 : ℝ) (2 / 3 : ℝ)]
  norm_num

theorem le_rpow_two_thirds_of_mul_sqrt_le
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x * Real.sqrt x ≤ y) :
    x ≤ y ^ (2 / 3 : ℝ) := by
  have hpow : x ^ (3 / 2 : ℝ) ≤ y := by
    simpa [pow_three_halves_eq_mul_sqrt hx] using hxy
  have h' :=
    Real.rpow_le_rpow (show 0 ≤ x ^ (3 / 2 : ℝ) by positivity) hpow
      (by positivity : 0 ≤ (2 / 3 : ℝ))
  simpa [rpow_two_thirds_pow_three_halves hx] using h'

theorem rpow_two_thirds_le_of_le_mul_sqrt
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≤ x * Real.sqrt x) :
    y ^ (2 / 3 : ℝ) ≤ x := by
  have hpow : y ≤ x ^ (3 / 2 : ℝ) := by
    simpa [pow_three_halves_eq_mul_sqrt hx] using hxy
  have h' := Real.rpow_le_rpow hy hpow (by positivity : 0 ≤ (2 / 3 : ℝ))
  simpa [rpow_two_thirds_pow_three_halves hx] using h'

theorem scale_bounds_of_nonneg
    {c xLower x xUpper : ℝ}
    (hc : 0 ≤ c) (hLower : xLower ≤ x) (hUpper : x ≤ xUpper) :
    c * xLower ≤ c * x ∧ c * x ≤ c * xUpper := by
  constructor
  · exact mul_le_mul_of_nonneg_left hLower hc
  · exact mul_le_mul_of_nonneg_left hUpper hc

theorem mul_bounds_of_nonneg
    {aLower a aUpper bLower b bUpper : ℝ}
    (haLowerNonneg : 0 ≤ aLower) (hbLowerNonneg : 0 ≤ bLower)
    (haLower : aLower ≤ a) (haUpper : a ≤ aUpper)
    (hbLower : bLower ≤ b) (hbUpper : b ≤ bUpper) :
    aLower * bLower ≤ a * b ∧ a * b ≤ aUpper * bUpper := by
  constructor
  · nlinarith [haLowerNonneg, hbLowerNonneg, haLower, hbLower]
  · nlinarith [haLowerNonneg, hbLowerNonneg, haUpper, hbUpper]

theorem le_sqrt_of_nonneg_of_le_one
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ Real.sqrt x := by
  have hxSq : x ^ 2 ≤ x := by nlinarith
  have hSqrtSq : (Real.sqrt x) ^ 2 = x := by
    simpa [sq] using (Real.sq_sqrt hx0)
  have hSqrtNonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith

theorem sqrt_sqrt_eq_rpow_quarter
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = Real.rpow x (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx (1 / 2 : ℝ) (1 / 2 : ℝ)]
  norm_num

theorem reciprocal_linear_eq_min_add_sq
    {a A η ηStar : ℝ}
    (hη : 0 < η)
    (hRel : a = A * ηStar ^ 2) :
    a / η + A * η = 2 * A * ηStar + A * (η - ηStar) ^ 2 / η := by
  field_simp [hη.ne']
  nlinarith [hRel]

theorem reciprocal_linear_value_at_closed_form
    {a A ηStar : ℝ}
    (hEtaStar : 0 < ηStar)
    (hRel : a = A * ηStar ^ 2) :
    a / ηStar + A * ηStar = 2 * A * ηStar := by
  field_simp [hEtaStar.ne']
  nlinarith [hRel]

theorem reciprocal_linear_lt_of_ne
    {a A η ηStar : ℝ}
    (hA : 0 < A) (hη : 0 < η)
    (hRel : a = A * ηStar ^ 2)
    (hNe : η ≠ ηStar) :
    2 * A * ηStar < a / η + A * η := by
  rw [reciprocal_linear_eq_min_add_sq hη hRel]
  have hSq : 0 < (η - ηStar) ^ 2 := by
    exact sq_pos_iff.mpr (sub_ne_zero.mpr hNe)
  have hTerm : 0 < A * (η - ηStar) ^ 2 / η := by
    positivity
  linarith

end

end SteepestDescentOptimizationBounds
