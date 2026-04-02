import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic

open scoped BigOperators

namespace SteepestDescentOptimizationBounds

noncomputable section

/-! ------------------------------------------------------------------------
Public Definitions
------------------------------------------------------------------------ -/

/-- Tail weight `W(k) = ∑_{t=k}^n w_t`. -/
def tailWeight (w : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc k n, w t

/-- Tail numerator `N(k) = ∑_{t=k}^n w_t q_t`. -/
def tailNumerator (w q : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc k n, w t * q t

/-- Tail average `A(k) = N(k) / W(k)`. -/
def tailAvg (w q : ℕ → ℝ) (k n : ℕ) : ℝ :=
  tailNumerator w q k n / tailWeight w k n

/-! ------------------------------------------------------------------------
Private Lemmas and Theorems
------------------------------------------------------------------------ -/

private theorem tailWeight_step
    (w : ℕ → ℝ) {k n : ℕ} (hk : k < n) :
    tailWeight w k n = w k + tailWeight w (k + 1) n := by
  have hIcc :
      insert k (Finset.Icc (k + 1) n) = Finset.Icc k n := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := k) (b := n) (Nat.le_of_lt hk))
  have hk_not_mem : k ∉ Finset.Icc (k + 1) n := by
    simp
  calc
    tailWeight w k n = ∑ t ∈ insert k (Finset.Icc (k + 1) n), w t := by
      rw [tailWeight, ← hIcc]
    _ = w k + ∑ t ∈ Finset.Icc (k + 1) n, w t := by
      rw [Finset.sum_insert hk_not_mem]
    _ = w k + tailWeight w (k + 1) n := by
      rw [tailWeight]

private theorem tailNumerator_step
    (w q : ℕ → ℝ) {k n : ℕ} (hk : k < n) :
    tailNumerator w q k n = w k * q k + tailNumerator w q (k + 1) n := by
  have hIcc :
      insert k (Finset.Icc (k + 1) n) = Finset.Icc k n := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := k) (b := n) (Nat.le_of_lt hk))
  have hk_not_mem : k ∉ Finset.Icc (k + 1) n := by
    simp
  calc
    tailNumerator w q k n =
        ∑ t ∈ insert k (Finset.Icc (k + 1) n), w t * q t := by
      rw [tailNumerator, ← hIcc]
    _ = w k * q k + ∑ t ∈ Finset.Icc (k + 1) n, w t * q t := by
      rw [Finset.sum_insert hk_not_mem]
    _ = w k * q k + tailNumerator w q (k + 1) n := by
      rw [tailNumerator]

private theorem tailWeight_mul_tailAvg_eq_tailNumerator
    (w q : ℕ → ℝ) {k n : ℕ} (hW : tailWeight w k n ≠ 0) :
    tailWeight w k n * tailAvg w q k n = tailNumerator w q k n := by
  unfold tailAvg
  field_simp [hW]

private theorem tailAvg_sub_anchor_eq
    (w q : ℕ → ℝ) {k n : ℕ} (_hk : k ≤ n) (hW : tailWeight w k n ≠ 0) :
    tailAvg w q k n - q k =
      (1 / tailWeight w k n) * ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
  have hExpand :
      tailNumerator w q k n - q k * tailWeight w k n =
        ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
    rw [tailNumerator, tailWeight]
    have hMul :
        q k * ∑ t ∈ Finset.Icc k n, w t =
          ∑ t ∈ Finset.Icc k n, q k * w t := by
      rw [Finset.mul_sum]
    rw [hMul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  calc
    tailAvg w q k n - q k =
        (tailNumerator w q k n - q k * tailWeight w k n) / tailWeight w k n := by
      unfold tailAvg
      field_simp [hW]
    _ = (∑ t ∈ Finset.Icc k n, w t * (q t - q k)) / tailWeight w k n := by
      rw [hExpand]
    _ = (1 / tailWeight w k n) * ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
      rw [div_eq_mul_inv, one_div, mul_comm]

private theorem tailWeight_coefficient_identity
    (w : ℕ → ℝ) {k n : ℕ} (hk : k < n)
    (hWk : tailWeight w k n ≠ 0) (hWk1 : tailWeight w (k + 1) n ≠ 0) :
    w k / (tailWeight w k n * tailWeight w (k + 1) n) =
      (1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n) := by
  have hStep := tailWeight_step w hk
  field_simp [hWk, hWk1]
  linarith

private theorem tailAvg_step_recurrence_anchor
    (w q : ℕ → ℝ) {k n : ℕ} (hk : k < n)
    (hWk : tailWeight w k n ≠ 0) (hWk1 : tailWeight w (k + 1) n ≠ 0) :
    tailAvg w q (k + 1) n =
      tailAvg w q k n +
        (w k / tailWeight w (k + 1) n) * (tailAvg w q k n - q k) := by
  have hNum :
      tailNumerator w q (k + 1) n = tailNumerator w q k n - w k * q k := by
    linarith [tailNumerator_step w q hk]
  calc
    tailAvg w q (k + 1) n =
        (tailNumerator w q k n - w k * q k) / tailWeight w (k + 1) n := by
      rw [tailAvg, hNum]
    _ =
        (tailWeight w k n * tailAvg w q k n - w k * q k) / tailWeight w (k + 1) n := by
      rw [tailWeight_mul_tailAvg_eq_tailNumerator (w := w) (q := q) (k := k) (n := n) hWk]
    _ =
        ((w k + tailWeight w (k + 1) n) * tailAvg w q k n - w k * q k) /
          tailWeight w (k + 1) n := by
      rw [tailWeight_step w hk]
    _ = tailAvg w q k n +
        (w k / tailWeight w (k + 1) n) * (tailAvg w q k n - q k) := by
      field_simp [hWk1]
      ring

private theorem tailAvg_step_recurrence_precoeff
    (w q : ℕ → ℝ) {k n : ℕ} (hk : k < n)
    (hWk : tailWeight w k n ≠ 0) (hWk1 : tailWeight w (k + 1) n ≠ 0) :
    tailAvg w q (k + 1) n =
      tailAvg w q k n +
        (w k / (tailWeight w k n * tailWeight w (k + 1) n)) *
          ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
  have hAnchor := tailAvg_sub_anchor_eq (w := w) (q := q) (k := k) (n := n) (Nat.le_of_lt hk) hWk
  calc
    tailAvg w q (k + 1) n =
        tailAvg w q k n +
          (w k / tailWeight w (k + 1) n) * (tailAvg w q k n - q k) := by
      exact tailAvg_step_recurrence_anchor (w := w) (q := q) hk hWk hWk1
    _ =
        tailAvg w q k n +
          (w k / tailWeight w (k + 1) n) *
            ((1 / tailWeight w k n) * ∑ t ∈ Finset.Icc k n, w t * (q t - q k)) := by
      rw [hAnchor]
    _ =
        tailAvg w q k n +
          (w k / (tailWeight w k n * tailWeight w (k + 1) n)) *
            ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
      field_simp [hWk, hWk1]

private theorem tailAvg_one_step_recurrence
    (w q : ℕ → ℝ) {k n : ℕ} (hk : k < n)
    (hWk : tailWeight w k n ≠ 0) (hWk1 : tailWeight w (k + 1) n ≠ 0) :
    tailAvg w q (k + 1) n - tailAvg w q k n =
      ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
        ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
  calc
    tailAvg w q (k + 1) n - tailAvg w q k n =
        (w k / (tailWeight w k n * tailWeight w (k + 1) n)) *
          ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
      rw [tailAvg_step_recurrence_precoeff (w := w) (q := q) hk hWk hWk1]
      ring
    _ =
        ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
          ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
      rw [tailWeight_coefficient_identity (w := w) hk hWk hWk1]

private theorem tailAvg_range_telescope
    (A : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (A (k + 1) - A k) = A n - A 0 := by
  simpa using Finset.sum_range_sub A n

private theorem tailAvg_self
    (w q : ℕ → ℝ) (n : ℕ) (hW : tailWeight w n n ≠ 0) :
    tailAvg w q n n = q n := by
  have hw : w n ≠ 0 := by
    simpa [tailWeight] using hW
  simpa [tailAvg, tailNumerator, tailWeight, mul_comm, mul_left_comm, mul_assoc] using
    (mul_div_cancel_left₀ (q n) hw)

/-! ------------------------------------------------------------------------
Public Theorems
------------------------------------------------------------------------ -/

/--
Pure weighted last-iterate identity in 0-based tail-average form.

This theorem is purely algebraic: the only hypothesis is that every tail
denominator that appears is nonzero.
-/
theorem weighted_lastIterate_identity
    (w q : ℕ → ℝ) (n : ℕ)
    (hTail : ∀ k, k ≤ n → tailWeight w k n ≠ 0) :
    q n =
      tailAvg w q 0 n +
        ∑ k ∈ Finset.range n,
          ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
            ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
  have hTel :
      ∑ k ∈ Finset.range n,
        ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
          ∑ t ∈ Finset.Icc k n, w t * (q t - q k) =
        tailAvg w q n n - tailAvg w q 0 n := by
    calc
      ∑ k ∈ Finset.range n,
          ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
            ∑ t ∈ Finset.Icc k n, w t * (q t - q k) =
          ∑ k ∈ Finset.range n, (tailAvg w q (k + 1) n - tailAvg w q k n) := by
        apply Finset.sum_congr rfl
        intro k hk
        symm
        exact tailAvg_one_step_recurrence
          (w := w) (q := q) (k := k) (n := n)
          (Finset.mem_range.mp hk)
          (hTail k (Nat.le_of_lt (Finset.mem_range.mp hk)))
          (hTail (k + 1) (Finset.mem_range.mp hk))
      _ = tailAvg w q n n - tailAvg w q 0 n := by
        simpa using tailAvg_range_telescope (A := fun k => tailAvg w q k n) n
  have hEnd : tailAvg w q n n = q n :=
    tailAvg_self (w := w) (q := q) n (hTail n le_rfl)
  have hAssemble :
      tailAvg w q n n =
        tailAvg w q 0 n +
          ∑ k ∈ Finset.range n,
            ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
              ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
    linarith
  calc
    q n = tailAvg w q n n := by simpa using hEnd.symm
    _ =
        tailAvg w q 0 n +
          ∑ k ∈ Finset.range n,
            ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
              ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
      exact hAssemble

/--
Convenience wrapper: strict positivity of the weights implies the nonvanishing
tail-sum hypothesis used by `weighted_lastIterate_identity`.
-/
theorem weighted_lastIterate_identity_of_positive_weights
    (w q : ℕ → ℝ) (n : ℕ)
    (hPos : ∀ t, t ≤ n → 0 < w t) :
    q n =
      tailAvg w q 0 n +
        ∑ k ∈ Finset.range n,
          ((1 / tailWeight w (k + 1) n) - (1 / tailWeight w k n)) *
            ∑ t ∈ Finset.Icc k n, w t * (q t - q k) := by
  apply weighted_lastIterate_identity (w := w) (q := q) (n := n)
  intro k hk
  have hk_mem : k ∈ Finset.Icc k n := by
    simp [hk]
  have hNonneg : ∀ t ∈ Finset.Icc k n, 0 ≤ w t := by
    intro t ht
    exact le_of_lt (hPos t (Finset.mem_Icc.mp ht).2)
  have hwk : 0 < w k := hPos k hk
  have hle : w k ≤ tailWeight w k n := by
    unfold tailWeight
    exact Finset.single_le_sum hNonneg hk_mem
  exact ne_of_gt (lt_of_lt_of_le hwk hle)

end

end SteepestDescentOptimizationBounds
