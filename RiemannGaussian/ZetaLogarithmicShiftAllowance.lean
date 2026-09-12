/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneLogProfile

/-!
# A complete affine allowance for vertical logarithmic shifts

Two logarithmic tangent inequalities control every shifted ordinate by
the central profile and an explicit absolute first-moment cost. There
is no local window or unestimated far-height branch in this comparison.
-/

namespace RiemannGaussian.ZetaLogarithmicShiftAllowance
noncomputable section
open DerivativePowerExponents ZetaNearOneLogProfile

/-- The logarithm lies below its exact tangent at every positive base. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have he : (y - x) / x = y / x - 1 := by field_simp
  rw [he]
  linarith

/-- The enlarged height retains the central ordinate and the complete
absolute shift, including points crossing height zero. -/
theorem height_shift_le (t a u : ℝ) : height (t + a * u) ≤ height t + |a| * |u| := by
  have h := abs_add_le t (a * u)
  rw [abs_mul] at h
  unfold height
  linarith

/-- The explicit first-moment price for a vertical shift at the chosen
order and central height. -/
def shiftCost (k : ℕ) (t a : ℝ) : ℝ :=
  (alpha k + (Real.log (height t))⁻¹) * |a| / height t

/-- Every shift has a nonnegative first-moment cost. -/
theorem shiftCost_nonneg (k : ℕ) (t a : ℝ) : 0 ≤ shiftCost k t a := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  have ha := alpha_pos k
  unfold shiftCost
  positivity

/-- The shift cost is uniformly small at large central height, with
no dependence on the derivative order. -/
theorem shiftCost_le (k : ℕ) (t a : ℝ) : shiftCost k t a ≤ 3 * |a| / height t := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : (1 / 2 : ℝ) ≤ Real.log (height t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (two_le_height t)
    linarith [Real.log_two_gt_d9]
  have hi : (Real.log (height t))⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hl
    norm_num only [one_div, inv_div, inv_one, mul_one] at h
    exact h
  unfold shiftCost
  apply div_le_div_of_nonneg_right _ hh.le
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
  linarith [alpha_le_half k]

/-- Both height logarithms have a simultaneous affine bound over the
whole shifted vertical line, retaining all order and scale dependence. -/
theorem profile_shift_le (k : ℕ) (t a u : ℝ) :
    profile k (t + a * u) ≤ profile k t + shiftCost k t a * |u| := by
  have ht : 0 < height t := by linarith [two_le_height t]
  have hu : 0 < height (t + a * u) := by linarith [two_le_height (t + a * u)]
  have hlt : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  have hlu : 0 < Real.log (height (t + a * u)) :=
    Real.log_pos (by linarith [two_le_height (t + a * u)])
  let q : ℝ := |a| * |u| / height t
  have hheight : (height (t + a * u) - height t) / height t ≤ q := by
    apply div_le_div_of_nonneg_right _ ht.le
    linarith [height_shift_le t a u]
  have hl : Real.log (height (t + a * u)) ≤ Real.log (height t) + q := by
    linarith [log_le_tangent ht hu]
  have hd : (Real.log (height (t + a * u)) - Real.log (height t)) /
      Real.log (height t) ≤ q / Real.log (height t) := by
    apply div_le_div_of_nonneg_right _ hlt.le
    linarith
  have hll : Real.log (Real.log (height (t + a * u))) ≤
      Real.log (Real.log (height t)) + q / Real.log (height t) := by
    linarith [log_le_tangent hlt hlu]
  have hm := mul_le_mul_of_nonneg_left hl (alpha_pos k).le
  calc
    _ ≤ Real.log (32768 / DerivativeOrderComparison.delta k) +
        alpha k * (Real.log (height t) + q) +
        (Real.log (Real.log (height t)) + q / Real.log (height t)) := by
      unfold profile
      linarith
    _ = _ := by unfold profile shiftCost; dsimp [q]; ring

/-- The actual positive-log zeta carrier satisfies the complete affine
vertical allowance at every real shift. -/
theorem positiveLog_shift_le (k : ℕ) (hk : 1 ≤ k) (t a u : ℝ) :
    positiveLog k (t + a * u) ≤ profile k t + shiftCost k t a * |u| :=
  (positiveLog_le k hk (t + a * u)).trans (profile_shift_le k t a u)

end
end RiemannGaussian.ZetaLogarithmicShiftAllowance
