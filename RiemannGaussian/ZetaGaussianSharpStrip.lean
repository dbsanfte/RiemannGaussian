/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneFullDisc

/-!
# Retaining the exact Gaussian quadratic in strip propagation

The real quadratic contribution of the Gaussian is kept at the left
boundary. Completing one square pays the actual height-dependent shift
cost. The right boundary is already below the same allowance, so no
extra constant is added when propagating across the strip.
-/

namespace RiemannGaussian.ZetaGaussianSharpStrip
noncomputable section
open Complex Set ZetaGaussianLocalizer ZetaGaussianStrip ZetaNearOneLogProfile
open ZetaLogarithmicShiftAllowance DirichletPowerParameters DerivativeOrderComparison
open DerivativePowerExponents

/-- The complete vertical shift cost after exact Gaussian square
completion. It decreases quadratically in the actual central height. -/
def correction (t : ℝ) : ℝ := (3 / height t) ^ 2 / 4

/-- The given line majorant already dominates the fixed safe-line
allowance. This uses its actual coefficient rather than only positivity. -/
theorem profile_ge_seven (k : ℕ) (t : ℝ) : 7 ≤ profile k t := by
  have hH := two_le_height t
  have hδ := delta_pos k
  have hc : (32768 : ℝ) ≤ 32768 / delta k := by
    apply (le_div_iff₀ hδ).mpr
    have hd : delta k ≤ 1 := order_mul_alpha_le_one k
    nlinarith
  have hp : 1 ≤ height t ^ alpha k :=
    Real.one_le_rpow (by linarith) (alpha_pos k).le
  have hl : (1 / 2 : ℝ) ≤ Real.log (height t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hH
    linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 32768 / delta k by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ Real.log (height t) by linarith)
  have h3 := mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.log (height t) by linarith)
  have hmajor : (16384 : ℝ) ≤
      32768 / delta k * height t ^ alpha k * Real.log (height t) := by nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16384) hmajor
  rw [← profile_eq_log] at hlog
  have he : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
    rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]
    norm_num
  rw [he] at hlog
  linarith [Real.log_two_gt_d9]

/-- The exact left-boundary quadratic survives completion of the
vertical shift square; its remainder has no fixed additive loss. -/
theorem left_boundary (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ} (hs : s.re = line k) :
    ‖carrier t s‖ ≤ Real.exp (profile k t + (line k) ^ 2 + correction t) := by
  have hlo : 0 ≤ s.re := by rw [hs]; linarith [half_le_line k hk]
  have hhi : s.re < 1 := by rw [hs]; exact line_lt_one k
  have hs1 : s ≠ 1 := by intro h; simp [h] at hhi
  have hshift := profile_shift_le k t 1 (s.im - t)
  simp only [one_mul, add_sub_cancel] at hshift
  have hnorm := (norm_regularized_le_zeta hlo hs1).trans (norm_zeta_le_exp_profile k hk hs)
  rw [norm_carrier]
  have hm := mul_le_mul_of_nonneg_right
    (hnorm.trans (Real.exp_le_exp.mpr hshift)) (Real.exp_pos (s.re ^ 2 - (s.im - t) ^ 2)).le
  apply hm.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc := shiftCost_le k t 1
  simp only [abs_one, mul_one] at hc
  have hmul := mul_le_mul_of_nonneg_right hc (abs_nonneg (s.im - t))
  have hsquare : |s.im - t| ^ 2 = (s.im - t) ^ 2 := sq_abs _
  rw [hs]
  unfold correction
  nlinarith [sq_nonneg (2 * |s.im - t| - 3 / height t)]

/-- Both boundary lines obey the same sharp actual allowance. The
right line contributes no additional logarithmic constant. -/
theorem carrier_bound (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖carrier t s‖ ≤ Real.exp (profile k t + (line k) ^ 2 + correction t) := by
  apply PhragmenLindelof.vertical_strip (diffContOnCl_carrier k hk t)
    (carrier_growth k hk t) _ _ hlo hhi
  · intro w hw
    exact left_boundary k hk t hw
  · intro w hw
    apply (right_boundary t hw).trans
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he : (8 : ℝ) ≤ Real.exp 3 := by
      calc
        (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) htwo 3
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    calc
      8 * Real.exp 3 ≤ Real.exp 3 * Real.exp 3 :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp 6 := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp (profile k t + (line k) ^ 2 + correction t) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ correction t := by unfold correction; positivity
        nlinarith [profile_ge_seven k t, sq_nonneg (line k)]

end
end RiemannGaussian.ZetaGaussianSharpStrip
