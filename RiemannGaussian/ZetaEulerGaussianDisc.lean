/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerLogProfile
import RiemannGaussian.ZetaGaussianSharpDisc

/-!
# Direct Euler growth through the complete Gaussian strip and disc

Pole clearing retains the uniform Euler growth bound over the entire
vertical boundary. The original Gaussian square, radius, inverse factor
and possible boundary zeros are unchanged. The full disc now receives
an allowance independent of the former eta division cost.
-/

namespace RiemannGaussian.ZetaEulerGaussianDisc
noncomputable section
open Complex Metric Set ZetaGaussianLocalizer ZetaGaussianStrip
open ZetaNearOneLocalDisc ZetaNearOneLogProfile ZetaLogarithmicShiftAllowance
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison

/-- The exact left-boundary quadratic survives completion of the
vertical shift square; its remainder has no fixed additive loss. -/
theorem left_boundary (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ} (hs : s.re = line k) :
    ‖carrier t s‖ ≤ Real.exp (ZetaEulerLogProfile.profile k t + (line k) ^ 2 + ZetaGaussianSharpStrip.correction t) := by
  have hshift := ZetaEulerLogProfile.profile_shift_le k t 1 (s.im - t)
  simp only [one_mul, add_sub_cancel] at hshift
  have hnorm := ZetaEulerLogProfile.regularized_le_exp_profile k hk hs
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
  unfold ZetaGaussianSharpStrip.correction
  nlinarith [sq_nonneg (2 * |s.im - t| - 3 / height t)]

/-- Both boundary lines obey the same sharp actual allowance. The
right line contributes no additional logarithmic constant. -/
theorem carrier_bound (k : ℕ) (hk : 1 ≤ k) (t : ℝ) {s : ℂ}
    (hlo : line k ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖carrier t s‖ ≤ Real.exp (ZetaEulerLogProfile.profile k t + (line k) ^ 2 + ZetaGaussianSharpStrip.correction t) := by
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
      _ ≤ Real.exp (ZetaEulerLogProfile.profile k t + (line k) ^ 2 + ZetaGaussianSharpStrip.correction t) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ ZetaGaussianSharpStrip.correction t := by unfold ZetaGaussianSharpStrip.correction; positivity
        nlinarith [ZetaEulerLogProfile.profile_ge_six k t, sq_nonneg (line k)]

/-- The retained Gaussian exponent cancels the left boundary's real
quadratic throughout the full actual zeta disc. -/
theorem norm_zeta_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k)) :
    ‖riemannZeta s‖ ≤ Real.exp (ZetaEulerLogProfile.profile k t + ZetaGaussianSharpDisc.correction k t) := by
  obtain ⟨hlo, hhi, hwindow⟩ := ZetaNearOneFullDisc.disc_geometry k hk t hx hx' hs
  have hn : ‖s - center x t‖ ≤ delta k := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have him : |s.im - t| ≤ delta k := by
    have h := (Complex.abs_im_le_norm (s - center x t)).trans hn
    simpa [ZetaNearOneLocalDisc.center] using h
  have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
  have hv : 0 < |t| - delta k := by linarith
  have hy : |t| - delta k ≤ |s.im| := by
    have h : |t| ≤ |s.im| + |s.im - t| := by
      calc
        |t| = |s.im + (t - s.im)| := by congr 1; ring
        _ ≤ |s.im| + |t - s.im| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm t s.im]
    linarith
  have hratio := ZetaGaussianSharpDisc.inverse_ratio_le hv hy
  have hbase := carrier_bound k (by omega) t hlo hhi
  have hinverse : ‖Complex.exp (-((s - Complex.I * (t : ℂ)) ^ 2))‖ =
      Real.exp ((s.im - t) ^ 2 - s.re ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, one_mul, sub_zero, zero_add]
    ring
  have hσ : 0 ≤ line k := by linarith [half_le_line k (by omega : 1 ≤ k)]
  have hre2 := pow_le_pow_left₀ hσ hlo 2
  have him2 : (s.im - t) ^ 2 ≤ (delta k) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (s.im - t)) him 2
    simpa only [sq_abs] using h
  rw [reconstruction t (ne_one_of_window ht hwindow)
    (add_one_ne_zero (hσ.trans hlo)), norm_mul, norm_mul, hinverse]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hbase
    (Real.exp_pos ((s.im - t) ^ 2 - s.re ^ 2)).le) hratio (norm_nonneg _)
    (by positivity)
  apply hm.trans
  have hratpos : 0 < 1 + 2 / (|t| - delta k) := by positivity
  calc
    _ = Real.exp (ZetaEulerLogProfile.profile k t + (line k) ^ 2 + ZetaGaussianSharpStrip.correction t +
        ((s.im - t) ^ 2 - s.re ^ 2) + Real.log (1 + 2 / (|t| - delta k))) := by
      symm
      rw [Real.exp_add, Real.exp_log hratpos, Real.exp_add]
    _ ≤ Real.exp (ZetaEulerLogProfile.profile k t + ZetaGaussianSharpDisc.correction k t) := by
      apply Real.exp_le_exp.mpr
      unfold ZetaGaussianSharpDisc.correction
      linarith

/-- The full translated disc inherits the sharper actual norm bound,
including possible zeros on its outer sphere. -/
theorem norm_translated_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta k)) :
    ‖ZetaNearOneCanonical.translated x t z‖ ≤ Real.exp (ZetaEulerLogProfile.profile k t + ZetaGaussianSharpDisc.correction k t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta k) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  exact norm_zeta_le k hk ht hx hx' hm

end
end RiemannGaussian.ZetaEulerGaussianDisc
