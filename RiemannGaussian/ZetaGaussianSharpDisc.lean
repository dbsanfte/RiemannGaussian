/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianSharpStrip

/-!
# The actual Gaussian reconstruction cost on the full local disc

The retained real quadratics cancel in the original zeta reconstruction.
The remaining allowance is the actual vertical shift square, the disc
radius squared, and the rational normalization at its true height. It
is uniformly at most two, in place of the earlier blanket constant.
-/

namespace RiemannGaussian.ZetaGaussianSharpDisc
noncomputable section
open Complex Metric Set ZetaGaussianLocalizer ZetaNearOneLocalDisc
open ZetaNearOneLogProfile DirichletPowerParameters DerivativeOrderComparison

/-- The complete reconstruction cost, retaining its actual height,
disc radius and rational normalization. -/
def correction (k : ℕ) (t : ℝ) : ℝ :=
  ZetaGaussianSharpStrip.correction t + (delta k) ^ 2 +
    Real.log (1 + 2 / (|t| - delta k))

/-- The rational normalization pays its actual distance from height
zero, without a uniform bound on the numerator's real coordinate. -/
theorem inverse_ratio_le {s : ℂ} {v : ℝ} (hv : 0 < v) (hs : v ≤ |s.im|) :
    ‖(s + 1) / (s - 1)‖ ≤ 1 + 2 / v := by
  have hden : v ≤ ‖s - 1‖ := hs.trans (by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1))
  have hp : 0 < ‖s - 1‖ := hv.trans_le hden
  have hnum : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
    have h := norm_add_le (s - 1) (2 : ℂ)
    simpa only [show s - 1 + (2 : ℂ) = s + 1 by ring, Complex.norm_ofNat] using h
  rw [norm_div]
  calc
    ‖s + 1‖ / ‖s - 1‖ ≤ (‖s - 1‖ + 2) / ‖s - 1‖ :=
      div_le_div_of_nonneg_right hnum hp.le
    _ = 1 + 2 / ‖s - 1‖ := by field_simp
    _ ≤ 1 + 2 / v := add_le_add_right
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hv hden) 1

/-- The retained Gaussian exponent cancels the left boundary's real
quadratic throughout the full actual zeta disc. -/
theorem norm_zeta_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4) {s : ℂ}
    (hs : s ∈ closedBall (center x t) (delta k)) :
    ‖riemannZeta s‖ ≤ Real.exp (profile k t + correction k t) := by
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
  have hratio := inverse_ratio_le hv hy
  have hbase := ZetaGaussianSharpStrip.carrier_bound k (by omega) t hlo hhi
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
    _ = Real.exp (profile k t + (line k) ^ 2 + ZetaGaussianSharpStrip.correction t +
        ((s.im - t) ^ 2 - s.re ^ 2) + Real.log (1 + 2 / (|t| - delta k))) := by
      symm
      rw [Real.exp_add, Real.exp_log hratpos, Real.exp_add]
    _ ≤ Real.exp (profile k t + correction k t) := by
      apply Real.exp_le_exp.mpr
      unfold correction
      linarith

/-- The entire reconstruction correction is nonnegative and at most
two on every eligible full disc, with no asymptotic assumption. -/
theorem correction_bounds (k : ℕ) (hk : 2 ≤ k) {t : ℝ} (ht : 2 ≤ |t|) :
    0 ≤ correction k t ∧ correction k t ≤ 2 := by
  have hd := ZetaNearOneFullDisc.delta_le_two_sevenths hk
  have hδ := delta_pos k
  have hv : 0 < |t| - delta k := by linarith
  have hH : 4 ≤ height t := by unfold height; linarith
  have hq : 3 / height t ≤ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hH
  have hq2 := pow_le_pow_left₀ (by positivity : 0 ≤ 3 / height t) hq 2
  have hd2 := pow_le_pow_left₀ hδ.le hd 2
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 / (|t| - delta k) by positivity)
  have hi : 2 / (|t| - delta k) ≤ (7 / 6 : ℝ) := by
    apply (div_le_iff₀ hv).mpr
    linarith
  have hlog : 0 ≤ Real.log (1 + 2 / (|t| - delta k)) := by
    apply Real.log_nonneg
    have h : 0 ≤ 2 / (|t| - delta k) := by positivity
    linarith
  constructor
  · unfold correction ZetaGaussianSharpStrip.correction
    positivity
  · unfold correction ZetaGaussianSharpStrip.correction
    nlinarith

/-- The full translated disc inherits the sharper actual norm bound,
including possible zeros on its outer sphere. -/
theorem norm_translated_le (k : ℕ) (hk : 2 ≤ k) {t x : ℝ}
    (ht : 2 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta k / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta k)) :
    ‖ZetaNearOneCanonical.translated x t z‖ ≤ Real.exp (profile k t + correction k t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta k) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  exact norm_zeta_le k hk ht hx hx' hm

end
end RiemannGaussian.ZetaGaussianSharpDisc
