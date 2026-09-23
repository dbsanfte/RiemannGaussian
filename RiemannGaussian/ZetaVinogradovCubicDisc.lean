/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovCubicBound
import RiemannGaussian.ZetaVinogradovFullDisc

/-!
# The full analytic disc retains the cubic growth bound

The strip radius stays Delta_n while the actual height exponent improves
to 40*Delta_n^(3/2). The entire disc and its right-of-one part are paid
above T_(8n)+1. Analyticity, not zero-freeness, is proved on the disc.
-/

namespace RiemannGaussian.ZetaVinogradovCubicDisc
noncomputable section
open Complex Metric Set VinogradovCubicBudget VinogradovScaleSelection
open VinogradovSharperBudget (delta line delta_pos delta_le)
open ZetaNearOneLogProfile (height two_le_height)
open ZetaNearOneLocalDisc (center)
open ZetaNearOneCanonical (translated)

/-- The complete logarithmic profile for the actual high-height bound. -/
def profile (n : ℕ) (t : ℝ) : ℝ :=
  Real.log 8192 + growth n * Real.log (height t) + Real.log (Real.log (height t))

/-- The explicit profile is the logarithm of its positive majorant. -/
theorem profile_eq_log (n : ℕ) (t : ℝ) :
    profile n t = Real.log (8192 * height t ^ growth n * Real.log (height t)) := by
  have hh : 0 < height t := by linarith [two_le_height t]
  have hl : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
  rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 8192)
    (Real.rpow_pos_of_pos hh _)).ne' hl.ne',
    Real.log_mul (by norm_num : (8192 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hh _).ne', Real.log_rpow hh]
  rfl

/-- The complete profile is nonnegative at every ordinate, independently
of the threshold needed to bound zeta by it. -/
theorem profile_nonneg (n : ℕ) (t : ℝ) : 0 ≤ profile n t := by
  have hp : 1 ≤ height t ^ growth n :=
    Real.one_le_rpow (by linarith [two_le_height t]) (growth_pos n).le
  have hl : (1 / 2 : ℝ) ≤ Real.log (height t) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (two_le_height t)
    linarith [Real.log_two_gt_d9]
  rw [profile_eq_log]
  apply Real.log_nonneg
  nlinarith

/-- The actual Vinogradov growth bound extends through the entire
closed strip ending at three halves, with unchanged numerical cost. -/
theorem strip_bound_abs (n : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hlo : line n ≤ s.re) (hhi : s.re ≤ 3 / 2)
    (ht : (heightThreshold (8 * n) : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ growth n * Real.log |s.im| := by
  by_cases hσ : s.re ≤ 1
  · exact ZetaVinogradovCubicBound.bound_strip_abs n hn hlo hσ ht
  · have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
      exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
    have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
    have ht2 : 2 ≤ |s.im| := by linarith
    have hp : 1 ≤ |s.im| ^ growth n :=
      Real.one_le_rpow (by linarith) (growth_pos n).le
    have hl : 0 ≤ Real.log |s.im| := Real.log_nonneg (by linarith)
    have h := ZetaEulerRightStrip.bound_abs (lt_of_not_ge hσ).le hhi ht2
    nlinarith

/-- One physical height unit pays the entire threshold shift on every
point of a height-one local window. -/
theorem local_norm_bound (n : ℕ) (hn : 48 ≤ n) {t : ℝ}
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |t|) {s : ℂ}
    (hlo : line n ≤ s.re) (hhi : s.re ≤ 3 / 2) (hw : |s.im - t| ≤ 1) :
    ‖riemannZeta s‖ ≤ Real.exp (profile n t) := by
  have hreverse : |t| ≤ |s.im| + |s.im - t| := by
    calc
      |t| = |s.im + (t - s.im)| := by congr 1; ring
      _ ≤ |s.im| + |t - s.im| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm t s.im]
  have ht' : (heightThreshold (8 * n) : ℝ) ≤ |s.im| := by linarith
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
  have hpos : 0 < |s.im| := by linarith
  have hupper : |s.im| ≤ height t := by
    have h := abs_add_le (s.im - t) t
    rw [sub_add_cancel] at h
    unfold height
    linarith
  have hp := Real.rpow_le_rpow (abs_nonneg s.im) hupper (growth_pos n).le
  have hl := Real.log_le_log hpos hupper
  have hm := mul_le_mul hp hl (Real.log_nonneg (by linarith : 1 ≤ |s.im|))
    (Real.rpow_nonneg (by linarith [two_le_height t] : 0 ≤ height t) _)
  rw [profile_eq_log, Real.exp_log (by
    have hH : 0 < height t := by linarith [two_le_height t]
    have hlH : 0 < Real.log (height t) := Real.log_pos (by linarith [two_le_height t])
    positivity)]
  apply (strip_bound_abs n hn hlo hhi ht').trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 8192)

/-- The entire radius Delta_n lies inside the proved strip and unit
height window at every eligible Euler-side center. -/
theorem disc_geometry (n : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {s : ℂ} (hs : s ∈ closedBall (center x t) (delta n)) :
    line n ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - t| ≤ 1 := by
  have hn : ‖s - center x t‖ ≤ delta n := by
    simpa only [mem_closedBall, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - center x t)).trans hn
  have him := (Complex.abs_im_le_norm (s - center x t)).trans hn
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero] at hre
  simp only [ZetaNearOneLocalDisc.center, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] at him
  have hδ := delta_le n
  refine ⟨?_, ?_, ?_⟩
  · unfold line
    linarith [(abs_le.mp hre).1]
  · linarith [(abs_le.mp hre).2]
  · linarith

/-- The full actual translated disc is analytic, with the zeta pole
excluded by the same original buffered height condition. -/
theorem analyticOnNhd_translated (n : ℕ) (hn : 48 ≤ n) {t x : ℝ}
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    AnalyticOnNhd ℂ (translated x t) (closedBall 0 (delta n)) := by
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
  intro z hz
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  have ha := analyticOn_riemannZeta (z + center x t)
    (ZetaNearOneLocalDisc.ne_one_of_window (by linarith) (disc_geometry n t hx hx' hm).2.2)
  exact ha.comp (f := fun w : ℂ ↦ w + center x t) (by fun_prop)

/-- The entire enlarged disc retains the original Vinogradov profile
with no additional height or constant allowance. -/
theorem norm_translated_le (n : ℕ) (hn : 48 ≤ n) {t x : ℝ}
    (ht : (heightThreshold (8 * n) : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4)
    {z : ℂ} (hz : z ∈ closedBall 0 (delta n)) :
    ‖translated x t z‖ ≤ Real.exp (profile n t) := by
  have hm : z + center x t ∈ closedBall (center x t) (delta n) := by
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hz
  obtain ⟨hlo, hhi, hw⟩ := disc_geometry n t hx hx' hm
  exact local_norm_bound n hn ht hlo hhi hw

end
end RiemannGaussian.ZetaVinogradovCubicDisc
