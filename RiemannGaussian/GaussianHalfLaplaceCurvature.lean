/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceShift

/-!
# Curvature retained in the shifted Gaussian interval

The elementary exponential tangent bounds the Gaussian on a bounded
interval by a quadratic with its curvature retained. Integrating that
quadratic improves the negative-damping half-transform bound while
preserving the exact shifted-interval identity upstream.
-/

namespace RiemannGaussian.GaussianHalfLaplaceCurvature
noncomputable section
open MeasureTheory Set
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianHalfLaplaceShift

/-- On a bounded interval, the Gaussian lies below a quadratic that
retains a uniform fraction of its curvature. -/
theorem window_one_le_quadratic {h u : ℝ} (hu : u ^ 2 ≤ h ^ 2) :
    window 1 u ≤ 1 - u ^ 2 / (1 + h ^ 2) := by
  have hv : 0 < 1 + u ^ 2 := by positivity
  have hh : 0 < 1 + h ^ 2 := by positivity
  have he : Real.exp (-u ^ 2) ≤ 1 / (1 + u ^ 2) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hv (by linarith [Real.add_one_le_exp (u ^ 2)])
  have hq : 1 / (1 + u ^ 2) ≤ 1 - u ^ 2 / (1 + h ^ 2) := by
    rw [show 1 - u ^ 2 / (1 + h ^ 2) = (1 + h ^ 2 - u ^ 2) / (1 + h ^ 2) by
      field_simp]
    apply (div_le_div_iff₀ hv hh).mpr
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]
  simpa only [window, neg_mul, one_mul] using he.trans hq

/-- The complete displaced interval has a cubic improvement over its
length, obtained by integrating the retained quadratic curvature. -/
theorem integral_window_one_le {h : ℝ} (hh : 0 ≤ h) :
    (∫ u in -h..0, window 1 u) ≤ h - h ^ 3 / (3 * (1 + h ^ 2)) := by
  have hi : IntervalIntegrable (fun u : ℝ ↦ 1 - u ^ 2 / (1 + h ^ 2)) volume (-h) 0 := by
    exact (show Continuous (fun u : ℝ ↦ 1 - u ^ 2 / (1 + h ^ 2)) by fun_prop).intervalIntegrable _ _
  have hbound := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -h ≤ 0)
    ((continuous_window 1).intervalIntegrable _ _) hi (fun u hu ↦
      window_one_le_quadratic (by
        have hulo : -h ≤ u := hu.1
        have huhi : u ≤ 0 := hu.2
        nlinarith))
  have hi2 : IntervalIntegrable (fun u : ℝ ↦ u ^ 2 / (1 + h ^ 2)) volume (-h) 0 :=
    (show Continuous (fun u : ℝ ↦ u ^ 2 / (1 + h ^ 2)) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi2,
    intervalIntegral.integral_div, integral_pow] at hbound
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hbound
  convert hbound using 1
  field_simp
  ring

/-- Completing the square and retaining the shifted interval's curvature
gives a sharper pole bound at every nonnegative displacement. -/
theorem halfGaussian_neg_curvature_upper {x : ℝ} (hx : 0 ≤ x) :
    halfGaussian 1 (-x) ≤ Real.exp (x ^ 2 / 4) *
      (Real.sqrt Real.pi / 2 + x / 2 - (x / 2) ^ 3 / (3 * (1 + (x / 2) ^ 2))) := by
  rw [halfGaussian_neg_shift (by norm_num : (0 : ℝ) < 1)]
  norm_num only [div_one, mul_one] at *
  have h := integral_window_one_le (show 0 ≤ x / 2 by positivity)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith

end
end RiemannGaussian.GaussianHalfLaplaceCurvature
