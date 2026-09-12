/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripMap

/-!
# The signed projection controls the infinite strip ends

The arctangent height diverges at two boundary points. Retaining the
original real projection bounds its product with that height uniformly
throughout the disc. This supplies domination for signed boundary limits
without imposing a finite-height cutoff.
-/

namespace RiemannGaussian.AnalyticStripGrowth
noncomputable section
open Complex
open AnalyticStripMap

/-- The imaginary coordinate keeps the exact logarithmic Cayley modulus. -/
theorem arctan_im (w : ℂ) : (Complex.arctan w).im = -Real.log ‖cayley w‖ / 2 := by
  simp [Complex.arctan, cayley, Complex.mul_im, Complex.log_re]
  ring

/-- The real projection controls the entire arctangent height,
uniformly through both infinite strip ends. -/
theorem abs_re_mul_abs_arctan_im_le {w : ℂ} (hw : ‖w‖ < 1) :
    |w.re| * |(Complex.arctan w).im| ≤ 1 := by
  by_cases hx0 : w.re = 0
  · simp [hx0]
  have hx : 0 < |w.re| := abs_pos.mpr hx0
  have hp : 0 < ‖1 + w * I‖ := norm_pos_iff.mpr (numerator_ne_zero hw)
  have hm : 0 < ‖1 - w * I‖ := norm_pos_iff.mpr (denominator_ne_zero hw)
  have hpl : |w.re| ≤ ‖1 + w * I‖ := by
    simpa using Complex.abs_im_le_norm (1 + w * I)
  have hml : |w.re| ≤ ‖1 - w * I‖ := by
    simpa using Complex.abs_im_le_norm (1 - w * I)
  have hpu : ‖1 + w * I‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (w * I)
    simp only [norm_one, norm_mul, norm_I, mul_one] at h
    linarith
  have hmu : ‖1 - w * I‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (w * I)
    simp only [norm_one, norm_mul, norm_I, mul_one] at h
    linarith
  have he : Real.log ‖cayley w‖ = Real.log ‖1 + w * I‖ - Real.log ‖1 - w * I‖ := by
    rw [cayley, norm_div, Real.log_div hp.ne' hm.ne']
  have hl : |Real.log ‖cayley w‖| ≤ Real.log 2 - Real.log |w.re| := by
    rw [he, abs_le]
    constructor
    · linarith [Real.log_le_log hx hpl, Real.log_le_log hm hmu]
    · linarith [Real.log_le_log hp hpu, Real.log_le_log hx hml]
  have hlog : |w.re| * (Real.log 2 - Real.log |w.re|) ≤ 2 := by
    rw [← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hx)) hx.le
    have he : |w.re| * (2 / |w.re| - 1) = 2 - |w.re| := by field_simp
    rw [he] at h
    linarith
  have h := (mul_le_mul_of_nonneg_left hl hx.le).trans hlog
  rw [arctan_im, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- The physical strip height and original real projection have a
uniform coupled bound. Their singular factors are never bounded separately. -/
theorem abs_re_mul_abs_map_im_sub_le (c : ℂ) {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : ‖w‖ < 1) :
    |w.re| * |(AnalyticStripMap.map c η w).im - c.im| ≤ 4 * η / Real.pi := by
  have he : 4 * (η : ℂ) / Real.pi = ((4 * η / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  have him : (AnalyticStripMap.map c η w).im - c.im =
      (4 * η / Real.pi) * (Complex.arctan w).im := by
    rw [AnalyticStripMap.map, he]
    simp
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < 4 * η / Real.pi)]
  have h := mul_le_mul_of_nonneg_left (abs_re_mul_abs_arctan_im_le hw)
    (by positivity : 0 ≤ 4 * η / Real.pi)
  nlinarith

end
end RiemannGaussian.AnalyticStripGrowth
