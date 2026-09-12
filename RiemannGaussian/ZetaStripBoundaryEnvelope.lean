/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticStripGrowth
import RiemannGaussian.ZetaStripDisc
import RiemannGaussian.ZetaEulerReciprocalAllowance

/-!
# A uniform upper envelope for the actual signed strip boundary

The real projection controls the strip map's growing imaginary coordinate.
Actual zeta growth then bounds the left projection uniformly over the whole
unit disc. The full reciprocal Euler series controls the right projection.
The result is one-sided domination, including through actual zero points,
for the signed boundary-limit argument. It is not the sharp final boundary
allowance and does not assert convergence of the boundary integrals.
-/

namespace RiemannGaussian.ZetaStripBoundaryEnvelope
noncomputable section
open Complex
open ZetaGaussianLocalizer

/-- A coarse actual logarithmic growth envelope throughout the strip
needed for boundary domination, also at zero points. -/
theorem log_regularized_le {s : ℂ} (hlo : (1 / 2 : ℝ) ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    Real.log ‖regularized s‖ ≤ 52 + 2 * |s.im| := by
  by_cases hz : regularized s = 0
  · simp only [hz, norm_zero, Real.log_zero]
    positivity
  have h := Real.log_le_log (norm_pos_iff.mpr hz) (norm_regularized_le hlo hhi)
  have hy : 0 < |s.im| + 22 := by positivity
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 2 hy.ne'), Real.log_pow] at h
  norm_num at h
  linarith [Real.log_le_self (show (0 : ℝ) ≤ 8 by norm_num), Real.log_le_self hy.le]

/-- Actual strip growth and the retained real projection give a uniform
left-side upper envelope, despite the two infinite strip ends. -/
theorem left_projection_le {c w : ℂ} {η : ℝ} (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hw : ‖w‖ < 1) :
    |w.re| * Real.log ‖ZetaStripDisc.carrier c η w‖ ≤
      52 + 2 * |c.im| + 8 * η / Real.pi := by
  let s := AnalyticStripMap.map c η w
  have hstrip := AnalyticStripMap.map_mem_strip c hη hw
  have hslo : (1 / 2 : ℝ) ≤ s.re := by dsimp [s]; linarith [(abs_lt.mp hstrip).1]
  have hshi : s.re ≤ 3 / 2 := by dsimp [s]; linarith [(abs_lt.mp hstrip).2]
  have h := mul_le_mul_of_nonneg_left (log_regularized_le hslo hshi) (abs_nonneg w.re)
  have hy : |s.im| ≤ |c.im| + |s.im - c.im| := by
    have hh := abs_add_le c.im (s.im - c.im)
    rw [add_sub_cancel] at hh
    exact hh
  have hx : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw.le
  have hm := AnalyticStripGrowth.abs_re_mul_abs_map_im_sub_le c hη hw
  change |w.re| * |s.im - c.im| ≤ _ at hm
  change |w.re| * Real.log ‖regularized s‖ ≤ _
  have hheight := mul_le_mul_of_nonneg_left hy (abs_nonneg w.re)
  have hcenter := mul_le_of_le_one_left (abs_nonneg c.im) hx
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith [abs_nonneg w.re, abs_nonneg c.im]

/-- Undoing the rational normalization on the Euler side has a uniform
explicit norm cost depending only on its distance from the pole line. -/
theorem inverse_ratio_le {s : ℂ} (hs : 1 < s.re) :
    ‖(s + 1) / (s - 1)‖ ≤ 1 + 2 / (s.re - 1) := by
  have hx : 0 < s.re - 1 := by linarith
  have hl : s.re - 1 ≤ ‖s - 1‖ := by simpa using Complex.re_le_norm (s - 1)
  have hn : 0 < ‖s - 1‖ := hx.trans_le hl
  have ht : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
    have h := norm_add_le (s - 1) (2 : ℂ)
    norm_num [show s - 1 + 2 = s + 1 by ring] at h
    exact h
  rw [norm_div]
  calc
    _ ≤ (‖s - 1‖ + 2) / ‖s - 1‖ := div_le_div_of_nonneg_right ht hn.le
    _ = 1 + 2 / ‖s - 1‖ := by field_simp
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (by norm_num) hx hl) 1

/-- The complete reciprocal Euler series and rational normalization
give a height-independent right-half-plane logarithmic envelope. -/
theorem neg_log_regularized_le {c s : ℂ} (hc : 1 < c.re) (hs : c.re ≤ s.re) :
    -Real.log ‖regularized s‖ ≤ (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by
  have hs1 : 1 < s.re := hc.trans_le hs
  have hc0 : 0 < c.re - 1 := by linarith
  have hs0 : 0 < s.re - 1 := by linarith
  have hsne : s ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
  have he : (regularized s)⁻¹ = (riemannZeta s)⁻¹ * ((s + 1) / (s - 1)) := by
    rw [regularized_eq hsne, mul_inv_rev, inv_div]
  have hz : ‖(riemannZeta s)⁻¹‖ ≤ 1 + 1 / (c.re - 1) :=
    (ZetaEulerReciprocalAllowance.inverse_zeta_bound hs1).trans
      (add_le_add_right (one_div_le_one_div_of_le hc0 (by linarith)) 1)
  have hratio : ‖(s + 1) / (s - 1)‖ ≤ 1 + 2 / (c.re - 1) :=
    (inverse_ratio_le hs1).trans
      (add_le_add_right (div_le_div_of_nonneg_left (by norm_num) hc0 (by linarith)) 1)
  have hnorm : ‖(regularized s)⁻¹‖ ≤ (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by
    rw [he, norm_mul]
    exact mul_le_mul hz hratio (norm_nonneg _) (by positivity)
  have h := (Real.log_le_self (norm_nonneg ((regularized s)⁻¹))).trans hnorm
  rwa [norm_inv, Real.log_inv] at h

/-- The right projection stays on the genuine Euler side under the
strip map, and is uniformly bounded at every interior disc point. -/
theorem right_projection_le {c w : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hw : ‖w‖ < 1) (hre : 0 ≤ w.re) :
    -w.re * Real.log ‖ZetaStripDisc.carrier c η w‖ ≤
      (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by
  have hs : c.re ≤ (AnalyticStripMap.map c η w).re := by
    by_contra! h
    have hn := (AnalyticStripMap.map_re_lt_center_iff c hη hw).mp h
    linarith
  have h := mul_le_mul_of_nonneg_left (neg_log_regularized_le hc hs) hre
  have hx : w.re ≤ 1 := (Complex.re_le_norm w).trans hw.le
  have hc0 : 0 < c.re - 1 := by linarith
  have hp : 0 ≤ (1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1)) := by positivity
  have hb := mul_le_of_le_one_left hp hx
  change -w.re * Real.log ‖regularized (AnalyticStripMap.map c η w)‖ ≤ _
  nlinarith

/-- The entire original signed projection has a finite uniform upper
envelope through both infinite ends and all interior zero points. This
one-sided bound supplies domination for a subsequent boundary inequality. -/
theorem signed_projection_le {c w : ℂ} {η : ℝ} (hc : 1 < c.re) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ c.re - η) (hhi : c.re + η ≤ 3 / 2) (hw : ‖w‖ < 1) :
    -w.re * Real.log ‖ZetaStripDisc.carrier c η w‖ ≤
      max (52 + 2 * |c.im| + 8 * η / Real.pi)
        ((1 + 1 / (c.re - 1)) * (1 + 2 / (c.re - 1))) := by
  by_cases h : w.re ≤ 0
  · have hl := left_projection_le hη hlo hhi hw
    rw [abs_of_nonpos h] at hl
    exact hl.trans (le_max_left _ _)
  · exact (right_projection_le hc hη hw (by linarith)).trans (le_max_right _ _)

end
end RiemannGaussian.ZetaStripBoundaryEnvelope
