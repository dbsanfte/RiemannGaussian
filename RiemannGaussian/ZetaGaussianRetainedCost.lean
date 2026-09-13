/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianScaledBandBudget

/-!
# Retaining the fixed and logarithmic Gaussian strip costs

The full explicit family budget is bounded by a linear Gaussian constant
channel, a linear logarithmic-height term, and a separate log-log and fixed
allowance. No upper height constraint is used. Keeping these different
scales avoids charging every small term proportionally to dilation.
-/

namespace RiemannGaussian.ZetaGaussianRetainedCost
noncomputable section
open ZetaGaussianScaledBandBudget ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily
open ZetaStripEulerConstraint ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open ZetaNearOneLogProfile GaussianFermiLaplaceOrder

/-- The exact order-nine gap improves the inverse half-width ceiling. -/
theorem inverse_halfWidth_le {q : ℝ} (hq : 1 ≤ q) :
    1 / (2 * halfWidth 9 (shift q)) ≤ 93 := by
  have hx := (shift_bounds hq).1
  have hη := halfWidth_pos 9 hx
  apply (div_le_iff₀ (by positivity : 0 < 2 * halfWidth 9 (shift q))).mpr
  norm_num [halfWidth, delta, DerivativePowerExponents.alpha]
  linarith

private theorem log_small {v : ℝ} (hv : 0 < v) (hv' : v ≤ 200) : Real.log v ≤ 6 := by
  apply (Real.log_le_iff_le_exp hv).mpr
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
    (show (5 / 2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 6
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- Only the half-Gaussian part of the constant channel grows with dilation. -/
theorem constant_terms_le {q : ℝ} (hq : 1 ≤ q) :
    halfGaussian (gaussianScale q) (shift q) + Real.log (1 + shift q) / 2 +
      4 * gaussianScale q / GaussianPolynomialTransport.mass (gaussianScale q) +
      factor 9 (gaussianScale q) (shift q) * (1 / (delta 9 + 2 * shift q) +
        448 * localZetaLogHeight 0) +
      Real.log (1 + 1 / (delta 9 + 2 * shift q)) / (2 * halfWidth 9 (shift q)) ≤
        199575 * q + 560 := by
  rcases geometry hq with ⟨hη, _, _, hh, _, _, _⟩
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + shift q by linarith)
  have h22 : localZetaLogHeight 0 ≤ 4 := by
    change Real.log (|0| + 22) ≤ 4
    norm_num
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22)).mpr
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (show (5 / 2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 4
    rw [← Real.exp_nat_mul] at he
    norm_num at he
    linarith
  have hi : 1 / (delta 9 + 2 * shift q) ≤ 200 := by
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 200) hh).trans_eq (by norm_num)
  have hfactor := mul_le_mul_of_nonneg_left (show 1 / (delta 9 + 2 * shift q) +
      448 * localZetaLogHeight 0 ≤ 1992 by linarith) (factor_bounds hq).1
  have hfactor2 := mul_le_mul_of_nonneg_right (factor_bounds hq).2 (by norm_num : (0 : ℝ) ≤ 1992)
  have hm : Real.log (1 + 1 / (delta 9 + 2 * shift q)) ≤ 6 := by
    apply log_small (by positivity)
    have hδ : (1 / 199 : ℝ) ≤ delta 9 + 2 * shift q := by
      norm_num [delta, DerivativePowerExponents.alpha]
      linarith
    have hi' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 199) hδ
    norm_num at hi'
    rw [← one_div] at hi'
    linarith
  have hmean := mul_le_mul hm (inverse_halfWidth_le hq)
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 (shift q))) (by norm_num : (0 : ℝ) ≤ 6)
  rw [mul_one_div] at hmean
  have hs : shift q ≤ 1 := hxu.trans (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width])
  linarith [constant_upper hq, completion_le hq]

/-- The entire left allowance retains its actual logarithmic height and log-log term. -/
theorem left_allowance_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) ≤
      scale t / 2046 + Real.log (scale t) + 11 := by
  have h8192 : Real.log (8192 : ℝ) ≤ 10 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hs := ZetaLogarithmicShiftAllowance.shiftCost_le 9 t (verticalScale 9 (shift q))
  have hs1 : ZetaLogarithmicShiftAllowance.shiftCost 9 t (verticalScale 9 (shift q)) ≤ 1 := by
    apply hs.trans
    rw [abs_of_pos (vertical_bounds hq).1]
    apply (div_le_one (by unfold height; positivity)).mpr
    unfold height
    linarith [(vertical_bounds hq).2]
  have hshift : Real.log 2 * ZetaLogarithmicShiftAllowance.shiftCost 9 t (verticalScale 9 (shift q)) ≤ 1 := by
    have h := mul_le_mul (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9]) hs1
      (ZetaLogarithmicShiftAllowance.shiftCost_nonneg 9 t (verticalScale 9 (shift q))) (by norm_num)
    simpa using h
  unfold ZetaClippedEulerMean.allowance ZetaEulerLogProfile.profile
  norm_num [DerivativePowerExponents.alpha]
  change Real.log 8192 + (1 / 2046) * scale t + Real.log (scale t) + _ ≤ _
  linarith

private theorem extra_terms_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    12 * gaussianScale q / |t| ^ 3 +
      4 * gaussianScale q / GaussianPolynomialTransport.mass (gaussianScale q) ≤ 2 := by
  have hden : (1 : ℝ) ≤ |t| ^ 3 := by nlinarith [sq_nonneg (|t| - 1)]
  have hnum : 12 * gaussianScale q ≤ 1 := by
    have hb := (gaussianScale_bounds hq).2
    norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width] at hb
    linarith
  have h := (div_le_one (by positivity : 0 < |t| ^ 3)).mpr (hnum.trans hden)
  linarith [completion_le hq]

private theorem response_terms_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    (delta 9 + 2 * shift q) / t ^ 2 + Real.log (rightLine 9 (shift q) + |t|) / 2 ≤
      scale t / 2 + 1 := by
  rcases geometry hq with ⟨_, _, _, _, hhu, _, hτu⟩
  have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hfirst : (delta 9 + 2 * shift q) / t ^ 2 ≤ 1 := by
    apply (div_le_one (by linarith : 0 < t ^ 2)).mpr
    linarith
  have hl : Real.log (rightLine 9 (shift q) + |t|) ≤ scale t := by
    apply Real.log_le_log (by linarith [(geometry hq).2.2.2.2.2.1, abs_nonneg t])
    unfold height
    linarith
  linarith

/-- The complete family cost retains its linear, logarithmic and fixed scales,
uniformly over every dilation and every height in the explicit working domain. -/
theorem budget_le {a ω : ℕ → ℝ} (ha0 : 0 ≤ a 0) (ha0u : a 0 ≤ 37 / 200)
    (hW : 0 ≤ mass a) (hWu : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    budget 9 (gaussianScale q) (shift q) t a ω ≤
      36922 * q + scale t / 36 + 57 * Real.log (scale t) + 840 := by
  have hq0 : 0 < q := by linarith
  have hL := ZetaGaussianBandBudget.scale_lower ht
  have hl : 0 ≤ Real.log (scale t) := Real.log_nonneg hL
  have hη : 0 < halfWidth 9 (shift q) := halfWidth_pos 9 (shift_bounds hq).1
  have hconstant := (mul_le_mul_of_nonneg_left (constant_terms_le hq) ha0).trans
    (mul_le_mul_of_nonneg_right ha0u (show 0 ≤ 199575 * q + 560 by positivity))
  have hLR : ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) +
      8 * rightLine 9 (shift q) / t ^ 2 +
      2 * RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 *
        Real.exp (-|t| / |verticalScale 9 (shift q)|) ≤
      scale t / 2046 + Real.log (scale t) + 12 := by
    linarith [left_allowance_le hq ht, rational_le hq ht]
  have hleft := mul_le_mul hLR hWu hW (by positivity)
  have hleft' : mass a * (ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) +
      8 * rightLine 9 (shift q) / t ^ 2 + 2 * RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 *
      Real.exp (-|t| / |verticalScale 9 (shift q)|)) + 2 * frequencyCost a ω ≤
        (61 / 100 : ℝ) * (scale t / 2046 + Real.log (scale t) + 12) + 1 / 2 := by
    nlinarith only [hleft, hF]
  have hboundary := mul_le_mul hleft' (inverse_halfWidth_le hq)
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 (shift q))) (by positivity)
  rw [mul_one_div] at hboundary
  have hextra := (mul_le_mul_of_nonneg_left (extra_terms_le hq ht) hW).trans
    (mul_le_mul_of_nonneg_right hWu (by norm_num : (0 : ℝ) ≤ 2))
  have hresponse := (mul_le_mul_of_nonneg_left (response_terms_le hq ht) hW).trans
    (mul_le_mul_of_nonneg_right hWu (show 0 ≤ scale t / 2 + 1 by positivity))
  have hr := mul_le_mul_of_nonneg_left (show mass a * ((delta 9 + 2 * shift q) / t ^ 2 +
      Real.log (rightLine 9 (shift q) + |t|) / 2) + frequencyCost a ω / 2 ≤
        (61 / 100 : ℝ) * (scale t / 2 + 1) + 1 / 8 by linarith) (factor_bounds hq).1
  have hr' := mul_le_mul_of_nonneg_right (factor_bounds hq).2
    (show 0 ≤ (61 / 100 : ℝ) * (scale t / 2 + 1) + 1 / 8 by positivity)
  unfold budget
  nlinarith only [hconstant, hboundary, hextra, hr, hr', hq, hL, hl]

end
end RiemannGaussian.ZetaGaussianRetainedCost
