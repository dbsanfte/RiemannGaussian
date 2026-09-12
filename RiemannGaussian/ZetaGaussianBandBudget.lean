/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianStripExplicit
import RiemannGaussian.GaussianStripProfile

/-!
# A uniform explicit Gaussian cost on a height band

Every term of the full Gaussian strip cost receives a rational allowance
for absolute heights at least one million and logarithmic enlarged height
at most 320000. The estimate is uniform over every family with the stated
coarse constant mass, nonconstant mass and logarithmic moment. The fixed
positive center does not use an Euler boundary limit.
-/

namespace RiemannGaussian.ZetaGaussianBandBudget
noncomputable section
open GaussianStripProfile ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily
open ZetaStripEulerConstraint ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open ZetaNearOneLogProfile

private theorem geometry :
    1 / 200 ≤ halfWidth 9 shift ∧ halfWidth 9 shift ≤ 1 / 100 ∧
    1 / (2 * halfWidth 9 shift) ≤ 94 ∧
    1 / 200 ≤ delta 9 + 2 * shift ∧ delta 9 + 2 * shift ≤ 1 / 100 ∧
    1 < rightLine 9 shift ∧ rightLine 9 shift ≤ 2 := by
  norm_num [halfWidth, rightLine, delta, DerivativePowerExponents.alpha, shift, width]

private theorem vertical_bounds : 0 < verticalScale 9 shift ∧ verticalScale 9 shift ≤ 1 := by
  have hη := geometry.1
  have hηu := geometry.2.1
  unfold verticalScale
  constructor
  · positivity
  · apply (div_le_one Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]

private theorem factor_bounds : 0 ≤ factor 9 gaussianScale shift ∧
    factor 9 gaussianScale shift ≤ 1 / 50000 := by
  norm_num [factor, gaussianScale, halfWidth, delta, DerivativePowerExponents.alpha, shift, width]

private theorem completion_le :
    4 * gaussianScale / GaussianPolynomialTransport.mass gaussianScale ≤ 1 := by
  have hB : 0 < gaussianScale := by norm_num [gaussianScale, width]
  have hm : 4 * gaussianScale ≤ GaussianPolynomialTransport.mass gaussianScale := by
    unfold GaussianPolynomialTransport.mass
    apply (Real.le_sqrt (by norm_num [gaussianScale, width])
      (by positivity : 0 ≤ Real.pi / (1 / (4 * gaussianScale)))).mpr
    norm_num [gaussianScale, width]
    nlinarith [Real.pi_gt_three]
  exact (div_le_one (by unfold GaussianPolynomialTransport.mass; positivity)).mpr hm

private theorem log_200_le_six {v : ℝ} (hv : 0 < v) (hv' : v ≤ 200) : Real.log v ≤ 6 := by
  apply (Real.log_le_iff_le_exp hv).mpr
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) he.le 6
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

private theorem log_320000_le_thirteen {v : ℝ} (hv : 0 < v) (hv' : v ≤ 320000) :
    Real.log v ≤ 13 := by
  apply (Real.log_le_iff_le_exp hv).mpr
  have he : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he.le 13
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- The entire band lies in the proved logarithmic-scale domain. -/
theorem scale_lower {t : ℝ} (ht : 1000000 ≤ |t|) : 1 ≤ scale t := by
  apply (Real.le_log_iff_exp_le (by unfold height; positivity)).mpr
  unfold height
  linarith [Real.exp_one_lt_d9]

private theorem log_height_pos {t : ℝ} (ht : 1000000 ≤ |t|) : 0 < Real.log (height t) :=
  lt_of_lt_of_le (by norm_num) (scale_lower ht)

/-- The complete left Euler allowance has a uniform rational ceiling,
including the full vertical shift at every height in the band. -/
theorem left_allowance_le {t : ℝ} (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000) :
    ZetaClippedEulerMean.allowance 9 t (verticalScale 9 shift) ≤ 320000 / 2046 + 24 := by
  have hlog := log_320000_le_thirteen (log_height_pos ht) hL
  have h8192 : Real.log (8192 : ℝ) ≤ 10 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hs := ZetaLogarithmicShiftAllowance.shiftCost_le 9 t (verticalScale 9 shift)
  have hs1 : ZetaLogarithmicShiftAllowance.shiftCost 9 t (verticalScale 9 shift) ≤ 1 := by
    apply hs.trans
    rw [abs_of_pos vertical_bounds.1]
    apply (div_le_one (by unfold height; positivity)).mpr
    unfold height
    linarith [vertical_bounds.2]
  have hshift : Real.log 2 * ZetaLogarithmicShiftAllowance.shiftCost 9 t (verticalScale 9 shift) ≤ 1 := by
    have h := mul_le_mul (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9]) hs1
      (ZetaLogarithmicShiftAllowance.shiftCost_nonneg 9 t (verticalScale 9 shift)) (by norm_num)
    simpa using h
  have halpha : DerivativePowerExponents.alpha 9 * Real.log (height t) ≤ 320000 / 2046 := by
    norm_num [DerivativePowerExponents.alpha]
    change Real.log (height t) ≤ 320000 at hL
    linarith
  unfold ZetaClippedEulerMean.allowance ZetaEulerLogProfile.profile
  linarith

private theorem inverse_tail_le {t : ℝ} (ht : 1000000 ≤ |t|) :
    Real.exp (-|t| / |verticalScale 9 shift|) ≤ 1 / 1000000 := by
  have hb := vertical_bounds
  have hq : |t| ≤ |t| / |verticalScale 9 shift| := by
    rw [abs_of_pos hb.1]
    apply (le_div_iff₀ hb.1).mpr
    nlinarith [abs_nonneg t]
  have he := Real.add_one_le_exp (|t| / |verticalScale 9 shift|)
  rw [neg_div, Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

private theorem rational_profile_le : RationalVerticalCorrection.profile (rightLine 9 shift) 0 ≤ 200000 := by
  rcases geometry with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
  have he : rightLine 9 shift - 1 = delta 9 + 2 * shift := by unfold rightLine; ring
  have hq : 0 < 1 + 4 * rightLine 9 shift / ((rightLine 9 shift - 1) ^ 2 + (0 : ℝ) ^ 2) := by
    rw [he]
    positivity
  have hlog := Real.log_le_sub_one_of_pos hq
  have hu : 4 * rightLine 9 shift / ((rightLine 9 shift - 1) ^ 2 + (0 : ℝ) ^ 2) ≤ 320000 := by
    rw [he]
    calc
      _ ≤ 4 * 2 / ((1 / 200 : ℝ) ^ 2) := by gcongr; nlinarith
      _ = _ := by norm_num
  unfold RationalVerticalCorrection.profile
  linarith

/-- Both complete rational boundary tails fit in one unit throughout
the band, with the exponential tail retained until its explicit estimate. -/
theorem rational_le {t : ℝ} (ht : 1000000 ≤ |t|) :
    8 * rightLine 9 shift / t ^ 2 + 2 * RationalVerticalCorrection.profile (rightLine 9 shift) 0 *
      Real.exp (-|t| / |verticalScale 9 shift|) ≤ 1 := by
  have hsq : (1000000 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hfirst : 8 * rightLine 9 shift / t ^ 2 ≤ 16 / (1000000 : ℝ) ^ 2 := by
    gcongr
    linarith [geometry.2.2.2.2.2.2]
  have hsecond := mul_le_mul rational_profile_le (inverse_tail_le ht)
    (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 200000)
  norm_num at hfirst hsecond
  linarith

private theorem constant_terms_le :
    GaussianFermiLaplaceOrder.halfGaussian gaussianScale shift + Real.log (1 + shift) / 2 +
      4 * gaussianScale / GaussianPolynomialTransport.mass gaussianScale +
      factor 9 gaussianScale shift * (1 / (delta 9 + 2 * shift) +
        448 * localZetaLogHeight 0) +
      Real.log (1 + 1 / (delta 9 + 2 * shift)) / (2 * halfWidth 9 shift) ≤ 200142 := by
  rcases geometry with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + shift by norm_num [shift, width])
  have h22 : localZetaLogHeight 0 ≤ 4 := by
    change Real.log (|0| + 22) ≤ 4
    norm_num
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 22)).mpr
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
      (show (5 / 2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 4
    rw [← Real.exp_nat_mul] at he
    norm_num at he
    linarith
  have hi : 1 / (delta 9 + 2 * shift) ≤ 200 := by
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 200) hh).trans_eq (by norm_num)
  have hfactor := mul_le_mul_of_nonneg_left (show 1 / (delta 9 + 2 * shift) +
      448 * localZetaLogHeight 0 ≤ 1992 by linarith) factor_bounds.1
  have hfactor2 := mul_le_mul_of_nonneg_right factor_bounds.2 (by norm_num : (0 : ℝ) ≤ 1992)
  have hm : Real.log (1 + 1 / (delta 9 + 2 * shift)) ≤ 6 := by
    apply log_200_le_six (by positivity)
    norm_num [delta, DerivativePowerExponents.alpha, shift, width]
  have hmean := mul_le_mul hm hηi
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 shift)) (by norm_num : (0 : ℝ) ≤ 6)
  rw [mul_one_div] at hmean
  have hs : shift ≤ 1 := by norm_num [shift, width]
  linarith [constant_upper, completion_le]

private theorem extra_terms_le {t : ℝ} (ht : 1000000 ≤ |t|) :
    12 * gaussianScale / |t| ^ 3 + 4 * gaussianScale / GaussianPolynomialTransport.mass gaussianScale ≤ 2 := by
  have hden : (1 : ℝ) ≤ |t| ^ 3 := by nlinarith [sq_nonneg (|t| - 1)]
  have hnum : 12 * gaussianScale ≤ 1 := by norm_num [gaussianScale, width]
  have h := (div_le_one (by positivity : 0 < |t| ^ 3)).mpr (hnum.trans hden)
  linarith [completion_le]

private theorem response_terms_le {t : ℝ} (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000) :
    (delta 9 + 2 * shift) / t ^ 2 + Real.log (rightLine 9 shift + |t|) / 2 ≤ 160001 := by
  rcases geometry with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
  have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hfirst : (delta 9 + 2 * shift) / t ^ 2 ≤ 1 := by
    apply (div_le_one (by linarith : 0 < t ^ 2)).mpr
    linarith
  have hl : Real.log (rightLine 9 shift + |t|) ≤ scale t := by
    apply Real.log_le_log (by linarith [abs_nonneg t])
    unfold height
    linarith
  linarith

/-- Every family satisfying the coarse mass and logarithmic-moment
enclosures pays less than the fixed rational ceiling throughout the band. -/
theorem budget_le {a ω : ℕ → ℝ} (ha0 : 0 ≤ a 0) (ha0u : a 0 ≤ 37 / 200)
    (hW : 0 ≤ mass a) (hWu : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {t : ℝ} (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000) :
    budget 9 gaussianScale shift t a ω ≤ 47500 := by
  have hη := geometry.1
  have hconstant := (mul_le_mul_of_nonneg_left constant_terms_le ha0).trans
    (mul_le_mul_of_nonneg_right ha0u (by norm_num : (0 : ℝ) ≤ 200142))
  have hleft := mul_le_mul (add_le_add (left_allowance_le ht hL) (rational_le ht)) hWu hW
    (by norm_num : (0 : ℝ) ≤ 320000 / 2046 + 24 + 1)
  have hleft' : mass a * (ZetaClippedEulerMean.allowance 9 t (verticalScale 9 shift) +
      8 * rightLine 9 shift / t ^ 2 + 2 * RationalVerticalCorrection.profile (rightLine 9 shift) 0 *
      Real.exp (-|t| / |verticalScale 9 shift|)) + 2 * frequencyCost a ω ≤
        (61 / 100 : ℝ) * (320000 / 2046 + 25) + 1 / 2 := by nlinarith only [hleft, hF]
  have hboundary := mul_le_mul hleft' geometry.2.2.1
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 shift)) (by norm_num)
  rw [mul_one_div] at hboundary
  have hextra := (mul_le_mul_of_nonneg_left (extra_terms_le ht) hW).trans
    (mul_le_mul_of_nonneg_right hWu (by norm_num : (0 : ℝ) ≤ 2))
  have hresponse := (mul_le_mul_of_nonneg_left (response_terms_le ht hL) hW).trans
    (mul_le_mul_of_nonneg_right hWu (by norm_num : (0 : ℝ) ≤ 160001))
  have hr := mul_le_mul_of_nonneg_left (show mass a * ((delta 9 + 2 * shift) / t ^ 2 +
      Real.log (rightLine 9 shift + |t|) / 2) + frequencyCost a ω / 2 ≤
        (61 / 100 : ℝ) * 160001 + 1 / 8 by linarith) factor_bounds.1
  have hr' := mul_le_mul_of_nonneg_right factor_bounds.2
    (by norm_num : (0 : ℝ) ≤ (61 / 100) * 160001 + 1 / 8)
  unfold budget
  nlinarith only [hconstant, hboundary, hextra, hr, hr']

end
end RiemannGaussian.ZetaGaussianBandBudget
