/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandBudget

/-!
# Scaling the complete Gaussian cost with logarithmic height

The physical width and positive center shift shrink by `q`, while the
Gaussian parameter shrinks by `q²`. Exact Gaussian homogeneity retains the
source and constant channel at scale `q`. All remaining costs are estimated
with the same family information, for logarithmic heights up to `320000*q`.
-/

namespace RiemannGaussian.ZetaGaussianScaledBandBudget
noncomputable section
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily
open ZetaStripEulerConstraint ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open ZetaNearOneLogProfile GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds

/-- The horizontal width after a positive dilation of the source scale. -/
def width (q : ℝ) : ℝ := GaussianStripProfile.width / q

/-- The positive Euler-center shift scales with the horizontal width. -/
def shift (q : ℝ) : ℝ := GaussianStripProfile.shift / q

/-- Quadratic Gaussian scaling matches the linear damping-coordinate change. -/
def gaussianScale (q : ℝ) : ℝ := GaussianStripProfile.gaussianScale / q ^ 2

/-- Every dilation at least one preserves the original width ceiling. -/
theorem width_bounds {q : ℝ} (hq : 1 ≤ q) :
    0 < width q ∧ width q ≤ GaussianStripProfile.width := by
  have hq0 : 0 < q := by linarith
  exact ⟨div_pos (by norm_num [GaussianStripProfile.width]) hq0,
    div_le_self (by norm_num [GaussianStripProfile.width]) hq⟩

/-- The scaled Euler center remains strictly positive and below the old center. -/
theorem shift_bounds {q : ℝ} (hq : 1 ≤ q) :
    0 < shift q ∧ shift q ≤ GaussianStripProfile.shift := by
  have hq0 : 0 < q := by linarith
  exact ⟨div_pos (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]) hq0,
    div_le_self (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]) hq⟩

/-- The physical Gaussian parameter stays positive and only decreases. -/
theorem gaussianScale_bounds {q : ℝ} (hq : 1 ≤ q) :
    0 < gaussianScale q ∧ gaussianScale q ≤ GaussianStripProfile.gaussianScale := by
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  exact ⟨div_pos (by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width])
      (by linarith), div_le_self
        (by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]) hq2⟩

/-- The original strip geometry bounds hold throughout the entire dilation family. -/
theorem geometry {q : ℝ} (hq : 1 ≤ q) :
    1 / 200 ≤ halfWidth 9 (shift q) ∧ halfWidth 9 (shift q) ≤ 1 / 100 ∧
    1 / (2 * halfWidth 9 (shift q)) ≤ 94 ∧
    1 / 200 ≤ delta 9 + 2 * shift q ∧ delta 9 + 2 * shift q ≤ 1 / 100 ∧
    1 < rightLine 9 (shift q) ∧ rightLine 9 (shift q) ≤ 2 := by
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  norm_num [GaussianStripProfile.shift, GaussianStripProfile.width] at hxu
  have hd : delta 9 = 11 / 2046 := by norm_num [delta, DerivativePowerExponents.alpha]
  simp only [halfWidth, rightLine, hd]
  refine ⟨by linarith, by linarith, ?_, by linarith, by linarith, by linarith, by linarith⟩
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- Vertical scales stay positive and at most one, uniformly in the dilation. -/
theorem vertical_bounds {q : ℝ} (hq : 1 ≤ q) :
    0 < verticalScale 9 (shift q) ∧ verticalScale 9 (shift q) ≤ 1 := by
  have hη := (geometry hq).1
  have hηu := (geometry hq).2.1
  unfold verticalScale
  constructor
  · positivity
  · apply (div_le_one Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]

/-- The common response multiplier has the same uniform small bound. -/
theorem factor_bounds {q : ℝ} (hq : 1 ≤ q) :
    0 ≤ factor 9 (gaussianScale q) (shift q) ∧
      factor 9 (gaussianScale q) (shift q) ≤ 1 / 50000 := by
  obtain ⟨hB, hBu⟩ := gaussianScale_bounds hq
  have hη := (geometry hq).1
  unfold factor
  constructor
  · positivity
  · calc
      _ ≤ 24 * GaussianStripProfile.gaussianScale / ((1 / 200 : ℝ) ^ 2) := by
        gcongr
        norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]
      _ ≤ _ := by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]

/-- The complete Archimedean averaging allowance remains at most one. -/
theorem completion_le {q : ℝ} (hq : 1 ≤ q) :
    4 * gaussianScale q / GaussianPolynomialTransport.mass (gaussianScale q) ≤ 1 := by
  obtain ⟨hB, hBu⟩ := gaussianScale_bounds hq
  have hBsmall : 4 * gaussianScale q ≤ 1 := by
    norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width] at hBu
    linarith
  have hm : 4 * gaussianScale q ≤ GaussianPolynomialTransport.mass (gaussianScale q) := by
    unfold GaussianPolynomialTransport.mass
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    nlinarith [mul_nonneg hB.le (show 0 ≤ Real.pi - 4 * gaussianScale q by linarith [Real.pi_gt_three])]
  exact (div_le_one (by unfold GaussianPolynomialTransport.mass; positivity)).mpr hm

/-- Exact Gaussian homogeneity scales the selected positive-damping source. -/
theorem source_lower {q : ℝ} (hq : 1 ≤ q) :
    152000 * q ≤ halfGaussian (gaussianScale q) (shift q + width q) := by
  have hq0 : 0 < q := by linarith
  have hs := halfGaussian_scale hq0 (gaussianScale q) (shift q + width q)
  have hB : gaussianScale q * q ^ 2 = GaussianStripProfile.gaussianScale := by
    unfold gaussianScale
    field_simp
  have hx : (shift q + width q) * q = GaussianStripProfile.shift + GaussianStripProfile.width := by
    unfold shift width
    field_simp
  rw [hB, hx] at hs
  have h := mul_le_mul_of_nonneg_left GaussianStripProfile.source_lower hq0.le
  nlinarith only [h, hs]

/-- The full constant-channel half-Gaussian has the matching linear bound. -/
theorem constant_upper {q : ℝ} (hq : 1 ≤ q) :
    halfGaussian (gaussianScale q) (shift q) ≤ 199575 * q := by
  have hq0 : 0 < q := by linarith
  have hs := halfGaussian_scale hq0 (gaussianScale q) (shift q)
  have hB : gaussianScale q * q ^ 2 = GaussianStripProfile.gaussianScale := by
    unfold gaussianScale
    field_simp
  have hx : shift q * q = GaussianStripProfile.shift := by
    unfold shift
    field_simp
  rw [hB, hx] at hs
  have h := mul_le_mul_of_nonneg_left GaussianStripProfile.constant_upper hq0.le
  nlinarith only [h, hs]

private theorem log_200_le_six {v : ℝ} (hv : 0 < v) (hv' : v ≤ 200) : Real.log v ≤ 6 := by
  apply (Real.log_le_iff_le_exp hv).mpr
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 2) he.le 6
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

/-- The logarithm of the moving height ceiling is bounded by a linear
dilation cost, uniformly over the full unbounded family. -/
theorem log_scaled_le {q v : ℝ} (hq : 1 ≤ q) (hv : 0 < v) (hv' : v ≤ 320000 * q) :
    Real.log v ≤ 13 * q := by
  have hq0 : 0 < q := by linarith
  have hb : Real.log (320000 : ℝ) ≤ 13 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 320000)).mpr
    have he : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he.le 13
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have hvlog := Real.log_le_log hv hv'
  rw [Real.log_mul (by norm_num : (320000 : ℝ) ≠ 0) hq0.ne'] at hvlog
  linarith [Real.log_le_sub_one_of_pos hq0]

/-- The entire left Euler allowance scales at most linearly with the
height dilation; the full vertical shift is included. -/
theorem left_allowance_le {q t : ℝ} (hq : 1 ≤ q)
    (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000 * q) :
    ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) ≤
      (320000 / 2046 + 24) * q := by
  have hscale := ZetaGaussianBandBudget.scale_lower ht
  have hlog := log_scaled_le hq (by linarith : 0 < scale t) hL
  change Real.log (Real.log (height t)) ≤ 13 * q at hlog
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
  have halpha : DerivativePowerExponents.alpha 9 * Real.log (height t) ≤ (320000 / 2046) * q := by
    norm_num [DerivativePowerExponents.alpha]
    change Real.log (height t) ≤ 320000 * q at hL
    linarith
  unfold ZetaClippedEulerMean.allowance ZetaEulerLogProfile.profile
  linarith

private theorem inverse_tail_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    Real.exp (-|t| / |verticalScale 9 (shift q)|) ≤ 1 / 1000000 := by
  have hb := vertical_bounds hq
  have hv : |t| ≤ |t| / |verticalScale 9 (shift q)| := by
    rw [abs_of_pos hb.1]
    apply (le_div_iff₀ hb.1).mpr
    nlinarith [abs_nonneg t]
  have he := Real.add_one_le_exp (|t| / |verticalScale 9 (shift q)|)
  rw [neg_div, Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

private theorem rational_profile_le {q : ℝ} (hq : 1 ≤ q) :
    RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 ≤ 200000 := by
  rcases geometry hq with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
  have he : rightLine 9 (shift q) - 1 = delta 9 + 2 * shift q := by unfold rightLine; ring
  have hp : 0 < 1 + 4 * rightLine 9 (shift q) / ((rightLine 9 (shift q) - 1) ^ 2 + (0 : ℝ) ^ 2) := by
    rw [he]
    positivity
  have hlog := Real.log_le_sub_one_of_pos hp
  have hu : 4 * rightLine 9 (shift q) / ((rightLine 9 (shift q) - 1) ^ 2 + (0 : ℝ) ^ 2) ≤ 320000 := by
    rw [he]
    calc
      _ ≤ 4 * 2 / ((1 / 200 : ℝ) ^ 2) := by gcongr; nlinarith
      _ = _ := by norm_num
  unfold RationalVerticalCorrection.profile
  linarith

/-- Both rational boundary tails retain the same one-unit allowance. -/
theorem rational_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    8 * rightLine 9 (shift q) / t ^ 2 +
      2 * RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 *
        Real.exp (-|t| / |verticalScale 9 (shift q)|) ≤ 1 := by
  have hsq : (1000000 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hfirst : 8 * rightLine 9 (shift q) / t ^ 2 ≤ 16 / (1000000 : ℝ) ^ 2 := by
    gcongr
    linarith [(geometry hq).2.2.2.2.2.2]
  have hsecond := mul_le_mul (rational_profile_le hq) (inverse_tail_le hq ht)
    (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 200000)
  norm_num at hfirst hsecond
  linarith

/-- All constant-channel terms, including the exact half-Gaussian,
fit the same linear source-scale budget throughout the dilation family. -/
theorem constant_terms_le {q : ℝ} (hq : 1 ≤ q) :
    halfGaussian (gaussianScale q) (shift q) + Real.log (1 + shift q) / 2 +
      4 * gaussianScale q / GaussianPolynomialTransport.mass (gaussianScale q) +
      factor 9 (gaussianScale q) (shift q) * (1 / (delta 9 + 2 * shift q) +
        448 * localZetaLogHeight 0) +
      Real.log (1 + 1 / (delta 9 + 2 * shift q)) / (2 * halfWidth 9 (shift q)) ≤ 200142 * q := by
  rcases geometry hq with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
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
    apply log_200_le_six (by positivity)
    have hδ : (1 / 199 : ℝ) ≤ delta 9 + 2 * shift q := by
      norm_num [delta, DerivativePowerExponents.alpha]
      linarith
    have hi' := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 199) hδ
    norm_num at hi'
    rw [← one_div] at hi'
    linarith
  have hmean := mul_le_mul hm hηi
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 (shift q))) (by norm_num : (0 : ℝ) ≤ 6)
  rw [mul_one_div] at hmean
  have hs : shift q ≤ 1 := hxu.trans (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width])
  linarith [constant_upper hq, completion_le hq]

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

private theorem response_terms_le {q t : ℝ} (hq : 1 ≤ q)
    (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000 * q) :
    (delta 9 + 2 * shift q) / t ^ 2 + Real.log (rightLine 9 (shift q) + |t|) / 2 ≤ 160001 * q := by
  rcases geometry hq with ⟨hη, hηu, hηi, hh, hhu, hτ, hτu⟩
  have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hfirst : (delta 9 + 2 * shift q) / t ^ 2 ≤ 1 := by
    apply (div_le_one (by linarith : 0 < t ^ 2)).mpr
    linarith
  have hl : Real.log (rightLine 9 (shift q) + |t|) ≤ scale t := by
    apply Real.log_le_log (by linarith [abs_nonneg t])
    unfold height
    linarith
  linarith

/-- Every eligible family retains the full rational surplus at the
expanded logarithmic height, with no upper bound on the dilation. -/
theorem budget_le {a ω : ℕ → ℝ} (ha0 : 0 ≤ a 0) (ha0u : a 0 ≤ 37 / 200)
    (hW : 0 ≤ mass a) (hWu : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000 * q) :
    budget 9 (gaussianScale q) (shift q) t a ω ≤ 47500 * q := by
  have hq0 : 0 < q := by linarith
  have hη : 0 < halfWidth 9 (shift q) := lt_of_lt_of_le (by norm_num) (geometry hq).1
  have hconstant := (mul_le_mul_of_nonneg_left (constant_terms_le hq) ha0).trans
    (mul_le_mul_of_nonneg_right ha0u (show 0 ≤ 200142 * q by positivity))
  have hLR : ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) +
      8 * rightLine 9 (shift q) / t ^ 2 +
      2 * RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 *
        Real.exp (-|t| / |verticalScale 9 (shift q)|) ≤ (320000 / 2046 + 25) * q := by
    linarith [left_allowance_le hq ht hL, rational_le hq ht]
  have hleft := mul_le_mul hLR hWu hW (by positivity)
  have hleft' : mass a * (ZetaClippedEulerMean.allowance 9 t (verticalScale 9 (shift q)) +
      8 * rightLine 9 (shift q) / t ^ 2 + 2 * RationalVerticalCorrection.profile (rightLine 9 (shift q)) 0 *
      Real.exp (-|t| / |verticalScale 9 (shift q)|)) + 2 * frequencyCost a ω ≤
        ((61 / 100 : ℝ) * (320000 / 2046 + 25) + 1 / 2) * q := by nlinarith only [hleft, hF, hq]
  have hboundary := mul_le_mul hleft' (geometry hq).2.2.1
    (by positivity : 0 ≤ 1 / (2 * halfWidth 9 (shift q))) (by positivity)
  rw [mul_one_div] at hboundary
  have hextra := (mul_le_mul_of_nonneg_left (extra_terms_le hq ht) hW).trans
    (mul_le_mul_of_nonneg_right hWu (by norm_num : (0 : ℝ) ≤ 2))
  have hresponse := (mul_le_mul_of_nonneg_left (response_terms_le hq ht hL) hW).trans
    (mul_le_mul_of_nonneg_right hWu (show 0 ≤ 160001 * q by positivity))
  have hr := mul_le_mul_of_nonneg_left (show mass a * ((delta 9 + 2 * shift q) / t ^ 2 +
      Real.log (rightLine 9 (shift q) + |t|) / 2) + frequencyCost a ω / 2 ≤
        ((61 / 100 : ℝ) * 160001 + 1 / 8) * q by nlinarith only [hresponse, hF, hq]) (factor_bounds hq).1
  have hr' := mul_le_mul_of_nonneg_right (factor_bounds hq).2
    (show 0 ≤ ((61 / 100 : ℝ) * 160001 + 1 / 8) * q by positivity)
  unfold budget
  nlinarith only [hconstant, hboundary, hextra, hr, hr', hq]

end
end RiemannGaussian.ZetaGaussianScaledBandBudget
