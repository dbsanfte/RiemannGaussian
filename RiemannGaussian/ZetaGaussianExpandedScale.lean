/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianScaledBandBudget

/-!
# Gaussian geometry below the former dilation cutoff

The source scaling law only needs a positive dilation. On `q ≥ 9/100`,
the complete strip geometry, rational tails and Archimedean correction
remain controlled, with the larger response factor paid explicitly.
This module alone asserts no new zero-free region.
-/

namespace RiemannGaussian.ZetaGaussianExpandedScale
noncomputable section
open ZetaGaussianScaledBandBudget (width shift gaussianScale)
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily
open ZetaStripEulerConstraint ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open ZetaNearOneLogProfile GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds

/-- Positive dilations down to nine hundredths permit a wider physical strip. -/
theorem width_bounds {q : ℝ} (hq : 9 / 100 ≤ q) :
    0 < width q ∧ width q ≤ 1 / 40500 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact div_pos (by norm_num [GaussianStripProfile.width]) hq0
  · apply (div_le_iff₀ hq0).mpr
    norm_num [GaussianStripProfile.width]
    linarith

/-- The larger center shift remains positive with an explicit uniform ceiling. -/
theorem shift_bounds {q : ℝ} (hq : 9 / 100 ≤ q) :
    0 < shift q ∧ shift q ≤ 1 / 40500000 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact div_pos (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]) hq0
  · apply (div_le_iff₀ hq0).mpr
    norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
    linarith

/-- The physical Gaussian scale remains uniformly small on the enlarged range. -/
theorem gaussianScale_bounds {q : ℝ} (hq : 9 / 100 ≤ q) :
    0 < gaussianScale q ∧ gaussianScale q ≤ 4 / (40500 : ℝ) ^ 2 := by
  have hq0 : 0 < q := by linarith
  constructor
  · exact div_pos (by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width])
      (sq_pos_of_pos hq0)
  · apply (div_le_iff₀ (sq_pos_of_pos hq0)).mpr
    norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]
    nlinarith

/-- The original strip geometry bounds hold throughout the entire dilation family. -/
theorem geometry {q : ℝ} (hq : 9 / 100 ≤ q) :
    1 / 200 ≤ halfWidth 9 (shift q) ∧ halfWidth 9 (shift q) ≤ 1 / 100 ∧
    1 / (2 * halfWidth 9 (shift q)) ≤ 94 ∧
    1 / 200 ≤ delta 9 + 2 * shift q ∧ delta 9 + 2 * shift q ≤ 1 / 100 ∧
    1 < rightLine 9 (shift q) ∧ rightLine 9 (shift q) ≤ 2 := by
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hd : delta 9 = 11 / 2046 := by norm_num [delta, DerivativePowerExponents.alpha]
  simp only [halfWidth, rightLine, hd]
  refine ⟨by linarith, by linarith, ?_, by linarith, by linarith, by linarith, by linarith⟩
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- Vertical scales stay positive and at most one, uniformly in the dilation. -/
theorem vertical_bounds {q : ℝ} (hq : 9 / 100 ≤ q) :
    0 < verticalScale 9 (shift q) ∧ verticalScale 9 (shift q) ≤ 1 := by
  have hη := (geometry hq).1
  have hηu := (geometry hq).2.1
  unfold verticalScale
  constructor
  · positivity
  · apply (div_le_one Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]

/-- The larger response multiplier has an explicit ceiling of one four-hundredth. -/
theorem factor_bounds {q : ℝ} (hq : 9 / 100 ≤ q) :
    0 ≤ factor 9 (gaussianScale q) (shift q) ∧
      factor 9 (gaussianScale q) (shift q) ≤ 1 / 400 := by
  obtain ⟨hB, hBu⟩ := gaussianScale_bounds hq
  have hη := (geometry hq).1
  unfold factor
  constructor
  · positivity
  · calc
      _ ≤ 24 * (4 / (40500 : ℝ) ^ 2) / ((1 / 200 : ℝ) ^ 2) := by
        gcongr
      _ ≤ _ := by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]

/-- The complete Archimedean averaging allowance remains at most one. -/
theorem completion_le {q : ℝ} (hq : 9 / 100 ≤ q) :
    4 * gaussianScale q / GaussianPolynomialTransport.mass (gaussianScale q) ≤ 1 := by
  obtain ⟨hB, hBu⟩ := gaussianScale_bounds hq
  have hBsmall : 4 * gaussianScale q ≤ 1 := by
    norm_num at hBu
    linarith
  have hm : 4 * gaussianScale q ≤ GaussianPolynomialTransport.mass (gaussianScale q) := by
    unfold GaussianPolynomialTransport.mass
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    nlinarith [mul_nonneg hB.le (show 0 ≤ Real.pi - 4 * gaussianScale q by linarith [Real.pi_gt_three])]
  exact (div_le_one (by unfold GaussianPolynomialTransport.mass; positivity)).mpr hm

/-- Exact Gaussian homogeneity scales the selected positive-damping source. -/
theorem source_lower {q : ℝ} (hq0 : 0 < q) :
    152000 * q ≤ halfGaussian (gaussianScale q) (shift q + width q) := by
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
theorem constant_upper {q : ℝ} (hq0 : 0 < q) :
    halfGaussian (gaussianScale q) (shift q) ≤ 199575 * q := by
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

private theorem inverse_tail_le {q t : ℝ} (hq : 9 / 100 ≤ q) (ht : 1000000 ≤ |t|) :
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

private theorem rational_profile_le {q : ℝ} (hq : 9 / 100 ≤ q) :
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
theorem rational_le {q t : ℝ} (hq : 9 / 100 ≤ q) (ht : 1000000 ≤ |t|) :
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

end
end RiemannGaussian.ZetaGaussianExpandedScale
