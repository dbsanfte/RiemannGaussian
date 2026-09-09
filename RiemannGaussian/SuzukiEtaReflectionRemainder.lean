/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaSignedSquareBound
import RiemannGaussian.SuzukiEtaOrientedPhaseContours
import RiemannGaussian.SuzukiReflectionWeightSector

/-!
# Independent signed bounds for the actual reflection strip remainder

The oriented complex reflection weights lie in a controlled sector on
remote strip sides. Choosing the dyadic sine signs in the matching
quadrants makes their coefficients negative. The completed-square
inequality then bounds the signed eta/derivative remainder from below,
with a quartically decreasing allowance independent of the truncation
and of any denominator separation. The carrier energy is retained.
-/

open Complex
namespace RiemannGaussian
noncomputable section

private lemma oriented_coefficient_le (W L : ℂ) {ell : ℝ} (hl : 0 < ell)
    (hw : 0 ≤ W.re) (hwi : |W.im| ≤ W.re / 32) (hwn : ‖W‖ ≤ 2 * W.re)
    (hLre : |L.re| ≤ 2 * ell / 3) (hLim : ell / 12 ≤ L.im) :
    -(I * W * starRingEnd ℂ L).re ≤ -(ell / 32) * ‖W‖ := by
  have hprod : W.im * L.re ≤ (W.re / 32) * (2 * ell / 3) := by
    calc
      _ ≤ |W.im * L.re| := le_abs_self _
      _ = |W.im| * |L.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul hwi hLre (abs_nonneg _) (by positivity)
  have him := mul_le_mul_of_nonneg_left hLim hw
  have hnorm := mul_le_mul_of_nonneg_left hwn hl.le
  simp only [mul_re, mul_im, I_re, I_im, conj_re, conj_im, zero_mul, one_mul, zero_sub, zero_add]
  nlinarith

/-- The right-side oriented reflection test has a uniformly negative
dyadic coefficient throughout a favorable remote strip segment. -/
theorem suzukiEtaDyadicWeightCoefficient_reflection_right_le
    (rho : NontrivialZetaZero) {v y : ℝ}
    (hv : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re|) (hy : y ∈ Set.Icc 0 (1 / 2))
    (hcos : Real.cos (v * Real.log 2) ≤ 0) (hsin : 1 / 2 ≤ Real.sin (v * Real.log 2)) :
    suzukiEtaDyadicWeightCoefficient (I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I))
        (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≤
      -(Real.log 2 / 32) * ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ := by
  let s := suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)
  have hslo : 1 / 2 ≤ s.re := by rw [suzukiArithmeticZetaArgument_re]; simpa using hy.1
  have hshi : s.re ≤ 1 := by
    rw [suzukiArithmeticZetaArgument_re]
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    linarith [hy.2]
  have hscos : Real.cos (s.im * Real.log 2) ≤ 0 := by
    rwa [cos_suzukiArithmeticZetaArgument_vertical]
  have hssin : Real.sin (s.im * Real.log 2) ≤ -1 / 2 := by
    have he : Real.sin (s.im * Real.log 2) = -Real.sin (v * Real.log 2) := by
      simp [s, suzukiArithmeticZetaArgument, neg_mul, Real.sin_neg]
    rw [he]
    linarith
  obtain ⟨hw, hwi, hwn⟩ := suzukiXiReflectionWeight_vertical_sector rho hv hy
  have hr := pairedEtaFactorLogDerivative_re_phase_strip_bounds hslo hshi hscos
  have hi := pairedEtaFactorLogDerivative_im_phase_lower hslo hshi hscos hssin
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact oriented_coefficient_le _ _ hl hw hwi hwn (abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩) hi

/-- The left side with its reversed orientation has the same negative
coefficient when the sine has the opposite sign. -/
theorem suzukiEtaDyadicWeightCoefficient_reflection_left_le
    (rho : NontrivialZetaZero) {v y : ℝ}
    (hv : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re|) (hy : y ∈ Set.Icc 0 (1 / 2))
    (hcos : Real.cos (v * Real.log 2) ≤ 0) (hsin : Real.sin (v * Real.log 2) ≤ -1 / 2) :
    suzukiEtaDyadicWeightCoefficient (-I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I))
        (suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)) ≤
      -(Real.log 2 / 32) * ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ := by
  let s := suzukiArithmeticZetaArgument ((v : ℂ) + (y : ℂ) * I)
  have hslo : 1 / 2 ≤ s.re := by rw [suzukiArithmeticZetaArgument_re]; simpa using hy.1
  have hshi : s.re ≤ 1 := by
    rw [suzukiArithmeticZetaArgument_re]
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
    linarith [hy.2]
  have hscos : Real.cos (s.im * Real.log 2) ≤ 0 := by
    rwa [cos_suzukiArithmeticZetaArgument_vertical]
  have hssin : 1 / 2 ≤ Real.sin (s.im * Real.log 2) := by
    have he : Real.sin (s.im * Real.log 2) = -Real.sin (v * Real.log 2) := by
      simp [s, suzukiArithmeticZetaArgument, neg_mul, Real.sin_neg]
    rw [he]
    linarith
  let W := suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)
  let L := pairedEtaFactorLogDerivative s
  obtain ⟨hw, hwi, hwn⟩ := suzukiXiReflectionWeight_vertical_sector rho hv hy
  have hr := pairedEtaFactorLogDerivative_re_phase_strip_bounds hslo hshi hscos
  have hi := pairedEtaFactorLogDerivative_im_phase_upper hslo hshi hscos hssin
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := oriented_coefficient_le (starRingEnd ℂ W) (starRingEnd ℂ L) hl
    (by simpa [W] using hw) (by simpa [W] using hwi) (by simpa [W] using hwn)
    (abs_le.mpr ⟨by simpa [L] using (show -(2 * Real.log 2 / 3) ≤ L.re by dsimp [L]; linarith [hr.2]),
      by simpa [L] using (show L.re ≤ 2 * Real.log 2 / 3 by dsimp [L]; linarith [hr.1])⟩)
    (by simpa [L] using (show Real.log 2 / 12 ≤ -L.im by dsimp [L]; linarith))
  change -(-I * W * starRingEnd ℂ L).re ≤ -(Real.log 2 / 32) * ‖W‖
  convert h using 1
  · simp only [conj_conj, mul_re, mul_im,
      neg_re, neg_im, I_re, I_im, conj_re, conj_im]
    ring
  · simp

/-- The signed completed eta remainder on an upward vertical side,
using the original complex reflection weight and true denominator. -/
def suzukiXiEtaFiniteReflectionCompletedSide
    (rho : NontrivialZetaZero) (v : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  let z : ℂ := (v : ℂ) + (y : ℂ) * I
  let s := suzukiArithmeticZetaArgument z
  (I * suzukiXiReflectionWeight rho z * suzukiEtaFiniteCompletedNumerator N s).re /
    normSq (suzukiEtaFiniteCarrierDenominator N s)

/-- On the right, the actual complex weighted signed eta remainder
has a lower bound proportional only to the geometric weight norm. -/
theorem suzukiXiEtaFiniteReflectionCompletedSide_right_lower
    (rho : NontrivialZetaZero) (N : ℕ) {v y : ℝ}
    (hv : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re|) (hy : y ∈ Set.Icc 0 (1 / 2))
    (hcos : Real.cos (v * Real.log 2) ≤ 0) (hsin : 1 / 2 ≤ Real.sin (v * Real.log 2)) :
    -8 * ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ / Real.log 2 ≤
      suzukiXiEtaFiniteReflectionCompletedSide rho v N y := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef := suzukiEtaDyadicWeightCoefficient_reflection_right_le rho hv hy hcos hsin
  have h := suzukiEtaFiniteCompletedNumerator_quotient_lower_of_coefficient
    (I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) N
    (show 0 < Real.log 2 / 32 by positivity) (by simpa only [norm_mul, norm_I, one_mul] using hcoef)
  change _ ≤ suzukiXiEtaFiniteReflectionCompletedSide rho v N y at h
  simpa only [norm_mul, norm_I, one_mul,
    show ∀ t : ℝ, -t / (4 * (Real.log 2 / 32)) = -8 * t / Real.log 2 by intro t; ring] using h

/-- On the left, reversing the orientation gives the corresponding
upper bound for the upward density. -/
theorem suzukiXiEtaFiniteReflectionCompletedSide_left_upper
    (rho : NontrivialZetaZero) (N : ℕ) {v y : ℝ}
    (hv : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re|) (hy : y ∈ Set.Icc 0 (1 / 2))
    (hcos : Real.cos (v * Real.log 2) ≤ 0) (hsin : Real.sin (v * Real.log 2) ≤ -1 / 2) :
    suzukiXiEtaFiniteReflectionCompletedSide rho v N y ≤
      8 * ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef := suzukiEtaDyadicWeightCoefficient_reflection_left_le rho hv hy hcos hsin
  have h := suzukiEtaFiniteCompletedNumerator_quotient_lower_of_coefficient
    (-I * suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) N
    (show 0 < Real.log 2 / 32 by positivity) (by simpa only [norm_mul, norm_neg, norm_I, one_mul] using hcoef)
  have he : ∀ t : ℝ, -t / (4 * (Real.log 2 / 32)) = -8 * t / Real.log 2 := by intro t; ring
  simp only [norm_mul, norm_neg, norm_I, one_mul, neg_mul, neg_re, neg_div, he] at h
  change _ ≤ -suzukiXiEtaFiniteReflectionCompletedSide rho v N y at h
  linarith

/-- The signed completed remainder on both actual strip sides has a
uniform quartic floor at every height and every eta truncation. -/
theorem suzukiXiEtaFiniteReflectionCompletedSide_pair_lower
    (rho : NontrivialZetaZero) (N : ℕ) {R l r y : ℝ} (hR : 200 ≤ R)
    (hl : R ≤ |l|) (hr : R ≤ |r|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hy : y ∈ Set.Icc 0 (1 / 2))
    (hlcos : Real.cos (l * Real.log 2) ≤ 0) (hrcos : Real.cos (r * Real.log 2) ≤ 0)
    (hlsin : Real.sin (l * Real.log 2) ≤ -1 / 2) (hrsin : 1 / 2 ≤ Real.sin (r * Real.log 2)) :
    -(1024 * (zetaSpectralCoordinate rho.1).im ^ 2 / (Real.log 2 * R ^ 4)) ≤
      suzukiXiEtaFiniteReflectionCompletedSide rho r N y -
        suzukiXiEtaFiniteReflectionCompletedSide rho l N y := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRpos : 0 < R := by linarith
  have hgap (v : ℝ) (hv : R ≤ |v|) : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re| := by
    have ht := abs_sub_abs_le_abs_sub v (zetaSpectralCoordinate rho.1).re
    linarith
  have hlo := suzukiXiEtaFiniteReflectionCompletedSide_right_lower rho N (hgap r hr) hy hrcos hrsin
  have hhi := suzukiXiEtaFiniteReflectionCompletedSide_left_upper rho N (hgap l hl) hy hlcos hlsin
  have hnr := norm_suzukiXiReflectionWeight_vertical_le (y := y) rho hRpos hr ha
  have hnl := norm_suzukiXiReflectionWeight_vertical_le (y := y) rho hRpos hl ha
  have hnr' := mul_le_mul_of_nonneg_left hnr (show 0 ≤ 8 / Real.log 2 by positivity)
  have hnl' := mul_le_mul_of_nonneg_left hnl (show 0 ≤ 8 / Real.log 2 by positivity)
  simp only [div_eq_mul_inv, mul_inv_rev] at hlo hhi hnr' hnl' ⊢
  nlinarith

end
end RiemannGaussian
