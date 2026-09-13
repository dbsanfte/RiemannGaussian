/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SmoothedCotangentSource
import RiemannGaussian.GaussianHalfLaplaceBounds

/-!
# Quadratic ordinate loss of the complete Gaussian source

The real transform retains the cosine of the full imaginary displacement.
Its loss from the aligned transform is at most the exact second Gaussian
moment times half the squared displacement. A half-disc minimum bound
controls the analytic cotangent correction without separating its pole.
-/

namespace RiemannGaussian.GaussianComplexDisplacement
noncomputable section
open Complex MeasureTheory Set
open GaussianComplexHalfMoments GaussianFermiZeroPair GaussianFermiLaplaceOrder

/-- The exact real second Gaussian moment follows from the full complex recurrence. -/
theorem moment_two_zero_re {B : ℝ} (hB : 0 < B) :
    (moment B 2 0).re = halfGaussian B 0 / (2 * B) := by
  have h := moment_recurrence hB 0 0
  norm_num at h
  change 2 * (B : ℂ) * moment B 2 0 = transform B (0 : ℝ) at h
  rw [transform_real] at h
  have hr := congrArg Complex.re h
  norm_num at hr
  apply (eq_div_iff (by positivity : 2 * B ≠ 0)).mpr
  linarith

/-- The exact cosine loss is quadratic in the imaginary displacement,
uniformly over all nonnegative real damping and every positive Gaussian scale. -/
theorem transform_re_lower {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 ≤ z.re) :
    halfGaussian B z.re - z.im ^ 2 / (4 * B) * halfGaussian B 0 ≤
      (transform B z).re := by
  have hi0 := (integrable_atom hB 0 (z.re : ℂ)).integrableOn (s := Ioi (0 : ℝ))
  have hi2 := (integrable_atom hB 2 0).integrableOn (s := Ioi (0 : ℝ))
  have hiz := (integrable_atom hB 0 z).integrableOn (s := Ioi (0 : ℝ))
  have hp : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      (atom B 0 (z.re : ℂ) t).re - z.im ^ 2 / 2 * (atom B 2 0 t).re ≤
        (atom B 0 z t).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he : Real.exp (-z.re * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [show 0 < t from ht])
    have hg : 0 ≤ window B t := (Real.exp_pos _).le
    have hc := mul_le_mul_of_nonneg_left
      (Real.one_sub_sq_div_two_le_cos (x := z.im * t))
      (mul_nonneg hg (Real.exp_pos (-z.re * t)).le)
    have hl := mul_le_mul_of_nonneg_left he
      (show 0 ≤ z.im ^ 2 / 2 * (t ^ 2 * window B t) by positivity)
    simp only [atom, pow_zero, one_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.zero_re, Complex.zero_im, zero_mul, mul_zero,
      sub_zero, neg_zero, zero_add, Real.exp_zero, Real.cos_zero, mul_one,
      neg_mul, Real.cos_neg]
    simp only [neg_mul] at hc hl
    nlinarith only [hc, hl]
  have h := integral_mono_ae (hi0.re.sub (hi2.re.const_mul (z.im ^ 2 / 2))) hiz.re hp
  simp only [Pi.sub_apply] at h
  rw [integral_sub hi0.re (hi2.re.const_mul _), integral_const_mul,
    integral_re hi0, integral_re hi2, integral_re hiz] at h
  change (transform B (z.re : ℂ)).re - z.im ^ 2 / 2 * (moment B 2 0).re ≤
    (transform B z).re at h
  rw [transform_real, Complex.ofReal_re, moment_two_zero_re hB] at h
  convert h using 1
  ring

/-- The complete analytic cotangent-minus-pole correction loses at most
the inverse half-disc radius, including at its removed center. -/
theorem correction_re_lower {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : ‖z‖ ≤ η) (hzre : 0 ≤ z.re) :
    -(1 / η) ≤ (CotangentRegularization.correction η z).re := by
  have h := SmoothedCotangentSource.source_re_lower (F := fun _ => (0 : ℂ)) hη
    (show 0 ≤ 1 / η by positivity) (fun _ _ => analyticAt_const)
    (fun _ _ _ => by simp) (fun w hw _ => by simp [hw]) hz hzre
  simpa only [SmoothedCotangentSource.source, zero_add] using h

/-- A nearby Gaussian-cotangent source keeps its positive aligned mass,
with an explicit quadratic ordinate cost and inverse-radius correction. -/
theorem source_re_lower {B η : ℝ} (hB : 0 < B) (hη : 0 < η) {z : ℂ}
    (hz : ‖z‖ ≤ η) (hzre : 0 ≤ z.re) :
    halfGaussian B z.re - z.im ^ 2 / (4 * B) * halfGaussian B 0 - 1 / η ≤
      (SmoothedCotangentSource.source (transform B) η z).re := by
  have hg := transform_re_lower hB hzre
  have hc := correction_re_lower hη hz hzre
  simp only [SmoothedCotangentSource.source, Complex.add_re]
  linarith

end
end RiemannGaussian.GaussianComplexDisplacement
