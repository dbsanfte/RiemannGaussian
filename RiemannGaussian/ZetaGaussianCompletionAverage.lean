/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianVerticalAverage
import RiemannGaussian.ZetaRegularCorrectionVariation
import RiemannGaussian.GaussianDigammaLogEnvelope

/-!
# The complete complex Archimedean response under Gaussian averaging

The actual completion correction is uniformly Lipschitz on the positive
half-plane. The exact first absolute Gaussian moment therefore controls
its full complex averaging error. Its signed integral remains available
before that bound is applied; no Archimedean term is omitted.
-/

namespace RiemannGaussian.ZetaGaussianCompletionAverage
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianVerticalAverage
open GaussianPolynomialTransport (mass mass_pos)

/-- The original complete complex completion correction under the normalized Gaussian. -/
def response (B : ℝ) (s : ℂ) : ℂ :=
  GaussianVerticalAverage.average B (fun y => zetaGlobalRegularCorrection (s - I * y))

/-- The normalized Gaussian first absolute moment is genuinely integrable. -/
theorem integrable_density_abs {B : ℝ} (hB : 0 < B) :
    Integrable (fun y : ℝ => density B y * |y|) := by
  have h := (GaussianDigammaLogEnvelope.integrable_abs_mul_gaussian
    (by positivity : 0 < 1 / (4 * B))).div_const (mass B)
  apply h.congr
  filter_upwards with y
  unfold density
  ring

/-- The exact physical first absolute moment is `4B/mass(B)`. -/
theorem integral_density_abs {B : ℝ} (hB : 0 < B) :
    (∫ y : ℝ, density B y * |y|) = 4 * B / mass B := by
  have he (y : ℝ) : density B y * |y| =
      (|y| * Real.exp (-(1 / (4 * B)) * y ^ 2)) / mass B := by unfold density; ring
  simp only [he, integral_div]
  rw [GaussianDigammaLogEnvelope.integral_abs_mul_gaussian (by positivity : 0 < 1 / (4 * B))]
  simp only [one_div, inv_inv]

/-- The complete correction's displacement is controlled before averaging,
uniformly in its original height and without projection to a real part. -/
theorem norm_displacement_le {s : ℂ} (hs : 0 < s.re) (y : ℝ) :
    ‖zetaGlobalRegularCorrection (s - I * y) - zetaGlobalRegularCorrection s‖ ≤ |y| := by
  have h := norm_zetaGlobalRegularCorrection_sub_le hs
    (w := s - I * y) (by simpa using hs)
  simpa only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] using h

/-- The original full complex completion is integrable against the Gaussian
throughout the positive half-plane, including at every Euler-boundary center. -/
theorem integrable_response {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun y : ℝ => (density B y : ℂ) * zetaGlobalRegularCorrection (s - I * y)) := by
  have hc : Continuous (fun y : ℝ => zetaGlobalRegularCorrection (s - I * y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (hasDerivAt_zetaGlobalRegularCorrection (by simpa using hs)).continuousAt.comp (by fun_prop)
  have hm : Integrable (fun y : ℝ => density B y * ‖zetaGlobalRegularCorrection s‖ + density B y * |y|) :=
    ((integrable_density hB).mul_const _).add (integrable_density_abs hB)
  apply hm.mono' ?_ ?_
  · have hd : Continuous (fun y : ℝ => (density B y : ℂ)) := by unfold density; fun_prop
    exact (hd.mul hc).aestronglyMeasurable
  · filter_upwards with y
    have ht := norm_add_le
      (zetaGlobalRegularCorrection (s - I * y) - zetaGlobalRegularCorrection s)
      (zetaGlobalRegularCorrection s)
    rw [sub_add_cancel] at ht
    have hh : ‖zetaGlobalRegularCorrection (s - I * y)‖ ≤ ‖zetaGlobalRegularCorrection s‖ + |y| := by
      linarith [norm_displacement_le hs y]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (density_pos hB y)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hh (density_pos hB y).le

/-- Real projection keeps the exact original Archimedean integral. -/
theorem response_re {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 0 < s.re) :
    (response B s).re = ∫ y : ℝ, density B y * (zetaGlobalRegularCorrection (s - I * y)).re :=
  average_re (integrable_response hB hs)

/-- The original complex Archimedean averaging error has an explicit
first-moment allowance, independent of the center's ordinate. -/
theorem norm_response_sub_center_le {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 0 < s.re) :
    ‖response B s - zetaGlobalRegularCorrection s‖ ≤ 4 * B / mass B := by
  have hi : Integrable (fun y : ℝ => (density B y : ℂ) *
      (zetaGlobalRegularCorrection (s - I * y) - zetaGlobalRegularCorrection s)) := by
    apply ((integrable_response hB hs).sub
      (GaussianVerticalAverage.integrable_const hB (zetaGlobalRegularCorrection s))).congr
    filter_upwards with y
    simp only [Pi.sub_apply, mul_sub]
  rw [response, ← average_const hB (zetaGlobalRegularCorrection s),
    ← average_sub B (integrable_response hB hs) (GaussianVerticalAverage.integrable_const hB _)]
  calc
    _ ≤ ∫ y : ℝ, ‖(density B y : ℂ) *
        (zetaGlobalRegularCorrection (s - I * y) - zetaGlobalRegularCorrection s)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, density B y * |y| := by
      apply integral_mono_ae hi.norm (integrable_density_abs hB)
      filter_upwards with y
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (density_pos hB y)]
      exact mul_le_mul_of_nonneg_left (norm_displacement_le hs y) (density_pos hB y).le
    _ = _ := integral_density_abs hB

end
end RiemannGaussian.ZetaGaussianCompletionAverage
