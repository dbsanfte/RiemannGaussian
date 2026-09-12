/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianVerticalAverage
import RiemannGaussian.GaussianSimplePoleHeat
import RiemannGaussian.GaussianComplexHalfMoments

/-!
# Exact Gaussian averaging of a pole with full complex displacement

The complete product integral retains the imaginary displacement of every
pole. Fourier evaluation and Fubini identify its normalized vertical
average with the original complex half-Gaussian transform. Subtracting the
center pole then gives exactly the existing cubic-decay remainder.
-/

namespace RiemannGaussian.GaussianComplexPoleAverage
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianVerticalAverage
open GaussianSimplePoleHeat (laplace)

private def joint (B : ℝ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  (density B p.1 : ℂ) * laplace 0 z p.2 * Complex.exp (I * (p.1 : ℂ) * (p.2 : ℂ))

private theorem integrable_joint {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    Integrable (joint B z) (volume.prod (volume.restrict (Ioi 0))) := by
  have hp := (integrable_density hB).mul_prod (GaussianSimplePoleHeat.integrableOn_laplace 0 hz).norm
  apply hp.mono' (by unfold joint laplace density; fun_prop)
  filter_upwards with p
  simp [joint, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos hB p.1)]

private theorem laplace_shift (z : ℂ) (y t : ℝ) :
    laplace 0 (z - I * y) t = laplace 0 z t * Complex.exp (I * (y : ℂ) * (t : ℂ)) := by
  unfold laplace
  rw [show -(z - I * y) * t = -z * t + I * y * t by ring, Complex.exp_add]
  ring

private theorem integral_joint_time {z : ℂ} (hz : 0 < z.re) (B y : ℝ) :
    (∫ t : ℝ in Ioi 0, joint B z (y, t)) = (density B y : ℂ) * (z - I * y)⁻¹ := by
  have he (t : ℝ) : joint B z (y, t) = (density B y : ℂ) * laplace 0 (z - I * y) t := by
    rw [laplace_shift]
    unfold joint
    ring
  simp_rw [he]
  rw [integral_const_mul, GaussianSimplePoleHeat.integral_laplace 0 (by simpa using hz)]
  simp

private theorem integral_joint_frequency {B : ℝ} (hB : 0 < B) (z : ℂ) (t : ℝ) :
    (∫ y : ℝ, joint B z (y, t)) = GaussianComplexHalfMoments.atom B 0 z t := by
  have he (y : ℝ) : joint B z (y, t) = laplace 0 z t *
      ((density B y : ℂ) * Complex.exp (I * (y : ℂ) * (t : ℂ))) := by unfold joint; ring
  simp_rw [he]
  rw [integral_const_mul, ← GaussianVerticalAverage.average, average_phase hB]
  simp only [laplace, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    GaussianComplexHalfMoments.atom, GaussianFermiZeroPair.window]
  ring

/-- A pole at every complex displacement with positive real part is
genuinely integrable under the full normalized vertical Gaussian. -/
theorem integrable_pole {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => (density B y : ℂ) * (z - I * y)⁻¹) := by
  have h := (integrable_joint hB hz).integral_prod_left
  simpa only [integral_joint_time hz] using h

/-- The original complex pole average equals the full half-Gaussian
transform, with all imaginary displacement and normalization retained. -/
theorem average_pole {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    average B (fun y => (z - I * y)⁻¹) = GaussianComplexHalfMoments.transform B z := by
  have h := integral_integral_swap (f := fun y t => joint B z (y, t)) (integrable_joint hB hz)
  simpa only [integral_joint_time hz, integral_joint_frequency hB,
    GaussianVerticalAverage.average, GaussianComplexHalfMoments.transform,
    GaussianComplexHalfMoments.moment] using h

/-- Subtracting the complete center pole preserves actual integrability. -/
theorem integrable_pole_sub_center {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => (density B y : ℂ) * ((z - I * y)⁻¹ - z⁻¹)) := by
  apply ((integrable_pole hB hz).sub (integrable_const hB z⁻¹)).congr
  filter_upwards with y
  simp only [Pi.sub_apply, mul_sub]

/-- The full signed smoothing correction is exactly the original complex
transform minus its center pole, before any zero sum or norm is taken. -/
theorem average_pole_sub_center {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    average B (fun y => (z - I * y)⁻¹ - z⁻¹) =
      GaussianComplexHalfMoments.transform B z - 1 / z := by
  rw [average_sub B (integrable_pole hB hz) (integrable_const hB z⁻¹),
    average_pole hB hz, average_const hB, one_div]

/-- The exact Poisson average is the real projection of the complete
complex transform. The complex identity remains available upstream. -/
theorem integral_poisson {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 < z.re) :
    (∫ y : ℝ, density B y * (z.re / Complex.normSq (z - I * y))) =
      (GaussianComplexHalfMoments.transform B z).re := by
  have h := congrArg Complex.re (average_pole hB hz)
  rw [average_re (integrable_pole hB hz)] at h
  simpa only [Complex.inv_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero] using h

end
end RiemannGaussian.GaussianComplexPoleAverage
