/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiSpectralWeight

/-!
# Exact Gaussian mixture for the full Fermi pair

Split any positive time-Gaussian scale into two positive parts. The centered
Fermi factor in one part supplies a positive spectral density with unit
mass. Averaging the remaining complex Gaussian against that density gives
the original analytic Fermi pair exactly, at every complex argument.

The product-integrability proof retains the oscillatory phase and
discharges the Fourier/Gaussian interchange before any zero sum is taken.
-/

namespace RiemannGaussian.GaussianFermiGaussianMixture

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiSpectralWeight

/-- The full complex Laplace atom of a time Gaussian. -/
def gaussianAtom (b : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (Real.pi / b) : ℂ) * Complex.exp (z ^ 2 / ((4 * b : ℝ) : ℂ))

/-- The original Gaussian time integrand, before its integral is evaluated. -/
def timeAtom (b : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (window b u : ℂ) * Complex.exp (-z * (u : ℂ))

/-- Every complex Laplace argument has genuine Gaussian integrability. -/
theorem integrable_timeAtom {b : ℝ} (hb : 0 < b) (z : ℂ) : Integrable (timeAtom b z) := by
  have hi := integrable_cexp_quadratic' (b := -(b : ℂ))
    (by simpa using neg_neg_of_pos hb) (-z) 0
  apply hi.congr
  filter_upwards with u
  rw [timeAtom, window, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact evaluation retains both real and imaginary parts of the Laplace
argument and the Gaussian normalization. -/
theorem integral_timeAtom {b : ℝ} (hb : 0 < b) (z : ℂ) :
    (∫ u : ℝ, timeAtom b z u) = gaussianAtom b z := by
  have hi := integral_cexp_quadratic (b := -(b : ℂ))
    (by simpa using neg_neg_of_pos hb) (-z) 0
  have hs : ((Real.pi : ℂ) / -(-(b : ℂ))) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / b) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow]
    simpa using (Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hb.le) (1 / 2 : ℝ)).symm
  calc
    _ = ∫ u : ℝ, Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2 + -z * (u : ℂ) + 0) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [timeAtom, window, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = gaussianAtom b z := by
      rw [hi, hs]
      unfold gaussianAtom
      congr 2
      push_cast
      ring

/-- The exact complex norm separates horizontal growth from vertical
Gaussian localization. -/
theorem norm_gaussianAtom (b : ℝ) (z : ℂ) :
    ‖gaussianAtom b z‖ = Real.sqrt (Real.pi / b) *
      Real.exp ((z.re ^ 2 - z.im ^ 2) / (4 * b)) := by
  unfold gaussianAtom
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  congr 2
  rw [Complex.div_ofReal_re]
  simp [pow_two]

/-- Vertical translations have a uniform norm bound, while the exact
localized Gaussian norm remains available upstream. -/
theorem norm_gaussianAtom_shift_le {b : ℝ} (hb : 0 < b) (z : ℂ) (y : ℝ) :
    ‖gaussianAtom b (z - (y : ℂ) * I)‖ ≤
      Real.sqrt (Real.pi / b) * Real.exp (z.re ^ 2 / (4 * b)) := by
  rw [norm_gaussianAtom]
  apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (z - (y : ℂ) * I).im])
    (by positivity)

/-- The actual density average of the complex Gaussian is absolutely
integrable, at every complex evaluation point. -/
theorem integrable_density_gaussianAtom {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (z : ℂ) :
    Integrable (fun y : ℝ => (density a c y : ℂ) * gaussianAtom b (z - (y : ℂ) * I)) := by
  have hd := (integrable_density ha hc).norm
  have hcont := continuous_density hc a
  apply (hd.mul_const (Real.sqrt (Real.pi / b) * Real.exp (z.re ^ 2 / (4 * b)))).mono'
    (by unfold gaussianAtom; fun_prop)
  filter_upwards with y
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (norm_gaussianAtom_shift_le hb z y) (abs_nonneg (density a c y))

/-- The scale split is an exact identity of complex time signals, before
integration or averaging. -/
theorem split_timeAtom (a b c : ℝ) (z : ℂ) (u : ℝ) :
    timeAtom b (z - (a / 2 : ℝ)) u * (signal a c u : ℂ) =
      (weight a (window (b + c)) u : ℂ) * Complex.exp (-z * (u : ℂ)) := by
  unfold timeAtom signal GaussianFermiDerivativeBounds.damped weight window
  push_cast
  calc
    _ = Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2 +
        -(z - (a : ℂ) / 2) * (u : ℂ) +
        (-(c : ℂ) * (u : ℂ) ^ 2 - (a : ℂ) / 2 * (u : ℂ))) *
          (EtaGammaSmoothing.fermi (-a * u) : ℂ) := by
      rw [Complex.exp_add, Complex.exp_add]
      ring
    _ = _ := by
      rw [show -(b : ℂ) * (u : ℂ) ^ 2 + -(z - (a : ℂ) / 2) * (u : ℂ) +
          (-(c : ℂ) * (u : ℂ) ^ 2 - (a : ℂ) / 2 * (u : ℂ)) =
          -((b : ℂ) + (c : ℂ)) * (u : ℂ) ^ 2 + -z * (u : ℂ) by ring,
        Complex.exp_add]
      ring

private def joint (a b c : ℝ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  (density a c p.1 : ℂ) * timeAtom b z p.2 *
    Complex.exp (I * (p.1 : ℂ) * (p.2 : ℂ))

private theorem integrable_joint {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (z : ℂ) : Integrable (joint a b c z) (volume.prod volume) := by
  have hp := (integrable_density ha hc).norm.mul_prod (integrable_timeAtom hb z).norm
  have hd := continuous_density hc a
  apply hp.mono' (by unfold joint timeAtom window; fun_prop)
  filter_upwards with p
  simp [joint, Complex.norm_real, Complex.norm_exp, Complex.mul_re]

/-- The full density/Gaussian interchange is justified by product
integrability. The result is the original Fermi pair with the two
positive Gaussian scales added, at every complex argument. -/
theorem integral_density_gaussianAtom_eq_pair {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (z : ℂ) :
    (∫ y : ℝ, (density a c y : ℂ) *
      gaussianAtom b (z - (a / 2 : ℝ) - (y : ℂ) * I)) =
      2 * (transform a (window (b + c)) z +
        transform a (window (b + c)) ((a : ℂ) - z)) := by
  let q : ℂ := z - (a / 2 : ℝ)
  calc
    _ = ∫ y : ℝ, ∫ u : ℝ, joint a b c q (y, u) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_timeAtom hb, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      unfold joint timeAtom
      dsimp only [q]
      rw [show -(z - (a / 2 : ℝ) - (y : ℂ) * I) * (u : ℂ) =
          -(z - (a / 2 : ℝ)) * (u : ℂ) + I * (y : ℂ) * (u : ℂ) by ring,
        Complex.exp_add]
      ring
    _ = ∫ u : ℝ, ∫ y : ℝ, joint a b c q (y, u) :=
      integral_integral_swap (integrable_joint ha hb hc q)
    _ = ∫ u : ℝ, timeAtom b q u * (2 * (signal a c u : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← integral_density_mul_cexp ha hc u, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      unfold joint
      ring
    _ = _ := by
      rw [gaussian_pair_eq_bilateral (add_pos hb hc), ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      calc
        _ = 2 * (timeAtom b q u * (signal a c u : ℂ)) := by ring
        _ = _ := by rw [split_timeAtom]

/-- The original analytic Fermi pair is exactly half a unit-mass spectral
average of complex Gaussians. Positivity of the averaging density is
available for every positive reflection parameter. -/
theorem pair_eq_gaussian_average {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hc : 0 < c) (z : ℂ) :
    transform a (window (b + c)) z + transform a (window (b + c)) ((a : ℂ) - z) =
      (1 / 2 : ℂ) * ∫ y : ℝ, (density a c y : ℂ) *
        gaussianAtom b (z - (a / 2 : ℝ) - (y : ℂ) * I) := by
  rw [integral_density_gaussianAtom_eq_pair ha hb hc]
  ring

end
end RiemannGaussian.GaussianFermiGaussianMixture
