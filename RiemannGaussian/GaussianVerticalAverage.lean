/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianPolynomialTransport

/-!
# The normalized Gaussian vertical averaging operator

The true Gaussian mass normalizes the full complex integral. Its exact
Fourier transform retains the original frequency and phase before any real
projection. These identities provide the common averaging operator for
the actual Euler series, zero poles and Archimedean correction.
-/

namespace RiemannGaussian.GaussianVerticalAverage
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianPolynomialTransport (mass mass_pos)

/-- The genuine positive vertical Gaussian, normalized by its exact mass. -/
def density (B y : ℝ) : ℝ := Real.exp (-(1 / (4 * B)) * y ^ 2) / mass B

/-- The original complex average; no real part or norm is taken in its definition. -/
def average (B : ℝ) (f : ℝ → ℂ) : ℂ := ∫ y : ℝ, (density B y : ℂ) * f y

/-- Every point of the averaging density has positive weight. -/
theorem density_pos {B : ℝ} (hB : 0 < B) (y : ℝ) : 0 < density B y :=
  div_pos (Real.exp_pos _) (mass_pos hB)

/-- The complete normalized density is integrable. -/
theorem integrable_density {B : ℝ} (hB : 0 < B) : Integrable (density B) := by
  change Integrable (fun y : ℝ => Real.exp (-(1 / (4 * B)) * y ^ 2) / mass B)
  have h := (GaussianPolynomialTransport.integrable_real_pow_gaussian hB 0).div_const (mass B)
  simpa only [pow_zero, one_mul] using h

/-- The normalization is exactly one, proved from the original Gaussian integral. -/
theorem integral_density {B : ℝ} (hB : 0 < B) : (∫ y : ℝ, density B y) = 1 := by
  simp only [density, integral_div, integral_gaussian]
  exact div_self (mass_pos hB).ne'

/-- The normalized integral commutes with real projection when the original
complex weighted carrier is integrable. -/
theorem average_re {B : ℝ} {f : ℝ → ℂ}
    (hf : Integrable (fun y : ℝ => (density B y : ℂ) * f y)) :
    (average B f).re = ∫ y : ℝ, density B y * (f y).re := by
  unfold average
  simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using! (integral_re hf).symm

/-- Every constant complex carrier is integrable against the full density. -/
theorem integrable_const {B : ℝ} (hB : 0 < B) (c : ℂ) :
    Integrable (fun y : ℝ => (density B y : ℂ) * c) :=
  (integrable_density hB).ofReal.mul_const c

/-- Constants retain their complete complex value under normalized averaging. -/
theorem average_const {B : ℝ} (hB : 0 < B) (c : ℂ) : average B (fun _ => c) = c := by
  rw [average, integral_mul_const, integral_complex_ofReal, integral_density hB]
  simp

/-- Gaussian averaging preserves the exact sum of two genuinely integrable carriers. -/
theorem average_add (B : ℝ) {f g : ℝ → ℂ}
    (hf : Integrable (fun y : ℝ => (density B y : ℂ) * f y))
    (hg : Integrable (fun y : ℝ => (density B y : ℂ) * g y)) :
    average B (fun y => f y + g y) = average B f + average B g := by
  simp only [average, mul_add]
  exact integral_add hf hg

/-- Gaussian averaging preserves the exact signed difference of two integrable carriers. -/
theorem average_sub (B : ℝ) {f g : ℝ → ℂ}
    (hf : Integrable (fun y : ℝ => (density B y : ℂ) * f y))
    (hg : Integrable (fun y : ℝ => (density B y : ℂ) * g y)) :
    average B (fun y => f y - g y) = average B f - average B g := by
  simp only [average, mul_sub]
  exact integral_sub hf hg

/-- An arbitrary complex amplitude is retained exactly by the averaging operator. -/
theorem average_const_mul (B : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    average B (fun y => c * f y) = c * average B f := by
  simp only [average, mul_left_comm (density B _ : ℂ) c, integral_const_mul]

/-- The full Fourier atom is genuinely integrable under the normalized Gaussian. -/
theorem integrable_phase {B : ℝ} (hB : 0 < B) (x : ℝ) :
    Integrable (fun y : ℝ => (density B y : ℂ) * Complex.exp (I * (y : ℂ) * (x : ℂ))) := by
  apply (integrable_density hB).mono' (by unfold density; fun_prop)
  filter_upwards with y
  simp [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos hB y)]

/-- The exact Fourier multiplier has the same physical Gaussian scale as
the original prime damping, with no phasewise inequality. -/
theorem average_phase {B : ℝ} (hB : 0 < B) (x : ℝ) :
    average B (fun y => Complex.exp (I * (y : ℂ) * (x : ℂ))) =
      (Real.exp (-B * x ^ 2) : ℂ) := by
  have he (y : ℝ) : (density B y : ℂ) * Complex.exp (I * (y : ℂ) * (x : ℂ)) =
      (mass B : ℂ)⁻¹ * GaussianPolynomialTransport.atom B x y := by
    rw [GaussianPolynomialTransport.atom_eq_gaussian_phase, density, Complex.ofReal_div]
    ring
  simp only [average, he, integral_const_mul, GaussianPolynomialTransport.integral_atom hB]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (mass_pos hB).ne'), one_mul]

end
end RiemannGaussian.GaussianVerticalAverage
