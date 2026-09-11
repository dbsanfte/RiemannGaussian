/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiSpectralWeight

/-!
# Exact phase evaluation under the Fermi spectral average

The proved characteristic function evaluates every shifted cosine without
discarding its phase. Multiplication by the remaining time Gaussian
recombines the two positive scales into the original Fermi weight. These
identities apply to every logarithmic prime-power frequency.
-/

namespace RiemannGaussian.GaussianFermiCosineAverage

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiSpectralWeight GaussianFermiPairDecay
open GaussianFermiDerivativeBounds GaussianFermiZeroPair

/-- The literal centered time amplitude is strictly positive. -/
theorem signal_pos (a b u : ℝ) : 0 < signal a b u := damped_pos a b (a / 2) u

/-- The centered amplitude retains Gaussian domination at every real
time, including both time directions. -/
theorem signal_le_window {a : ℝ} (ha : 0 ≤ a) (b u : ℝ) :
    signal a b u ≤ window b u := by
  have h := damped_le_exp_abs (a := a) (b := b) (x := a / 2) (δ := 0)
    (by linarith) (by linarith) u
  simpa only [signal, zero_mul, add_zero, window] using h

/-- The Gaussian scale split recombines pointwise in the original real
Fermi signal. -/
theorem signal_split (a b c u : ℝ) : window b u * signal a c u = signal a (b + c) u := by
  unfold window signal damped
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

private theorem shifted_phase (d t x y : ℝ) :
    (d : ℂ) * Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ)) =
      Complex.exp (I * (t : ℂ) * (x : ℂ)) *
        starRingEnd ℂ ((d : ℂ) * Complex.exp (I * (y : ℂ) * (x : ℂ))) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [show I * ((t - y : ℝ) : ℂ) * (x : ℂ) =
      I * (t : ℂ) * (x : ℂ) + (-I) * (y : ℂ) * (x : ℂ) by push_cast; ring,
    Complex.exp_add]
  ring

/-- The full complex character is integrable against the actual spectral
density at every real frequency. -/
theorem integrable_density_phase {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (x : ℝ) :
    Integrable (fun y : ℝ => (density a c y : ℂ) * Complex.exp (I * (y : ℂ) * (x : ℂ))) := by
  apply (integrable_oscillatory (integrable_density ha hc) (-x)).congr
  filter_upwards with y
  congr 1
  congr 1
  push_cast
  ring

/-- Frequency translation preserves integrability, with the exact complex
conjugation retained. -/
theorem integrable_density_shifted_phase {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (t x : ℝ) :
    Integrable (fun y : ℝ => (density a c y : ℂ) *
      Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))) := by
  apply ((integrable_density_phase ha hc (-x)).const_mul
    (Complex.exp (I * (t : ℂ) * (x : ℂ)))).congr
  filter_upwards with y
  rw [shifted_phase]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.ofReal_neg, Complex.conj_I]
  congr 2
  congr 1
  ring

/-- Exact evaluation of the translated complex character. -/
theorem integral_density_shifted_phase {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (t x : ℝ) :
    (∫ y : ℝ, (density a c y : ℂ) *
      Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))) =
      Complex.exp (I * (t : ℂ) * (x : ℂ)) * (2 * (signal a c x : ℂ)) := by
  calc
    _ = Complex.exp (I * (t : ℂ) * (x : ℂ)) *
        starRingEnd ℂ (∫ y : ℝ, (density a c y : ℂ) *
          Complex.exp (I * (y : ℂ) * (x : ℂ))) := by
      rw [← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => shifted_phase (density a c y) t x y
    _ = _ := by
      rw [integral_density_mul_cexp ha hc]
      have htwo : starRingEnd ℂ (2 : ℂ) = 2 := map_natCast (starRingEnd ℂ) 2
      simp [htwo]

/-- The actual shifted cosine integrand is absolutely integrable. -/
theorem integrable_density_cosine {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (t x : ℝ) :
    Integrable (fun y : ℝ => density a c y * Real.cos ((t - y) * x)) := by
  have hr : Integrable (fun y : ℝ => ((density a c y : ℂ) *
      Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))).re) :=
    (integrable_density_shifted_phase ha hc t x).re
  convert hr using 1
  funext y
  simp [Complex.mul_re, Complex.exp_re]

/-- Every shifted cosine is evaluated by the original Fermi amplitude,
including its exact physical phase and normalization. -/
theorem integral_density_cosine {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (t x : ℝ) :
    (∫ y : ℝ, density a c y * Real.cos ((t - y) * x)) =
      2 * signal a c x * Real.cos (t * x) := by
  have hr : (∫ y : ℝ, ((density a c y : ℂ) *
      Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))).re) =
      (∫ y : ℝ, (density a c y : ℂ) *
        Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))).re :=
    integral_re (integrable_density_shifted_phase ha hc t x)
  calc
    _ = (∫ y : ℝ, (density a c y : ℂ) *
        Complex.exp (I * ((t - y : ℝ) : ℂ) * (x : ℂ))).re := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re,
        Complex.I_re, Complex.I_im, zero_mul, zero_sub, neg_zero, mul_zero, sub_zero,
        Complex.mul_im, one_mul, zero_add, add_zero, Complex.mul_re, Real.exp_zero] using hr
    _ = _ := by
      rw [integral_density_shifted_phase ha hc]
      simp [Complex.mul_re, Complex.exp_re]
      ring

end
end RiemannGaussian.GaussianFermiCosineAverage
