/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaPhaseApproximation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual Gamma function and its continuous phase

Integrating the genuine digamma function on a positive vertical line gives
a logarithmic increment whose exponential is exactly the Gamma ratio.
The phase estimated in `GammaPhaseApproximation` is its imaginary part.
This retains whole turns and supplies a positive-amplitude polar formula.
-/

namespace RiemannGaussian.GammaContinuousPhase
noncomputable section
open Complex MeasureTheory Set

/-- The full logarithmic Gamma increment along a positive vertical line. -/
def logarithmicIncrement (a t : ℝ) : ℂ :=
  ∫ y : ℝ in 0..t, I * Complex.digamma ((a : ℂ) + y * I)

private theorem avoids_poles {a : ℝ} (ha : 0 < a) (t : ℝ) (m : ℕ) :
    (a : ℂ) + t * I ≠ -(m : ℂ) := by
  intro he
  have hh := congrArg Complex.re he
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero, neg_re, natCast_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) m]

private theorem continuous_density {a : ℝ} (ha : 0 < a) :
    Continuous (fun y : ℝ => I * Complex.digamma ((a : ℂ) + y * I)) := by
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_digamma_euler (by simpa using ha)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y : ℝ => (a : ℂ) + y * I) t)

/-- The logarithmic increment differentiates to the actual vertical density. -/
theorem logarithmicIncrement_hasDerivAt {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (logarithmicIncrement a)
      (I * Complex.digamma ((a : ℂ) + t * I)) t := by
  have hc := continuous_density ha
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The phase already estimated is exactly the imaginary part of the full increment. -/
theorem logarithmicIncrement_im {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (logarithmicIncrement a t).im = GammaPhaseApproximation.phase a t := by
  have hh := Complex.imCLM.intervalIntegral_comp_comm (μ := volume)
    ((continuous_density ha).intervalIntegrable 0 t)
  simpa only [Complex.imCLM_apply, Complex.I_mul_im,
    logarithmicIncrement, GammaPhaseApproximation.phase] using hh.symm

/-- Exponentiating the integrated logarithmic derivative gives the actual Gamma
ratio. No principal argument or unidentified integer winding is used. -/
theorem Gamma_eq_mul_exp {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Complex.Gamma ((a : ℂ) + t * I) =
      Complex.Gamma (a : ℂ) * Complex.exp (logarithmicIncrement a t) := by
  let g : ℝ → ℂ := fun y => Complex.Gamma ((a : ℂ) + y * I)
  have hg (y : ℝ) : HasDerivAt g
      (I * Complex.digamma ((a : ℂ) + y * I) * g y) y := by
    have hl : HasDerivAt (fun x : ℝ => (a : ℂ) + x * I) I y := by
      simpa only [Complex.ofReal_one, one_mul, id_eq] using
        ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (a : ℂ)
    have hd := (Complex.differentiableAt_Gamma _ (avoids_poles ha y)).hasDerivAt.comp y hl
    have he : deriv Complex.Gamma ((a : ℂ) + y * I) =
        Complex.digamma ((a : ℂ) + y * I) * g y := by
      rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀]
      exact Complex.Gamma_ne_zero (avoids_poles ha y)
    rw [he] at hd
    simpa only [Function.comp_def, g, mul_comm, mul_left_comm, mul_assoc] using hd
  let f : ℝ → ℂ := fun y => g y * Complex.exp (-logarithmicIncrement a y)
  have hf (y : ℝ) : HasDerivAt f 0 y := by
    have hh := (hg y).mul ((logarithmicIncrement_hasDerivAt ha y).neg.cexp)
    convert! hh using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt)
    (fun y => (hf y).deriv) t 0
  have hz : f 0 = Complex.Gamma (a : ℂ) := by simp [f, g, logarithmicIncrement]
  rw [hz] at hc
  have hh := congrArg (fun z => z * Complex.exp (logarithmicIncrement a t)) hc
  simpa only [f, g, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one] using hh

/-- The strictly positive modulus factor in the exact Gamma polar formula. -/
def amplitude (a t : ℝ) : ℝ :=
  Real.Gamma a * Real.exp (logarithmicIncrement a t).re

/-- The Gamma amplitude is strictly positive on every positive vertical line. -/
theorem amplitude_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < amplitude a t :=
  mul_pos (Real.Gamma_pos_of_pos ha) (Real.exp_pos _)

/-- The actual Gamma value has the estimated unwrapped phase and a positive
real amplitude, so its argument is correctly tracked through every turn. -/
theorem Gamma_eq_amplitude_mul_phase {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Complex.Gamma ((a : ℂ) + t * I) =
      (amplitude a t : ℂ) * Complex.exp (I * GammaPhaseApproximation.phase a t) := by
  rw [Gamma_eq_mul_exp ha, Complex.Gamma_ofReal]
  have he : logarithmicIncrement a t =
      ((logarithmicIncrement a t).re : ℂ) +
        I * GammaPhaseApproximation.phase a t := by
    rw [← logarithmicIncrement_im ha]
    simpa only [mul_comm] using (Complex.re_add_im (logarithmicIncrement a t)).symm
  rw [he, Complex.exp_add]
  simp only [amplitude, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc]

end
end RiemannGaussian.GammaContinuousPhase
