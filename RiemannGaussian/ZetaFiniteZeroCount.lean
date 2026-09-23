/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSymmetry
import RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog

/-!
# The complete finite zero count and its quarter-contour formula

This uses the existing complete xi divisor theorem, with its actual analytic
multiplicities. The count includes both signs of the ordinate. The Gaussian
weight at parameter zero is exactly two; both normalization factors are
retained in the quarter-contour identity used for numerical counting.
-/

namespace RiemannGaussian.ZetaFiniteZeroCount
noncomputable section
open Complex MeasureTheory Set
open scoped ComplexConjugate

/-- The complete multiplicity-weighted count of nontrivial zeta zeros in
the symmetric closed height window. -/
def count (T : ℝ) : ℕ :=
  ∑ ρ ∈ spectralZetaZeroWindow T, analyticZetaZeroMultiplicity ρ

private theorem zero_gaussian (z : ℂ) :
    complexSymmetricGaussian 0 0 z = 2 := by
  norm_num [complexSymmetricGaussian, complexTranslatedGaussian]

private theorem zero_integrand (z : ℂ) :
    gaussianXiSpectralIntegrand 0 0 z = 2 * xiSpectralNegativeLogDerivative z := by
  rw [gaussianXiSpectralIntegrand, zero_gaussian]

/-- The zero-parameter symmetric Gaussian is twice the literal zero count. -/
theorem gaussian_window_zero (T : ℝ) : gaussianXiWindowZeroSum 0 0 T = 2 * (count T : ℂ) := by
  simp only [gaussianXiWindowZeroSum, zetaSymmetricGaussianDistinctZeroSummand,
    zero_gaussian, count, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

private theorem continuous_lower :
    Continuous (fun x : ℝ => xiSpectralNegativeLogDerivative ((x : ℂ) - I)) := by
  apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
  intro x
  apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
  apply riemannXiSpectral_ne_zero_of_half_le_abs_im
  norm_num

private theorem continuous_right {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    Continuous (fun y : ℝ => xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)) := by
  apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
  intro y
  apply analyticAt_xiSpectralNegativeLogDerivative_of_ne
  apply riemannXiSpectral_ne_zero_of_abs_re_ne
    (by simpa only [zetaSpectralCoordinate_re] using hb)
  simpa using abs_of_nonneg hT

/-- The existing residue theorem specializes to the literal complete count. -/
theorem contour_eq_count {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    (∫ x : ℝ in -T..T, xiSpectralNegativeLogDerivative ((x : ℂ) - I)) +
      I * (∫ y : ℝ in (-1 : ℝ)..1,
        xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)) =
      -(Real.pi : ℂ) * (count T : ℂ) := by
  have hh := intervalIntegral_gaussianXiSpectralIntegrand_lower_add_vertical
    0 0 hT (by simpa only [zetaSpectralCoordinate_re] using hb)
  simp_rw [zero_integrand, intervalIntegral.integral_const_mul, gaussian_window_zero] at hh
  linear_combination (1 / 2 : ℂ) * hh

private theorem integral_even (f : ℝ → ℝ) (hf : Continuous f)
    (he : Function.Even f) (T : ℝ) :
    (∫ x : ℝ in -T..T, f x) = 2 * ∫ x : ℝ in 0..T, f x := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)]
  have hh := intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := T)
  have heq : (fun x => f (-x)) = f := funext he
  rw [heq] at hh
  simp only [neg_zero] at hh
  rw [← hh]
  ring

private theorem lower_re_even : Function.Even
    (fun x : ℝ => (xiSpectralNegativeLogDerivative ((x : ℂ) - I)).re) := by
  intro x
  dsimp only
  have he : ((-x : ℝ) : ℂ) - I = -conj ((x : ℂ) - I) := by
    simp [sub_eq_add_neg, add_comm]
  rw [he, xiSpectralNegativeLogDerivative_neg, xiSpectralNegativeLogDerivative_conj]
  simp

private theorem right_im_even (T : ℝ) : Function.Even
    (fun y : ℝ => (xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im) := by
  intro y
  dsimp only
  have he : (T : ℂ) + (-y : ℝ) * I = conj ((T : ℂ) + y * I) := by simp
  rw [he, xiSpectralNegativeLogDerivative_conj]
  simp

private theorem lower_value (x : ℝ) :
    xiSpectralNegativeLogDerivative ((x : ℂ) - I) =
      -logDeriv riemannXi ((3 / 2 : ℂ) + x * I) := by
  have he : completedSpectralCoordinate ((x : ℂ) - I) = (3 / 2 : ℂ) + x * I := by
    unfold completedSpectralCoordinate
    simp [mul_sub, mul_comm]
    ring
  simp only [xiSpectralNegativeLogDerivative, he, logDeriv_apply, neg_div]

private theorem right_value (T y : ℝ) :
    xiSpectralNegativeLogDerivative ((T : ℂ) + y * I) =
      -logDeriv riemannXi (((1 / 2 - y : ℝ) : ℂ) + T * I) := by
  have he : completedSpectralCoordinate ((T : ℂ) + y * I) =
      ((1 / 2 - y : ℝ) : ℂ) + T * I := by
    unfold completedSpectralCoordinate
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp only [xiSpectralNegativeLogDerivative, he, logDeriv_apply, neg_div]

/-- The complete symmetric count equals the unwrapped xi phase on one
quarter contour. The horizontal side goes back to the critical line. -/
theorem quarter_contour {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T) :
    Real.pi * (count T : ℝ) = 2 *
      ((∫ t : ℝ in 0..T, (logDeriv riemannXi ((3 / 2 : ℂ) + t * I)).re) -
        ∫ σ : ℝ in (1 / 2 : ℝ)..(3 / 2),
          (logDeriv riemannXi ((σ : ℂ) + T * I)).im) := by
  have hc := congrArg Complex.re (contour_eq_count hT hb)
  have hl : (∫ x : ℝ in -T..T,
      xiSpectralNegativeLogDerivative ((x : ℂ) - I)).re =
      2 * ∫ x : ℝ in 0..T, (xiSpectralNegativeLogDerivative ((x : ℂ) - I)).re := by
    have hi := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
      (continuous_lower.intervalIntegrable (-T) T)
    simp only [Complex.reCLM_apply] at hi
    rw [← hi]
    exact integral_even _ (Complex.continuous_re.comp continuous_lower) lower_re_even T
  have hr : (∫ y : ℝ in (-1 : ℝ)..1,
      xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im =
      2 * ∫ y : ℝ in (-1 : ℝ)..0,
        (xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im := by
    have hi := Complex.imCLM.intervalIntegral_comp_comm (μ := volume)
      ((continuous_right hT hb).intervalIntegrable (-1) 1)
    simp only [Complex.imCLM_apply] at hi
    rw [← hi]
    have hh := integral_even _ (Complex.continuous_im.comp (continuous_right hT hb))
      (right_im_even T) 1
    simp only [Function.comp_def] at hh
    have hn := intervalIntegral.integral_comp_neg
      (fun y : ℝ => (xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im)
      (a := (0 : ℝ)) (b := 1)
    have heq : (fun y : ℝ => (xiSpectralNegativeLogDerivative ((T : ℂ) + ((-y : ℝ) : ℂ) * I)).im) =
        (fun y : ℝ => (xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im) :=
      funext (right_im_even T)
    rw [heq] at hn
    simp only [neg_zero] at hn
    rw [hh, hn]
  simp only [add_re, I_mul_re, hl, hr] at hc
  norm_num at hc
  have hlo : (∫ x : ℝ in 0..T,
      (xiSpectralNegativeLogDerivative ((x : ℂ) - I)).re) =
      -(∫ x : ℝ in 0..T, (logDeriv riemannXi ((3 / 2 : ℂ) + x * I)).re) := by
    simp_rw [lower_value, neg_re, intervalIntegral.integral_neg]
  have hri : (∫ y : ℝ in (-1 : ℝ)..0,
      (xiSpectralNegativeLogDerivative ((T : ℂ) + y * I)).im) =
      -(∫ σ : ℝ in (1 / 2 : ℝ)..(3 / 2),
        (logDeriv riemannXi ((σ : ℂ) + T * I)).im) := by
    simp_rw [right_value, neg_im, intervalIntegral.integral_neg]
    rw [intervalIntegral.integral_comp_sub_left
      (fun σ : ℝ => (logDeriv riemannXi ((σ : ℂ) + T * I)).im)]
    norm_num
  rw [hlo, hri] at hc
  linarith

end
end RiemannGaussian.ZetaFiniteZeroCount
