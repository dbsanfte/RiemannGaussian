/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FermiCosineModulation
import RiemannGaussian.GaussianHalfLaplaceMoments
import RiemannGaussian.CosineTaylorEnclosure

/-!
# Exact dilation and tangent for the modulated Gaussian Laplace family

The coupled cosine stays inside the half-line Laplace integral. Its mass
has an exact Fourier evaluation, every positive dilation is exact, and the
exponential tangent uses the modulated first moment rather than the larger
unmodulated one. All widths and modulation frequencies remain available.
-/

namespace RiemannGaussian.GaussianModulatedLaplace
noncomputable section
open Filter MeasureTheory Set
open GaussianFermiZeroPair GaussianHalfLaplaceBounds GaussianHalfLaplaceMoments
open FermiCosineModulation

/-- The full cosine-modulated half-Gaussian transform. -/
def halfModulated (b δ x : ℝ) : ℝ := halfLaplace (modulate δ (window b)) x

/-- Every modulated transform converges absolutely at every real damping. -/
theorem integrable_halfModulated {b : ℝ} (hb : 0 < b) (δ x : ℝ) :
    Integrable (fun t : ℝ ↦ modulate δ (window b) t * Real.exp (-x * t)) :=
  integrable_modulate_exp δ (continuous_window b) x (integrable_window_exp hb x)

/-- The actual integral has nonnegative sign. -/
theorem halfModulated_nonneg (b δ x : ℝ) : 0 ≤ halfModulated b δ x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (modulate_nonneg δ (fun _ ↦ (Real.exp_pos _).le) t) (Real.exp_pos _).le

/-- Damping orders the entire coupled transform, including negative damping. -/
theorem halfModulated_antitone {b : ℝ} (hb : 0 < b) (δ : ℝ) :
    Antitone (halfModulated b δ) := by
  intro x y hxy
  apply integral_mono_ae (integrable_halfModulated hb δ y).integrableOn
    (integrable_halfModulated hb δ x).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have ht0 : 0 < t := ht
    nlinarith
  · exact modulate_nonneg δ (fun _ ↦ (Real.exp_pos _).le) t

/-- Positive dilation transports width, frequency and damping together. -/
theorem halfModulated_scale {r : ℝ} (hr : 0 < r) (b δ x : ℝ) :
    r * halfModulated (b * r ^ 2) (δ * r) (x * r) = halfModulated b δ x := by
  have h := integral_comp_mul_left_Ioi'
    (fun t : ℝ ↦ modulate δ (window b) t * Real.exp (-x * t)) 0 hr
  simp only [mul_zero, smul_eq_mul] at h
  have he : (fun t : ℝ ↦ modulate (δ * r) (window (b * r ^ 2)) t * Real.exp (-(x * r) * t)) =
      (fun t : ℝ ↦ modulate δ (window b) (r * t) * Real.exp (-x * (r * t))) := by
    funext t
    have hw : window (b * r ^ 2) t = window b (r * t) := by
      unfold window
      congr 1
      ring
    have hf : factor (δ * r) t = factor δ (r * t) := by
      unfold factor
      rw [mul_assoc]
    simp only [modulate, hw, hf, show -(x * r) * t = -x * (r * t) by ring]
  simpa only [halfModulated, halfLaplace, he] using h

/-- Fourier inversion evaluates the exact modulated half mass. -/
theorem halfModulated_zero {b : ℝ} (hb : 0 < b) (δ : ℝ) :
    halfModulated b δ 0 = Real.sqrt (Real.pi / b) *
      (1 + Real.exp (-δ ^ 2 / (4 * b))) / 4 := by
  have hc : Integrable (fun t : ℝ ↦ window b t * Real.cos (δ * t)) := by
    have h := (integrable_boundary hb δ).re
    simpa [Complex.mul_re, Complex.exp_re] using h
  have he : (∫ t in Ioi (0 : ℝ), window b t * Real.cos (δ * t)) =
      Real.sqrt (Real.pi / b) * Real.exp (-δ ^ 2 / (4 * b)) / 2 := by
    have h := integral_half_boundary_re hb δ
    have hr : (∫ t in Ioi (0 : ℝ), ((window b t : ℂ) *
        Complex.exp (-((δ : ℂ) * Complex.I) * (t : ℂ))).re) =
      (∫ t in Ioi (0 : ℝ), (window b t : ℂ) *
        Complex.exp (-((δ : ℂ) * Complex.I) * (t : ℂ))).re :=
      integral_re (integrable_boundary hb δ).integrableOn
    rw [← hr] at h
    simpa [Complex.mul_re, Complex.exp_re] using h
  have h0 : Integrable (window b) := by simpa using integrable_window_exp hb 0
  have hp : (fun t : ℝ ↦ modulate δ (window b) t * Real.exp (-0 * t)) =
      (fun t : ℝ ↦ (window b t + window b t * Real.cos (δ * t)) / 2) := by
    ext t
    simp [modulate, factor]
    ring
  unfold halfModulated halfLaplace
  rw [hp, integral_div, integral_add h0.integrableOn hc.integrableOn, he]
  have hv : (∫ t in Ioi (0 : ℝ), window b t) = Real.sqrt (Real.pi / b) / 2 := by
    simpa [GaussianFermiLaplaceOrder.halfGaussian] using halfGaussian_zero b
  rw [hv]
  ring

/-- Polynomial factors remain integrable with the full cosine modulation. -/
theorem integrable_atom_factor (n : ℕ) (δ x : ℝ) :
    Integrable (fun t : ℝ ↦ atom n x t * factor δ t) := by
  apply (integrable_atom n x).norm.mono' (by unfold atom window factor; fun_prop)
  filter_upwards with t
  rw [norm_mul, Real.norm_eq_abs (factor δ t), abs_of_nonneg (factor_bounds δ t).1]
  exact mul_le_of_le_one_right (norm_nonneg _) (factor_bounds δ t).2

/-- The exact tangent retains the actual modulated first moment. -/
theorem halfModulated_tangent_lower (δ x : ℝ) :
    halfModulated 1 δ 0 - x * (∫ t in Ioi (0 : ℝ), atom 1 0 t * factor δ t) ≤
      halfModulated 1 δ x := by
  have hi0 : Integrable (modulate δ (window 1)) := by
    simpa using integrable_halfModulated (by norm_num : (0 : ℝ) < 1) δ 0
  have hi1 := integrable_atom_factor 1 δ 0
  have hit : Integrable (fun t : ℝ ↦ modulate δ (window 1) t -
      x * (atom 1 0 t * factor δ t)) := hi0.sub (hi1.const_mul x)
  have hpoint (t : ℝ) : modulate δ (window 1) t - x * (atom 1 0 t * factor δ t) ≤
      modulate δ (window 1) t * Real.exp (-x * t) := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (x * t))
      (modulate_nonneg δ (g := window 1) (fun _ ↦ (Real.exp_pos _).le) t)
    simp only [atom, pow_one, neg_zero, zero_mul, Real.exp_zero, mul_one] at ⊢
    dsimp only [modulate] at h ⊢
    simp only [neg_mul] at h ⊢
    nlinarith
  have h := integral_mono (hit.integrableOn (s := Ioi (0 : ℝ)))
    (integrable_halfModulated (by norm_num : (0 : ℝ) < 1) δ x).integrableOn hpoint
  rw [integral_sub hi0.integrableOn (hi1.const_mul x).integrableOn, integral_const_mul] at h
  simpa [halfModulated, halfLaplace] using h

/-- The quartic cosine majorant gives a signed first-moment improvement
at every nonnegative modulation frequency. -/
theorem first_moment_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in Ioi (0 : ℝ), atom 1 0 t * factor δ t) ≤ 1 / 2 - δ ^ 2 / 8 + δ ^ 4 / 48 := by
  have hp : Integrable (fun t : ℝ ↦ atom 1 0 t - δ ^ 2 / 4 * atom 3 0 t +
      δ ^ 4 / 48 * atom 5 0 t) :=
    ((integrable_atom 1 0).sub ((integrable_atom 3 0).const_mul _)).add
      ((integrable_atom 5 0).const_mul _)
  have h := integral_mono_ae (integrable_atom_factor 1 δ 0).integrableOn hp.integrableOn
    (show ∀ᵐ t ∂volume.restrict (Ioi 0), atom 1 0 t * factor δ t ≤
      atom 1 0 t - δ ^ 2 / 4 * atom 3 0 t + δ ^ 4 / 48 * atom 5 0 t from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      have hc := CosineTaylorEnclosure.cos_le_quartic (mul_nonneg hδ ht0)
      have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ t * window 1 t by
        exact mul_nonneg ht0 (Real.exp_pos _).le)
      dsimp [atom, factor]
      simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
      nlinarith)
  have hi13 : IntegrableOn (fun t : ℝ ↦ atom 1 0 t - δ ^ 2 / 4 * atom 3 0 t) (Ioi 0) :=
    ((integrable_atom 1 0).sub ((integrable_atom 3 0).const_mul _)).integrableOn
  rw [integral_add hi13 ((integrable_atom 5 0).const_mul _).integrableOn,
    integral_sub (integrable_atom 1 0).integrableOn ((integrable_atom 3 0).const_mul _).integrableOn,
    integral_const_mul, integral_const_mul] at h
  change _ ≤ moment 1 0 - δ ^ 2 / 4 * moment 3 0 + δ ^ 4 / 48 * moment 5 0 at h
  have h1 := moment_one 0
  have h3 := moment_recurrence 1 0
  have h5 := moment_recurrence 3 0
  norm_num at h1 h3 h5
  have he1 : moment 1 0 = 1 / 2 := by linarith
  have he3 : moment 3 0 = 1 / 2 := by linarith
  have he5 : moment 5 0 = 1 := by linarith
  rw [he1, he3, he5] at h
  convert h using 1
  ring

end
end RiemannGaussian.GaussianModulatedLaplace
