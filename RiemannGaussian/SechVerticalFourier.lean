/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SechVerticalMoments
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Positive Fourier transform of the exact vertical detector

A logistic change of variables identifies the whole Fourier integral of
the hyperbolic-secant density with a beta integral. Its parameters are
complex conjugates, so the beta--gamma identity gives an exact gamma norm
square. Positivity follows with no frequency restriction or numerical
constant. The complex identity is retained before taking its real part.
-/

namespace RiemannGaussian.SechVerticalFourier
noncomputable section
open Complex MeasureTheory Set Filter
open SechVerticalKernel SechVerticalMoments
open scoped ComplexConjugate

/-- Every finite logistic coordinate lies in the open unit interval. -/
theorem survival_mem (u : ℝ) : survival u ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · unfold survival
    positivity
  · unfold survival
    apply (div_lt_one (by positivity : 0 < 1 + Real.exp (-2 * u))).mpr
    linarith

/-- The logistic survival coordinate is injective on the whole line. -/
theorem survival_injective : Function.Injective survival := by
  intro u v h
  unfold survival at h
  have h := (div_eq_div_iff (by positivity : 1 + Real.exp (-2 * u) ≠ 0)
    (by positivity : 1 + Real.exp (-2 * v) ≠ 0)).mp h
  have he : Real.exp (-2 * u) = Real.exp (-2 * v) := by nlinarith
  have he := Real.exp_injective he
  linarith

/-- The logistic image is exactly the open unit interval; both endpoints
are approached only at infinite physical coordinates. -/
theorem survival_image : survival '' (univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨u, _, rfl⟩
    exact survival_mem u
  · intro hp
    let u := -Real.log (p / (1 - p)) / 2
    have he : Real.exp (-2 * u) = p / (1 - p) := by
      rw [show -2 * u = Real.log (p / (1 - p)) by dsimp [u]; ring]
      exact Real.exp_log (div_pos hp.1 (sub_pos.mpr hp.2))
    refine ⟨u, mem_univ _, ?_⟩
    unfold survival
    rw [he]
    field_simp [(sub_pos.mpr hp.2).ne']
    ring

/-- The difference of the two endpoint logarithms retains the physical
coordinate exactly, before multiplying by an oscillatory frequency. -/
theorem log_survival_sub (u : ℝ) :
    Real.log (survival u) - Real.log (1 - survival u) = -2 * u := by
  have hE : 1 + Real.exp (-2 * u) ≠ 0 := by positivity
  have hc : 1 - survival u = 1 / (1 + Real.exp (-2 * u)) := by
    unfold survival
    field_simp
    ring
  rw [hc, survival, Real.log_div (Real.exp_pos _).ne' hE,
    Real.log_div one_ne_zero hE, Real.log_one, Real.log_exp]
  ring

/-- The original complex Fourier mode, with its sign and frequency intact. -/
def mode (v u : ℝ) : ℂ := Complex.exp (Complex.I * (v : ℂ) * (u : ℂ))

/-- Every real-frequency mode has norm one. -/
theorem norm_mode (v u : ℝ) : ‖mode v u‖ = 1 := by
  simp [mode, Complex.norm_exp]

/-- The whole complex Fourier carrier is absolutely integrable. -/
theorem integrable_mode (v : ℝ) :
    Integrable (fun u : ℝ => (density u : ℂ) * mode v u) := by
  have hc : Continuous (fun u : ℝ => (density u : ℂ) * mode v u) :=
    (Complex.continuous_ofReal.comp continuous_density).mul (by unfold mode; fun_prop)
  apply integrable_density.mono' hc.aestronglyMeasurable
  filter_upwards [] with u
  rw [norm_mul, norm_mode, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (density_nonneg u)]

private def betaMode (v p : ℝ) : ℂ :=
  (p : ℂ) ^ (-(Complex.I * (v : ℂ) / 2)) *
    (1 - (p : ℂ)) ^ (Complex.I * (v : ℂ) / 2)

private theorem betaMode_survival (v u : ℝ) : betaMode v (survival u) = mode v u := by
  have hp := survival_mem u
  have hq : 0 < 1 - survival u := sub_pos.mpr hp.2
  have hc : (1 - (survival u : ℂ)) = ((1 - survival u : ℝ) : ℂ) := by simp
  unfold betaMode mode
  rw [hc, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.1.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hp.1.le, ← Complex.ofReal_log hq.le, ← Complex.exp_add]
  congr 1
  have h : ((Real.log (survival u) : ℝ) : ℂ) -
      ((Real.log (1 - survival u) : ℝ) : ℂ) = -2 * (u : ℂ) := by
    exact_mod_cast log_survival_sub u
  linear_combination -(Complex.I * (v : ℂ) / 2) * h

/-- The full complex detector transform is a genuine beta integral.
The change of variables uses the exact Jacobian on the whole real line. -/
theorem integral_mode_eq_beta (v : ℝ) :
    (∫ u : ℝ, (density u : ℂ) * mode v u) =
      Complex.betaIntegral (1 - Complex.I * (v : ℂ) / 2) (1 + Complex.I * (v : ℂ) / 2) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (hasDerivAt_survival u).hasDerivWithinAt)
    survival_injective.injOn (betaMode v)
  rw [survival_image, setIntegral_univ] at h
  simp_rw [abs_neg, abs_of_nonneg (density_nonneg _), betaMode_survival,
    Complex.real_smul] at h
  rw [← h, Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro p _
  unfold betaMode
  congr 2 <;> ring

/-- The complete Fourier transform is an exact nonnegative gamma norm
square. All frequencies are treated at once. -/
theorem integral_mode_eq_gamma_norm (v : ℝ) :
    (∫ u : ℝ, (density u : ℂ) * mode v u) =
      ((‖Complex.Gamma (1 + Complex.I * (v : ℂ) / 2)‖ ^ 2 : ℝ) : ℂ) := by
  rw [integral_mode_eq_beta, Complex.betaIntegral_eq_Gamma_mul_div _ _
    (by norm_num) (by norm_num)]
  rw [show (1 - Complex.I * (v : ℂ) / 2) + (1 + Complex.I * (v : ℂ) / 2) = 2 by ring]
  have hG : Complex.Gamma 2 = 1 := by
    norm_num
  rw [hG, div_one]
  have hc : 1 - Complex.I * (v : ℂ) / 2 = conj (1 + Complex.I * (v : ℂ) / 2) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
    ring
  rw [hc, Complex.Gamma_conj, mul_comm, Complex.mul_conj, ← Complex.sq_norm]

/-- The exact real multiplier applied to each frequency by vertical
averaging. It retains the gamma factor instead of an absolute envelope. -/
def attenuation (v : ℝ) : ℝ := ‖Complex.Gamma (1 + Complex.I * (v : ℂ) / 2)‖ ^ 2

/-- The cosine channel is absolutely integrable against the original density. -/
theorem integrable_cos (v : ℝ) : Integrable (fun u : ℝ => density u * Real.cos (v * u)) := by
  have h := Complex.reCLM.integrable_comp (integrable_mode v)
  simpa [mode, Complex.exp_re] using! h

/-- The sine channel is absolutely integrable against the original density. -/
theorem integrable_sin (v : ℝ) : Integrable (fun u : ℝ => density u * Real.sin (v * u)) := by
  have h := Complex.imCLM.integrable_comp (integrable_mode v)
  simpa [mode, Complex.exp_im] using! h

/-- The original cosine transform is exactly the gamma norm square. -/
theorem integral_cos (v : ℝ) :
    (∫ u : ℝ, density u * Real.cos (v * u)) = attenuation v := by
  have h := Complex.reCLM.integral_comp_comm (integrable_mode v)
  rw [integral_mode_eq_gamma_norm] at h
  simpa [mode, Complex.exp_re, attenuation, pow_two] using h

/-- The complete odd channel cancels exactly, before any phase sum. -/
theorem integral_sin (v : ℝ) : (∫ u : ℝ, density u * Real.sin (v * u)) = 0 := by
  have h := Complex.imCLM.integral_comp_comm (integrable_mode v)
  rw [integral_mode_eq_gamma_norm] at h
  simpa [mode, Complex.exp_im, pow_two] using h

/-- Every frequency multiplier is strictly positive. -/
theorem attenuation_pos (v : ℝ) : 0 < attenuation v := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact Complex.Gamma_ne_zero_of_re_pos (by norm_num)

/-- The original mass-one density attenuates every frequency by at most one. -/
theorem attenuation_le_one (v : ℝ) : attenuation v ≤ 1 := by
  rw [← integral_cos, ← integral_density]
  exact integral_mono (integrable_cos v) integrable_density
    (fun u => mul_le_of_le_one_right (density_nonneg u) (Real.cos_le_one _))

/-- Common vertical averaging preserves a cosine phase with a strictly
positive multiplier; its odd sine contribution cancels exactly. -/
theorem integral_cos_shift (x v : ℝ) :
    (∫ u : ℝ, density u * Real.cos (x + v * u)) = attenuation v * Real.cos x := by
  rw [show (fun u : ℝ => density u * Real.cos (x + v * u)) =
      (fun u => Real.cos x * (density u * Real.cos (v * u)) -
        Real.sin x * (density u * Real.sin (v * u))) by
      funext u; rw [Real.cos_add]; ring,
    integral_sub ((integrable_cos v).const_mul _) ((integrable_sin v).const_mul _),
    integral_const_mul, integral_const_mul, integral_cos, integral_sin]
  ring

end
end RiemannGaussian.SechVerticalFourier
