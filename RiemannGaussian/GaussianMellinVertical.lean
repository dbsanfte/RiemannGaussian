import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The full vertical Gaussian Mellin atom

The complex Gaussian on a vertical line is integrable for every positive
heat time. Its integral is evaluated exactly, including the normalization.
The abscissa cancels only after integration; the pointwise complex phase
and its precise quadratic expansion remain available upstream.
-/

open Complex MeasureTheory

namespace RiemannGaussian

noncomputable section

/-- The exact quadratic phase of a Gaussian Mellin atom on its original vertical line. -/
theorem gaussianMellin_vertical_eq_quadratic (b tau sigma t : ℝ) :
    Complex.exp ((b : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
      (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2) =
    Complex.exp (-(tau : ℂ) * (t : ℂ) ^ 2 +
      (((b + 2 * tau * sigma : ℝ) : ℂ) * I) * (t : ℂ) +
      ((b * sigma + tau * sigma ^ 2 : ℝ) : ℂ)) := by
  congr 1
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- Every full vertical Gaussian Mellin atom is genuinely integrable at positive heat time. -/
theorem integrable_gaussianMellin_vertical (b sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun t : ℝ ↦ Complex.exp ((b : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
      (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2)) := by
  simp_rw [gaussianMellin_vertical_eq_quadratic]
  exact integrable_cexp_quadratic' (by simpa using neg_neg_of_pos htau) _ _

/-- The exact norm separates the abscissa factor from the Gaussian ordinate decay. -/
theorem norm_gaussianMellin_vertical (b tau sigma t : ℝ) :
    ‖Complex.exp ((b : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
      (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2)‖ =
      Real.exp (b * sigma + tau * sigma ^ 2) * Real.exp (-tau * t ^ 2) := by
  rw [gaussianMellin_vertical_eq_quadratic, Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [pow_two]
  ring

/-- The full complex vertical integral is the real Gaussian in the Mellin displacement, independently of abscissa. -/
theorem integral_gaussianMellin_vertical (b sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    (∫ t : ℝ, Complex.exp ((b : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) +
      (tau : ℂ) * ((sigma : ℂ) + (t : ℂ) * I) ^ 2)) =
      ((Real.sqrt (Real.pi / tau) * Real.exp (-b ^ 2 / (4 * tau)) : ℝ) : ℂ) := by
  simp_rw [gaussianMellin_vertical_eq_quadratic]
  rw [integral_cexp_quadratic (by simpa using neg_neg_of_pos htau)]
  have hphase : ((b * sigma + tau * sigma ^ 2 : ℝ) : ℂ) -
      ((((b + 2 * tau * sigma : ℝ) : ℂ) * I) ^ 2) / (4 * -(tau : ℂ)) =
        ((-b ^ 2 / (4 * tau) : ℝ) : ℂ) := by
    have ht : (tau : ℂ) ≠ 0 := by exact_mod_cast htau.ne'
    push_cast
    field_simp
    apply Complex.ext <;> simp [pow_two]; ring
  have hsqrt : ((Real.pi : ℂ) / -(-(tau : ℂ))) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / tau) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow]
    simpa using (Complex.ofReal_cpow (div_nonneg Real.pi_pos.le htau.le) (1 / 2 : ℝ)).symm
  rw [hphase, hsqrt, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

end

end RiemannGaussian
