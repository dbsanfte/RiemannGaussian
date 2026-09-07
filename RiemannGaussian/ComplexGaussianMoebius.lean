import RiemannGaussian.GaussianMoebiusMellin

/-!
# The actual Gaussian Möbius family with complex Mellin weights

Each summand keeps the actual Möbius coefficient and full complex power.
Its exact norm is a translated real Gaussian, so absolute convergence
holds for every complex weight and every positive heat time. No critical
strip or zeta-zero premise is needed for this summability statement.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual Möbius coefficient with its full Mellin phase and logarithmic Gaussian weight. -/
def complexGaussianMoebiusSummand (s : ℂ) (a tau : ℝ) (n : ℕ) : ℂ :=
  ((μ n : ℤ) : ℂ) * Complex.exp
    (-s * (Real.log n : ℂ) - (((a - Real.log n) ^ 2 / (4 * tau) : ℝ) : ℂ))

/-- The exponential presentation agrees with the original complex Dirichlet weight, including the vanishing zero index. -/
theorem complexGaussianMoebiusSummand_eq_cpow (s : ℂ) (a tau : ℝ) (n : ℕ) :
    complexGaussianMoebiusSummand s a tau n = ((μ n : ℤ) : ℂ) * (n : ℂ) ^ (-s) *
      (Real.exp (-(a - Real.log n) ^ 2 / (4 * tau)) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [complexGaussianMoebiusSummand]
  rw [complexGaussianMoebiusSummand, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
    ← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_exp,
    mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The exact norm keeps the real Mellin scaling and translates the Gaussian center without losing its heat time. -/
theorem norm_complexGaussianMoebiusSummand (s : ℂ) (a : ℝ) {tau : ℝ} (htau : 0 < tau) (n : ℕ) :
    ‖complexGaussianMoebiusSummand s a tau n‖ =
      Real.exp (-s.re * a + tau * s.re ^ 2) *
        |gaussianMoebiusSummand (a - 2 * tau * s.re) tau n| := by
  have hre : (-s * (Real.log n : ℂ) - (((a - Real.log n) ^ 2 / (4 * tau) : ℝ) : ℂ)).re =
      -s.re * Real.log n - (a - Real.log n) ^ 2 / (4 * tau) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have he : -s.re * Real.log n - (a - Real.log n) ^ 2 / (4 * tau) =
      (-s.re * a + tau * s.re ^ 2) + (-(a - 2 * tau * s.re - Real.log n) ^ 2 / (4 * tau)) := by
    field_simp
    ring
  rw [complexGaussianMoebiusSummand, norm_mul, Complex.norm_exp, hre, he, Real.exp_add]
  unfold gaussianMoebiusSummand
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- The actual complex-weighted Gaussian Möbius series converges absolutely at every positive heat time. -/
theorem summable_complexGaussianMoebiusSummand (s : ℂ) (a : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Summable (complexGaussianMoebiusSummand s a tau) := by
  apply Summable.of_norm
  exact ((summable_gaussianMoebiusSummand (a - 2 * tau * s.re) htau).abs.mul_left
    (Real.exp (-s.re * a + tau * s.re ^ 2))).congr fun n ↦ (norm_complexGaussianMoebiusSummand s a htau n).symm

/-- The full Gaussian Möbius sum retains a complex Mellin weight at every heat time. -/
def complexGaussianMoebiusSum (s : ℂ) (a tau : ℝ) : ℂ := ∑' n : ℕ, complexGaussianMoebiusSummand s a tau n

/-- The zero Mellin weight recovers exactly the existing actual real Gaussian Möbius sum. -/
theorem complexGaussianMoebiusSum_zero (a tau : ℝ) :
    complexGaussianMoebiusSum 0 a tau = (gaussianMoebiusSum a tau : ℂ) := by
  unfold complexGaussianMoebiusSum gaussianMoebiusSum
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  unfold complexGaussianMoebiusSummand gaussianMoebiusSummand
  simp only [neg_zero, zero_mul, zero_sub, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 2
  ring

/-- The complex heat kernel transports the normalized signed arithmetic source without discarding its phase. -/
def complexGaussianMoebiusHeatKernel (s : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((1 - 2 * s) * (v : ℂ) - (v : ℂ) ^ 2 / 4)

/-- Every fixed complex phase has a genuinely integrable heat kernel. -/
theorem integrable_complexGaussianMoebiusHeatKernel (s : ℂ) :
    Integrable (complexGaussianMoebiusHeatKernel s) := by
  convert integrable_cexp_quadratic' (b := (-(1 / 4) : ℂ)) (by norm_num) (1 - 2 * s) 0 using 1
  funext v
  unfold complexGaussianMoebiusHeatKernel
  congr 1
  ring

end

end RiemannGaussian
