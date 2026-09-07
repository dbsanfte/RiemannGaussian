import RiemannGaussian.ComplexGaussianMoebius

/-!
# Exact complex Gaussian heat atoms for the Möbius coefficients

Each original signed unit-time Gaussian is transported through a complex
heat kernel. Its full integral gives the original complex Dirichlet weight
at heat time two. The series of norm integrals is also proved summable,
so the subsequent infinite arithmetic exchange has no missing premise.
-/

open Complex MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- One normalized signed arithmetic atom retains the full complex phase of the second heat step. -/
def complexGaussianMoebiusHeatTerm (s : ℂ) (a : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  ((gaussianMoebiusSummand (a + v) 1 n / Real.exp (a + v) : ℝ) : ℂ) *
    complexGaussianMoebiusHeatKernel s v

/-- The exact quadratic phase of the original normalized arithmetic heat atom. -/
theorem complexGaussianMoebiusHeatTerm_eq_quadratic (s : ℂ) (a : ℝ) (n : ℕ) (v : ℝ) :
    complexGaussianMoebiusHeatTerm s a n v = ((μ n : ℤ) : ℂ) * Complex.exp
      (-(1 / 2 : ℂ) * (v : ℂ) ^ 2 +
        (-(((a - Real.log n : ℝ) : ℂ)) / 2 - 2 * s) * (v : ℂ) +
        (-(((a - Real.log n) ^ 2 : ℝ) : ℂ) / 4 - (a : ℂ))) := by
  unfold complexGaussianMoebiusHeatTerm gaussianMoebiusSummand complexGaussianMoebiusHeatKernel
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp,
    div_eq_mul_inv, ← Complex.exp_neg]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every actual signed complex heat atom is integrable over the whole real line. -/
theorem integrable_complexGaussianMoebiusHeatTerm (s : ℂ) (a : ℝ) (n : ℕ) :
    Integrable (complexGaussianMoebiusHeatTerm s a n) := by
  change Integrable (fun v : ℝ ↦ complexGaussianMoebiusHeatTerm s a n v)
  simp_rw [complexGaussianMoebiusHeatTerm_eq_quadratic]
  exact (integrable_cexp_quadratic' (by norm_num) _ _).const_mul _

/-- The Gaussian half-quadratic integral, with exact normalization, used for the absolute arithmetic exchange. -/
theorem integral_realGaussian_half_quadratic (c d : ℝ) :
    (∫ v : ℝ, Real.exp (-(1 / 2 : ℝ) * v ^ 2 + c * v + d)) =
      Real.sqrt (2 * Real.pi) * Real.exp (d + c ^ 2 / 2) := by
  have he (v : ℝ) : Real.exp (-(1 / 2 : ℝ) * v ^ 2 + c * v + d) =
      Real.exp (-(1 / 2 : ℝ) * (v - c) ^ 2) * Real.exp (d + c ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_mul_const,
    integral_sub_right_eq_self (fun v : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * v ^ 2)) c,
    integral_gaussian]
  congr 2
  ring

/-- Integrating one signed heat atom gives its actual complex Mellin weight at heat time two, retaining every phase. -/
theorem integral_complexGaussianMoebiusHeatTerm (s : ℂ) (a : ℝ) (n : ℕ) :
    (∫ v : ℝ, complexGaussianMoebiusHeatTerm s a n v) =
      ((Real.sqrt (2 * Real.pi) : ℂ) * Complex.exp ((s - 1) * (a : ℂ) + 2 * s ^ 2)) *
        complexGaussianMoebiusSummand s a 2 n := by
  simp_rw [complexGaussianMoebiusHeatTerm_eq_quadratic]
  rw [integral_const_mul, integral_cexp_quadratic (by norm_num)]
  have hsqrt : ((Real.pi : ℂ) / -(-(1 / 2 : ℂ))) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
    have h : (Real.sqrt (2 * Real.pi) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using Complex.ofReal_cpow (show 0 ≤ 2 * Real.pi by positivity) (1 / 2 : ℝ)
    rw [h]
    congr 1
    push_cast
    ring
  rw [hsqrt, complexGaussianMoebiusSummand]
  have he : -(((a - Real.log n) ^ 2 : ℝ) : ℂ) / 4 - (a : ℂ) -
      (-(((a - Real.log n : ℝ) : ℂ)) / 2 - 2 * s) ^ 2 / (4 * (-(1 / 2 : ℂ))) =
      ((s - 1) * (a : ℂ) + 2 * s ^ 2) +
        (-s * (Real.log n : ℂ) - (((a - Real.log n) ^ 2 / (4 * (2 : ℝ)) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- The exact norm integral retains the actual weighted coefficient and the full real normalization. -/
theorem integral_norm_complexGaussianMoebiusHeatTerm (s : ℂ) (a : ℝ) (n : ℕ) :
    (∫ v : ℝ, ‖complexGaussianMoebiusHeatTerm s a n v‖) =
      (Real.sqrt (2 * Real.pi) * Real.exp ((s.re - 1) * a + 2 * s.re ^ 2)) *
        ‖complexGaussianMoebiusSummand s a 2 n‖ := by
  have hre (v : ℝ) : (-(1 / 2 : ℂ) * (v : ℂ) ^ 2 +
      (-(((a - Real.log n : ℝ) : ℂ)) / 2 - 2 * s) * (v : ℂ) +
      (-(((a - Real.log n) ^ 2 : ℝ) : ℂ) / 4 - (a : ℂ))).re =
        -(1 / 2 : ℝ) * v ^ 2 + (-(a - Real.log n) / 2 - 2 * s.re) * v +
          (-(a - Real.log n) ^ 2 / 4 - a) := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
    norm_num
  simp_rw [complexGaussianMoebiusHeatTerm_eq_quadratic, norm_mul, Complex.norm_exp, hre]
  rw [integral_const_mul, integral_realGaussian_half_quadratic]
  rw [complexGaussianMoebiusSummand, norm_mul, Complex.norm_exp]
  have hw : (-s * (Real.log n : ℂ) - (((a - Real.log n) ^ 2 / (4 * (2 : ℝ)) : ℝ) : ℂ)).re =
      -s.re * Real.log n - (a - Real.log n) ^ 2 / 8 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num
  rw [hw]
  have he : -(a - Real.log n) ^ 2 / 4 - a + (-(a - Real.log n) / 2 - 2 * s.re) ^ 2 / 2 =
      ((s.re - 1) * a + 2 * s.re ^ 2) + (-s.re * Real.log n - (a - Real.log n) ^ 2 / 8) := by ring
  rw [he, Real.exp_add]
  ring

/-- The complete series of norm integrals converges for each original complex weight and center. -/
theorem summable_integral_norm_complexGaussianMoebiusHeatTerm (s : ℂ) (a : ℝ) :
    Summable (fun n : ℕ ↦ ∫ v : ℝ, ‖complexGaussianMoebiusHeatTerm s a n v‖) := by
  simp_rw [integral_norm_complexGaussianMoebiusHeatTerm]
  exact (summable_complexGaussianMoebiusSummand s a (by norm_num : (0 : ℝ) < 2)).norm.mul_left _

end

end RiemannGaussian
