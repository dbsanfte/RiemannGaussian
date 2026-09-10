/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeKernelSecondDifference
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exact Laplace tests of the factorial polynomial kernel

The whole complex polynomial has an exact convergent Laplace moment.
This identity supplies a signed test of its size without replacing its
coefficients by separate absolute values or requiring a Stirling estimate.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every factorial monomial has a genuinely integrable damped response. -/
theorem integrableOn_factorial_monomial_exp (n : ℕ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ ↦ ((t : ℂ) ^ n / (n.factorial : ℂ)) *
      Complex.exp (-(d : ℂ) * t)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) hd
  simp only [Real.rpow_natCast, Real.rpow_one] at h
  have hc := (Complex.ofRealCLM.integrable_comp h).div_const (n.factorial : ℂ)
  apply hc.congr
  filter_upwards [] with t
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_exp, Complex.ofReal_neg]
  ring

/-- The exact factorial Laplace moment, with its damping denominator
and convergence domain retained. -/
theorem integral_factorial_monomial_exp (n : ℕ) {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ in Set.Ioi 0, ((t : ℂ) ^ n / (n.factorial : ℂ)) *
      Complex.exp (-(d : ℂ) * t)) = (d : ℂ)⁻¹ ^ (n + 1) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := (n : ℂ) + 1) (by simpa using (show (0 : ℝ) < (n : ℝ) + 1 by positivity)) hd
  simp only [add_sub_cancel_right, Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial, one_div] at h
  rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by simp, Complex.cpow_natCast] at h
  have he (t : ℝ) : ((t : ℂ) ^ n / (n.factorial : ℂ)) * Complex.exp (-(d : ℂ) * t) =
      ((t : ℂ) ^ n * Complex.exp (-((d : ℂ) * t))) / (n.factorial : ℂ) := by
    rw [neg_mul]
    ring
  simp_rw [he]
  rw [integral_div, h]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [mul_div_cancel_right₀ _ hn]

/-- The complete complex polynomial response is integrable for every
positive damping and every moment order. -/
theorem integrableOn_zetaFactorialPolynomial_exp (p : Polynomial ℂ) (N : ℕ)
    {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ ↦ zetaFactorialPolynomial p N t * Complex.exp (-(d : ℂ) * t))
      (Set.Ioi 0) := by
  have he : (fun t : ℝ ↦ zetaFactorialPolynomial p N t * Complex.exp (-(d : ℂ) * t)) =
      (fun t : ℝ ↦ ∑ k ∈ p.support, p.coeff k *
        (((t : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)) * Complex.exp (-(d : ℂ) * t))) := by
    funext t
    simp only [zetaFactorialPolynomial, Polynomial.sum, Finset.sum_mul, mul_assoc]
  rw [he]
  exact integrable_finsetSum _ (fun k _ ↦ (integrableOn_factorial_monomial_exp (N + k) hd).const_mul _)

/-- Laplace integration recovers the exact polynomial evaluation. All
coefficients remain coupled in this identity. -/
theorem integral_zetaFactorialPolynomial_exp (p : Polynomial ℂ) (N : ℕ)
    {d : ℝ} (hd : 0 < d) :
    (∫ t : ℝ in Set.Ioi 0, zetaFactorialPolynomial p N t * Complex.exp (-(d : ℂ) * t)) =
      (d : ℂ)⁻¹ ^ (N + 1) * p.eval (d : ℂ)⁻¹ := by
  simp only [zetaFactorialPolynomial, Polynomial.sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun k _ ↦ (integrableOn_factorial_monomial_exp (N + k) hd).const_mul _)]
  simp_rw [integral_const_mul, integral_factorial_monomial_exp _ hd]
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, Finset.mul_sum, pow_add, pow_one]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end RiemannGaussian
