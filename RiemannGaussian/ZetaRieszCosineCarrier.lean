/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnfilteredSource

/-!
# The exact signed cosine form of the arithmetic carrier

The constant filter is precisely the original factorial log moment.
The full real residual is the actual signed Riesz coefficient times a
nonnegative exponential-factorial envelope times cos(gamma*log(n)).
This exact identity retains the physical floor, integer support and
product phase. It does not supply the independent arithmetic lower bound.
-/

namespace RiemannGaussian.ZetaRieszCosineCarrier
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszUnfilteredSource

/-- Constant filter one is exactly one original factorial moment. -/
theorem factorialPolynomial_one (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial 1 N t = t ^ N / (N.factorial : ℂ) := by
  simpa using zetaFactorialPolynomial_monomial 0 1 N t

/-- The unfiltered real kernel consists of one elementary cosine and
its original exponential-factorial amplitude. -/
theorem re_filterKernel_one (N : ℕ) (y x : ℝ) :
    (zetaPrimeFilterKernel 1 N (3 / 2 + Complex.I * y) x).re =
      Real.exp (-(3 / 2 : ℝ) * Real.log x) * (Real.log x) ^ N / N.factorial *
        Real.cos (y * Real.log x) := by
  rw [zetaPrimeFilterKernel, factorialPolynomial_one]
  have hreal : ((Real.log x : ℂ) ^ N / (N.factorial : ℂ)) =
      (((Real.log x) ^ N / (N.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hreal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re]
  have hre : (-(3 / 2 + Complex.I * (y : ℂ)) * (Real.log x : ℂ)).re =
      -(3 / 2 : ℝ) * Real.log x := by norm_num
  have him : (-(3 / 2 + Complex.I * (y : ℂ)) * (Real.log x : ℂ)).im =
      -(y * Real.log x) := by norm_num
  rw [hre, him, Real.cos_neg]
  ring

/-- The actual Riesz coefficient is real; its arithmetic sign is retained. -/
theorem coefficient_im_eq_zero (L : ℝ) (n : ℕ) :
    (SquarefreeVaughanLogSource.coefficient L n).im = 0 := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs <;> simp only [Complex.ofReal_im, Complex.zero_im]

/-- Each actual unfiltered atom retains exactly its arithmetic sign and
the cosine of its full multiplicative phase. -/
theorem re_coefficient_filter_one (L y : ℝ) (N n : ℕ) :
    (SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel 1 N (3 / 2 + Complex.I * y) n).re =
      (SquarefreeVaughanLogSource.coefficient L n).re *
        (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
          Real.cos (y * Real.log n) := by
  rw [Complex.mul_re, coefficient_im_eq_zero, zero_mul, sub_zero, re_filterKernel_one]
  ring

/-- The original factorial envelope is nonnegative on every natural label. -/
theorem factorial_envelope_nonneg (N n : ℕ) :
    0 ≤ Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial := by
  have hlog := Real.log_natCast_nonneg n
  positivity

/-- The complete remaining real response is exactly one signed
cosine-weighted arithmetic sum with nonnegative factorial envelope.
The physical floor and every previously proved support deletion remain. -/
theorem re_unfiltered_residual_eq_cosine_sum (rho : NontrivialZetaZero) (N : ℕ) :
    (normalizedUnfilteredResidual rho N).re =
      (3 / 2 - rho.1.re) ^ (N + 1) *
        ∑ n ∈ ZetaRieszSemiprimeDeletion.residualBand (3 / 2 - rho.1.re) N,
          (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n).re *
            (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
              Real.cos (rho.1.im * Real.log n) := by
  simp only [normalizedUnfilteredResidual, ZetaRieszSemiprimeDeletion.residualResponse,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp only [Complex.re_sum, re_coefficient_filter_one]

end
end RiemannGaussian.ZetaRieszCosineCarrier
