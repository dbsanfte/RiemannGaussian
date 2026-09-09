/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentBand
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact differential structure of the signed prime filter

The factorial log polynomial has an exact lowering derivative. Its full
complex prime kernel therefore obeys a first-order differential identity,
including both the real damping and the imaginary phase rotation. These
identities prepare the actual finite prime band for signed Abel summation.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The factorial polynomial acting on the logarithmic prime coordinate. -/
def zetaFactorialPolynomial (p : Polynomial ℂ) (N : ℕ) (t : ℂ) : ℂ :=
  p.sum (fun k c ↦ c * (t ^ (N + k) / ((N + k).factorial : ℂ)))

/-- The multiplicative real-variable kernel of the complete complex filter. -/
def zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  zetaFactorialPolynomial p N (Real.log x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))

/-- The real-variable kernel agrees with the exact log-weight carrier at
every natural arithmetic index, including its complete complex phase. -/
theorem zetaPrimeFilterKernel_nat (p : Polynomial ℂ) (N m : ℕ) (s : ℂ) :
    zetaPrimeFilterKernel p N s m = zetaPrimeFeature s m *
      ∑ k ∈ p.support, p.coeff k * ((Real.log m : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)) := by
  simp only [zetaPrimeFilterKernel, zetaFactorialPolynomial, Polynomial.sum, zetaPrimeFeature, neg_mul]
  ring

private theorem hasDerivAt_factorialLog_succ (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (Real.log t : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ))
      (((Real.log x : ℂ) ^ n / (n.factorial : ℂ)) / (x : ℂ)) x := by
  have h := (((Real.hasDerivAt_log hx.ne').ofReal_comp).pow (n + 1)).div_const
    ((n + 1).factorial : ℂ)
  apply h.congr_deriv
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Complex.ofReal_inv]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

/-- Differentiation lowers the moment order exactly; all polynomial
coefficients remain unchanged and coupled. -/
theorem hasDerivAt_zetaFactorialPolynomial_log (p : Polynomial ℂ) (N : ℕ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ zetaFactorialPolynomial p (N + 1) (Real.log t : ℂ))
      (zetaFactorialPolynomial p N (Real.log x : ℂ) / (x : ℂ)) x := by
  have h := HasDerivAt.fun_sum (u := p.support) (fun k _ ↦
    (hasDerivAt_factorialLog_succ (N + k) hx).const_mul (p.coeff k))
  simpa only [zetaFactorialPolynomial, Polynomial.sum, Finset.sum_div,
    mul_div_assoc, show ∀ k, N + 1 + k = N + k + 1 by omega] using h

/-- The complete prime kernel is twice continuously differentiable on
the positive real axis, including moment order zero. -/
theorem contDiffAt_zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 2 (zetaPrimeFilterKernel p N s) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have hlog : ContDiffAt ℝ 2 (fun t : ℝ ↦ (Real.log t : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx0)
  unfold zetaPrimeFilterKernel zetaFactorialPolynomial Polynomial.sum
  fun_prop

/-- The exact signed differential recurrence retains the imaginary
rotation term through the full complex parameter `s`. -/
theorem hasDerivAt_zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaPrimeFilterKernel p (N + 1) s)
      ((zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ)) x := by
  have hlog := (Real.hasDerivAt_log hx.ne').ofReal_comp
  have he := (hlog.const_mul (-s)).cexp
  have h := (hasDerivAt_zetaFactorialPolynomial_log p N hx).mul he
  apply h.congr_deriv
  simp only [zetaPrimeFilterKernel, Complex.ofReal_inv]
  ring

/-- The ordinary derivative is the same exact lowering expression. -/
theorem deriv_zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    deriv (zetaPrimeFilterKernel p (N + 1) s) x =
      (zetaPrimeFilterKernel p N s x - s * zetaPrimeFilterKernel p (N + 1) s x) / (x : ℂ) :=
  (hasDerivAt_zetaPrimeFilterKernel p N s hx).deriv

/-- The real channel receives a signed contribution from the imaginary
channel. Dropping it would discard the phase rotation used by Abel summation. -/
theorem deriv_zetaPrimeFilterKernel_re (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    (deriv (zetaPrimeFilterKernel p (N + 1) s) x).re =
      ((zetaPrimeFilterKernel p N s x).re - s.re * (zetaPrimeFilterKernel p (N + 1) s x).re +
        s.im * (zetaPrimeFilterKernel p (N + 1) s x).im) / x := by
  rw [deriv_zetaPrimeFilterKernel p N s hx, Complex.div_ofReal_re, Complex.sub_re, Complex.mul_re]
  ring

/-- The imaginary channel supplies the complementary signed rotation,
so the two derivative identities recover the full complex recurrence. -/
theorem deriv_zetaPrimeFilterKernel_im (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    (deriv (zetaPrimeFilterKernel p (N + 1) s) x).im =
      ((zetaPrimeFilterKernel p N s x).im - s.re * (zetaPrimeFilterKernel p (N + 1) s x).im -
        s.im * (zetaPrimeFilterKernel p (N + 1) s x).re) / x := by
  rw [deriv_zetaPrimeFilterKernel p N s hx, Complex.div_ofReal_im, Complex.sub_im, Complex.mul_im]
  ring

/-- The continuous density primitive exposes the pole-cancelling
operator exactly, rather than estimating its two terms separately. -/
theorem hasDerivAt_mul_zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) * zetaPrimeFilterKernel p (N + 1) s t)
      (zetaPrimeFilterKernel p N s x - (s - 1) * zetaPrimeFilterKernel p (N + 1) s x) x := by
  have h := (hasDerivAt_id x).ofReal_comp.mul (hasDerivAt_zetaPrimeFilterKernel p N s hx)
  apply h.congr_deriv
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.ofReal_one, one_mul, id_eq]
  field_simp
  ring

/-- Kernel derivatives are genuinely integrable on every positive compact
interval, as required for finite Abel summation. -/
theorem integrableOn_deriv_zetaPrimeFilterKernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (deriv (zetaPrimeFilterKernel p N s)) (Set.Icc a b) := by
  have h : ContDiffOn ℝ 2 (zetaPrimeFilterKernel p N s) (Set.Ioi 0) :=
    fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p N s hx).contDiffWithinAt
  exact ((h.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
    (fun _ hx ↦ ha.trans_le hx.1)).integrableOn_Icc

/-- Additivity of the factorial polynomial keeps the coefficient algebra
separate from assertions about the sign of its values. -/
theorem zetaFactorialPolynomial_add (p q : Polynomial ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (p + q) N t = zetaFactorialPolynomial p N t + zetaFactorialPolynomial q N t :=
  Polynomial.sum_add_index _ _ _ (by intro k; simp) (by intro k a b; ring)

/-- A monomial gives one exact factorial moment. -/
theorem zetaFactorialPolynomial_monomial (k : ℕ) (c : ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (Polynomial.monomial k c) N t = c * (t ^ (N + k) / ((N + k).factorial : ℂ)) :=
  Polynomial.sum_monomial_index _ _ (by simp)

/-- Multiplication by the spectral variable is exactly a shift of the
factorial moment order, before any scalar estimate is taken. -/
theorem zetaFactorialPolynomial_X_mul (p : Polynomial ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (Polynomial.X * p) N t = zetaFactorialPolynomial p (N + 1) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, zetaFactorialPolynomial_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.X_mul_monomial, zetaFactorialPolynomial_monomial, zetaFactorialPolynomial_monomial]
    rw [show N + (k + 1) = N + 1 + k by omega]

/-- Scalar coefficients commute with the factorial polynomial. -/
theorem zetaFactorialPolynomial_C_mul (p : Polynomial ℂ) (c : ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (Polynomial.C c * p) N t = c * zetaFactorialPolynomial p N t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, zetaFactorialPolynomial_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.C_mul_monomial, zetaFactorialPolynomial_monomial, zetaFactorialPolynomial_monomial]
    ring

/-- Subtraction in the spectral polynomial remains an exact signed
subtraction of the factorial kernels. -/
theorem zetaFactorialPolynomial_sub (p q : Polynomial ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (p - q) N t = zetaFactorialPolynomial p N t - zetaFactorialPolynomial q N t := by
  have h := zetaFactorialPolynomial_add (p - q) q N t
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- A nonnegative squared polynomial can produce a strictly negative
factorial kernel. Pairing coefficients with their conjugates therefore
does not justify a positivity claim for the arithmetic moment filter. -/
theorem zetaFactorialPolynomial_square_exact (N : ℕ) :
    zetaFactorialPolynomial ((1 - Polynomial.X : Polynomial ℂ) ^ 2) N ((N + 1 : ℕ) : ℂ) =
      -(((N + 1 : ℕ) : ℂ) ^ N / (N.factorial : ℂ)) / ((N + 2 : ℕ) : ℂ) := by
  have he : (1 - Polynomial.X : Polynomial ℂ) ^ 2 =
      Polynomial.monomial 0 1 + Polynomial.monomial 1 (-2) + Polynomial.monomial 2 1 := by
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_neg, map_ofNat, map_one]
    norm_num
    ring
  rw [he, zetaFactorialPolynomial_add, zetaFactorialPolynomial_add]
  simp only [zetaFactorialPolynomial_monomial, Nat.add_zero, one_mul]
  have hn1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hn2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  have hn2' : (N : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast (show N + 1 + 1 ≠ 0 by omega)
  rw [show N + 2 = (N + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_succ]
  field_simp
  ring

/-- The squared polynomial `(1-X)^2` has a strictly negative real
factorial transform at `N+1` for every order, not just in a numerical test. -/
theorem zetaFactorialPolynomial_square_re_neg (N : ℕ) :
    (zetaFactorialPolynomial ((1 - Polynomial.X : Polynomial ℂ) ^ 2) N ((N + 1 : ℕ) : ℂ)).re < 0 := by
  rw [zetaFactorialPolynomial_square_exact]
  have he : -(((N + 1 : ℕ) : ℂ) ^ N / (N.factorial : ℂ)) / ((N + 2 : ℕ) : ℂ) =
      ((-(((N + 1 : ℕ) : ℝ) ^ N / (N.factorial : ℝ)) / ((N + 2 : ℕ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.ofReal_re]
  have hp : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ N / (N.factorial : ℝ) := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hp) (by positivity)

end

end RiemannGaussian
