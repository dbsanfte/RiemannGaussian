/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimePolynomialHeat
import RiemannGaussian.AnalyticDoublePoleMoments

/-!
# Clearing before differentiating the actual prime heat response

The original ordinary-prime series is an analytic Dirichlet series on the
Euler half-plane. Multiplying it by any polynomial before taking a signed
factorial derivative gives its entire finite Leibniz expansion. Each
polynomial derivative then passes through the vertical Gaussian with its
exact Hermite correction. The resulting identity retains all downward
moment orders, coefficient signs and original prime exclusions.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter MeasureTheory Topology
open scoped Classical
open GaussianPolynomialTransport GaussianFermiZeroPair

/-- The exact signed factorial derivative as a polynomial, rather than
an evaluation at only one sampling point. -/
def signedDerivativePolynomial (q : Polynomial ℂ) (k : ℕ) : Polynomial ℂ :=
  Polynomial.C ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * (Polynomial.derivative^[k]) q

/-- Algebraic iterated derivatives agree with genuine complex derivatives
of polynomial evaluation. -/
theorem iteratedDeriv_polynomial_eval (q : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => q.eval z) = fun z => ((Polynomial.derivative^[k]) q).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext z
    exact Polynomial.deriv _

/-- The finite derivative polynomial retains exactly the signed Taylor
normalization of the original analytic multiplier. -/
theorem signedDerivativePolynomial_eval (q : Polynomial ℂ) (k : ℕ) (s : ℂ) :
    (signedDerivativePolynomial q k).eval s = signedTaylorMoment k (fun z => q.eval z) s := by
  rw [signedTaylorMoment, iteratedDeriv_polynomial_eval]
  simp only [signedDerivativePolynomial, Polynomial.eval_mul, Polynomial.eval_C]

/-- The unfiltered factorial kernel is exactly one normalized logarithmic
moment, including order zero. -/
theorem primeFilterKernel_one (N : ℕ) (s : ℂ) (n : ℕ) :
    zetaPrimeFilterKernel 1 N s n =
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ)) * zetaPrimeFeature s n := by
  have h := zetaFactorialPolynomial_monomial 0 1 N (Real.log n : ℂ)
  simp only [Polynomial.monomial_zero_left, map_one, Nat.add_zero, one_mul] at h
  rw [zetaPrimeFilterKernel, h]
  simp only [zetaPrimeFeature, neg_mul]

/-- The ordinary-prime coefficient is genuinely zero at the singular
natural index zero. -/
theorem primeCorrectionCoefficient_zero (D : ℕ) (S : Finset ℕ) :
    primeCorrectionCoefficient D S 0 = 0 := by simp [primeCorrectionCoefficient]

/-- The actual prime support has Euler absolute convergence beyond one,
for every fixed cutoff and finite prime sieve. -/
theorem primeCorrection_abscissa_le_one (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    LSeries.abscissaOfAbsConv (primeCorrectionCoefficient D S) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  have h := summable_primeLogResponse 1 D S hS 0 (s := (y : ℂ)) (by simpa using hy)
  simp_rw [primeFilterKernel_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at h
  unfold LSeriesSummable
  convert! h using 1
  ext n
  exact LSeries_term_eq_zetaPrimeFeature _ (primeCorrectionCoefficient_zero D S) _ _

/-- Every original unfiltered prime moment is the actual signed complex
derivative of its fixed-support Dirichlet series. -/
theorem primeLogResponse_one_eq_signedTaylorMoment (D : ℕ) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    primeLogResponse 1 D S N s = signedTaylorMoment N (LSeries (primeCorrectionCoefficient D S)) s := by
  have hc : LSeries.abscissaOfAbsConv (primeCorrectionCoefficient D S) < s.re :=
    lt_of_le_of_lt (primeCorrection_abscissa_le_one D S hS) (by exact_mod_cast hs)
  have h := (hasSum_signedTaylorMoment_LSeries _ (primeCorrectionCoefficient_zero D S) hc N).tsum_eq
  simpa only [primeLogResponse, primeFilterKernel_one, mul_assoc, mul_comm, mul_left_comm] using h

/-- The moment of the actual prime series after multiplication by the
entire clearing polynomial. Multiplication occurs before differentiation. -/
def clearedPrimeMoment (q : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment N (fun z => q.eval z * LSeries (primeCorrectionCoefficient D S) z) s

/-- All polynomial Leibniz terms are retained for the original prime
support, with their exact downward factorial moment orders. -/
theorem clearedPrimeMoment_eq_leibniz (q : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    clearedPrimeMoment q D S N s =
      ∑ k ∈ Finset.range (N + 1), (signedDerivativePolynomial q k).eval s *
        primeLogResponse 1 D S (N - k) s := by
  have hc : LSeries.abscissaOfAbsConv (primeCorrectionCoefficient D S) < s.re :=
    lt_of_le_of_lt (primeCorrection_abscissa_le_one D S hS) (by exact_mod_cast hs)
  have hq : AnalyticAt ℂ (fun z => q.eval z) s :=
    q.differentiable.analyticAt s
  rw [clearedPrimeMoment, signedTaylorMoment_mul hq (LSeries_analyticOnNhd _ s hc)]
  simp_rw [signedDerivativePolynomial_eval, primeLogResponse_one_eq_signedTaylorMoment D S hS _ hs]

/-- The exact arithmetic heat of the cleared moment retains the whole
finite Leibniz sum, with a separate Hermite correction for every term. -/
def clearedHeatPrimeResponse (B : ℝ) (q : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    polynomialHeatPrimeResponse B (signedDerivativePolynomial q k) 1 D S (N - k) s

/-- Every cleared higher moment is integrable on its original vertical
Euler line against the Gaussian, with all Leibniz terms present. -/
theorem integrable_clearedPrimeMoment_heat {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y : ℝ => (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      clearedPrimeMoment q D S N (s - I * y)) := by
  have he (y : ℝ) : (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      clearedPrimeMoment q D S N (s - I * y) =
      ∑ k ∈ Finset.range (N + 1), primePolynomialHeatWeight B (signedDerivativePolynomial q k) s y *
        primeLogResponse 1 D S (N - k) (s - I * y) := by
    rw [clearedPrimeMoment_eq_leibniz q D S hS N (by simpa using hs), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold primePolynomialHeatWeight
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun k _ => integrable_polynomialHeatPrimeResponse hB
    (signedDerivativePolynomial q k) 1 D S hS (N - k) hs)

/-- Clearing first, differentiating second, and smoothing last has one
exact full-prime formula. Every polynomial derivative and Hermite correction
is present, with the literal prime support and analytic hypotheses discharged. -/
theorem integral_clearedPrimeMoment_heat {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ, (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      clearedPrimeMoment q D S N (s - I * y)) =
      (mass B : ℂ) * clearedHeatPrimeResponse B q D S N s := by
  have he (y : ℝ) : (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      clearedPrimeMoment q D S N (s - I * y) =
      ∑ k ∈ Finset.range (N + 1), primePolynomialHeatWeight B (signedDerivativePolynomial q k) s y *
        primeLogResponse 1 D S (N - k) (s - I * y) := by
    rw [clearedPrimeMoment_eq_leibniz q D S hS N (by simpa using hs), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold primePolynomialHeatWeight
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => integrable_polynomialHeatPrimeResponse hB
    (signedDerivativePolynomial q k) 1 D S hS (N - k) hs)]
  simp_rw [integral_polynomialHeatPrimeResponse hB _ _ D S hS _ hs]
  rw [← Finset.mul_sum]
  rfl

end
end RiemannGaussian.SquarefreeEulerQuadratic
