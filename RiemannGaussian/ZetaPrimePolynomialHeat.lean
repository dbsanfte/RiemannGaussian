/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianPolynomialTransport
import RiemannGaussian.ZetaPrimeFermiHeatTransport

/-!
# Polynomial clearing factors inside the full prime heat average

Every complex polynomial multiplier is retained inside the vertical Gaussian
average of the original prime moment. The exact finite Hermite transform
gives its arithmetic multiplier. All term norms, the infinite interchange
and the integrability of the whole average are proved on the Euler
half-plane, for every original moment filter, cutoff and prime sieve.

This identity does not commute clearing with differentiation, and it does
not assert that a fixed polynomial clears the higher-order poles of every
moment. Those operations must keep their full Leibniz terms. No arithmetic
positivity or source limit is inferred from the positive Gaussian alone.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter MeasureTheory Topology
open scoped Classical
open GaussianPolynomialTransport GaussianFermiZeroPair

/-- The full polynomial weight on the original vertical Euler line. -/
def primePolynomialHeatWeight (B : ℝ) (q : Polynomial ℂ) (s : ℂ) (y : ℝ) : ℂ :=
  q.eval (s - I * (y : ℂ)) * (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ)

/-- The actual arithmetic response after transporting the polynomial
through the Gaussian. The original factorial filter and prime support stay
inside the same complete complex summand. -/
def polynomialHeatPrimeResponse (B : ℝ) (q p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
    (window B (Real.log n) : ℂ) * transport B q (s + 2 * (B : ℂ) * (Real.log n : ℂ))

/-- The polynomial and the full prime phase combine into the exact
Gaussian atom before any integral or arithmetic sum is estimated. -/
theorem polynomialHeatTerm_eq (B : ℝ) (q p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (N : ℕ) (s : ℂ) (n : ℕ) (y : ℝ) :
    primePolynomialHeatWeight B q s y *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n) =
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n) *
        (q.eval (s - I * y) * GaussianPolynomialTransport.atom B (Real.log n) y) := by
  rw [primePolynomialHeatWeight, primeFilterKernel_imaginary_shift, atom_eq_gaussian_phase]
  ring

/-- Every original prime term is integrable with its full polynomial
weight, without assuming a bound for the remaining prime sum. -/
theorem integrable_polynomialHeatTerm {B : ℝ} (hB : 0 < B) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    Integrable (fun y : ℝ => primePolynomialHeatWeight B q s y *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)) := by
  simp_rw [polynomialHeatTerm_eq]
  exact (integrable_weighted hB (Real.log n) s q).const_mul _

/-- The integral norm retains the exact polynomial Gaussian mass and
the norm of the original complex arithmetic term. -/
theorem integral_norm_polynomialHeatTerm (B : ℝ) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    (∫ y : ℝ, ‖primePolynomialHeatWeight B q s y *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)‖) =
      (∫ y : ℝ, ‖primePolynomialHeatWeight B q s y‖) *
        ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖ := by
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  simp only [norm_mul, norm_primeFilterKernel_imaginary_shift]

/-- The entire family of polynomial-weighted integral norms is summable
on the Euler half-plane, for every original finite prime sieve. -/
theorem summable_integral_norm_polynomialHeatTerm (B : ℝ) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y : ℝ, ‖primePolynomialHeatWeight B q s y *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)‖) := by
  simp_rw [integral_norm_polynomialHeatTerm]
  exact (summable_primeLogResponse p D S hS N hs).norm.mul_left _

/-- Each complete arithmetic term has the explicit finite Hermite
multiplier, with its complex displacement and exact Gaussian mass. -/
theorem integral_polynomialHeatTerm {B : ℝ} (hB : 0 < B) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (n : ℕ) :
    (∫ y : ℝ, primePolynomialHeatWeight B q s y *
      (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N (s - I * y) n)) =
      (mass B : ℂ) * (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (window B (Real.log n) : ℂ) * transport B q (s + 2 * (B : ℂ) * (Real.log n : ℂ))) := by
  simp_rw [polynomialHeatTerm_eq]
  rw [integral_const_mul]
  change _ * weighted B (Real.log n) s q = _
  rw [weighted_eq_transport hB]
  unfold window
  ring

/-- The full original prime response has an ordinate-independent norm
majorant on its fixed Euler line, retaining its polynomial and prime support. -/
theorem norm_primeLogResponse_imaginary_shift_le (p : Polynomial ℂ) (D : ℕ)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    ‖primeLogResponse p D S N (s - I * y)‖ ≤
      ∑' n : ℕ, ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖ := by
  have hi := summable_primeLogResponse p D S hS N
    (s := s - I * y) (by simpa using hs)
  have h := norm_tsum_le_tsum_norm hi.norm
  simpa only [primeLogResponse, norm_mul, norm_primeFilterKernel_imaginary_shift] using h

/-- The full polynomial-weighted prime average is genuinely integrable.
The complete Euler majorant pays its norm before the infinite interchange. -/
theorem integrable_polynomialHeatPrimeResponse {B : ℝ} (hB : 0 < B) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun y : ℝ => primePolynomialHeatWeight B q s y *
      primeLogResponse p D S N (s - I * y)) := by
  have hw : Continuous (primePolynomialHeatWeight B q s) := by
    have hq : Continuous (fun y : ℝ => q.eval (s - I * (y : ℂ))) :=
      q.continuous.comp (by fun_prop)
    unfold primePolynomialHeatWeight
    fun_prop
  have hm : Measurable (fun y : ℝ => primeLogResponse p D S N (s - I * y)) := by
    unfold primeLogResponse
    apply Measurable.tsum
    intro n
    simp_rw [primeFilterKernel_imaginary_shift]
    fun_prop
  have hm' : AEStronglyMeasurable (fun y : ℝ => primePolynomialHeatWeight B q s y *
      primeLogResponse p D S N (s - I * y)) :=
    (hw.measurable.mul hm).aestronglyMeasurable
  apply ((integrable_vertical_polynomial_gaussian hB s q).norm.mul_const
    (∑' n : ℕ, ‖primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n‖)).mono'
    hm'
  filter_upwards with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_primeLogResponse_imaginary_shift_le p D S hS N hs y)
    (norm_nonneg _)

/-- Every complex polynomial can be kept inside the actual full prime
heat average. The result is its explicit Hermite multiplier, including all
original factorial orders, ordinary-prime exclusions and complex phases. -/
theorem integral_polynomialHeatPrimeResponse {B : ℝ} (hB : 0 < B) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ, primePolynomialHeatWeight B q s y * primeLogResponse p D S N (s - I * y)) =
      (mass B : ℂ) * polynomialHeatPrimeResponse B q p D S N s := by
  have h := (hasSum_integral_of_summable_integral_norm
    (integrable_polynomialHeatTerm hB q p D S N s)
    (summable_integral_norm_polynomialHeatTerm B q p D S hS N hs)).tsum_eq
  simp_rw [integral_polynomialHeatTerm hB] at h
  simpa only [polynomialHeatPrimeResponse, primeLogResponse, tsum_mul_left] using h.symm

/-- The explicit corrected arithmetic series itself converges absolutely;
its sum is not introduced merely as a totalized expression. -/
theorem summable_polynomialHeatPrimeResponse {B : ℝ} (hB : 0 < B) (q p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
      (window B (Real.log n) : ℂ) * transport B q (s + 2 * (B : ℂ) * (Real.log n : ℂ))) := by
  have h := (hasSum_integral_of_summable_integral_norm
    (integrable_polynomialHeatTerm hB q p D S N s)
    (summable_integral_norm_polynomialHeatTerm B q p D S hS N hs)).summable
  simp_rw [integral_polynomialHeatTerm hB] at h
  have hm : (mass B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mass_pos hB).ne'
  convert! h.mul_left (mass B : ℂ)⁻¹ using 1
  ext n
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- A squared clearing factor has an exact three-term arithmetic
transport for every remaining polynomial. Both derivative cross terms
stay inside each original prime summand. -/
theorem polynomialHeatPrimeResponse_double_factor {B : ℝ} (hB : 0 < B)
    (q p : Polynomial ℂ) (r : ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) :
    polynomialHeatPrimeResponse B ((Polynomial.X - Polynomial.C r) ^ 2 * q) p D S N s =
      ∑' n : ℕ, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (window B (Real.log n) : ℂ) *
          (let z := s + 2 * (B : ℂ) * (Real.log n : ℂ);
          ((z - r) ^ 2 - 2 * (B : ℂ)) * transport B q z -
            4 * (B : ℂ) * (z - r) * transport B q.derivative z +
            4 * (B : ℂ) ^ 2 * transport B q.derivative.derivative z) := by
  unfold polynomialHeatPrimeResponse
  simp_rw [transport_double_factor hB]

/-- The literal squared pole factor is transported through the complete
convergent ordinary-prime moment, retaining its subtractive variance term.
For higher moments this is an identity, not a claim that the factor alone
clears their higher-order poles. -/
theorem integral_squaredFactor_primeHeat {B : ℝ} (hB : 0 < B) (p : Polynomial ℂ) (r : ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ, (s - I * (y : ℂ) - r) ^ 2 * (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      primeLogResponse p D S N (s - I * y)) =
      (mass B : ℂ) * ∑' n : ℕ, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n *
        (window B (Real.log n) : ℂ) *
          ((s + 2 * (B : ℂ) * (Real.log n : ℂ) - r) ^ 2 - 2 * (B : ℂ)) := by
  have h := integral_polynomialHeatPrimeResponse hB ((Polynomial.X - Polynomial.C r) ^ 2)
    p D S hS N hs
  simpa only [primePolynomialHeatWeight, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, polynomialHeatPrimeResponse, transport_linear_square hB]
    using h

end
end RiemannGaussian.SquarefreeEulerQuadratic
