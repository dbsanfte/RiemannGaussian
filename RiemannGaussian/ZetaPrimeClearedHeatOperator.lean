/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FactorialPolynomialTransport
import RiemannGaussian.ZetaPrimeClearedHeatDecay

/-!
# The full polynomial operator in the actual prime heat summand

All downward Leibniz orders combine into one finite operator applied to
the original clearing polynomial. This is an exact identity for the
genuinely summable ordinary-prime series, not a replacement by a model
density. It exposes the factorial displacement and signed quadratic
correction that any independent arithmetic lower bound must control.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open scoped Classical
open GaussianPolynomialTransport GaussianFermiZeroPair FactorialPolynomialTransport

private theorem factorial_binomial {N k : ℕ} (hk : k ≤ N) {x : ℂ} (hx : x ≠ 0) :
    x ^ N / (N.factorial : ℂ) * ((N.choose k : ℂ) * (-x⁻¹) ^ k) =
      ((-1 : ℂ) ^ k / (k.factorial : ℂ)) * (x ^ (N - k) / ((N - k).factorial : ℂ)) := by
  have hN : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hNk : ((N - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (N - k))
  have hp : x ^ N = x ^ (N - k) * x ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  rw [Nat.cast_choose ℂ hk, hp]
  rw [neg_pow, inv_pow]
  field_simp

/-- The entire downward factorial expansion is the exact normalized
polynomial operator, including its full Gaussian correction at every order. -/
theorem factorialHeat_eq_leibniz (B : ℝ) (N : ℕ) {x : ℂ} (hx : x ≠ 0)
    (q : Polynomial ℂ) (z : ℂ) :
    x ^ N / (N.factorial : ℂ) * heat B N x q z =
      ∑ k ∈ Finset.range (N + 1), x ^ (N - k) / ((N - k).factorial : ℂ) *
        transport B (signedDerivativePolynomial q k) z := by
  rw [heat_eq_binomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, factorial_binomial (by simpa using Finset.mem_range.mp hk) hx]
  unfold signedDerivativePolynomial
  rw [transport_C_mul]
  ring

private theorem primeCorrection_log_ne_zero {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) {n : ℕ} (hn : primeCorrectionCoefficient D S n ≠ 0) :
    (Real.log n : ℂ) ≠ 0 := by
  have hp : n.Prime := by
    by_contra h
    simp [primeCorrectionCoefficient_eq_prime_tail hD S hS, h] at hn
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

/-- Every actual prime summand keeps exactly the same coefficient,
Fourier phase and Gaussian weight when all Leibniz terms are combined.
The singular natural indices have zero actual coefficient. -/
theorem clearedHeatPrimeTerm_eq_operator (B : ℝ) (q : Polynomial ℂ) {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) (s : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (N + 1), primeCorrectionCoefficient D S n *
      zetaPrimeFilterKernel 1 (N - k) s n * (window B (Real.log n) : ℂ) *
        transport B (signedDerivativePolynomial q k) (s + 2 * (B : ℂ) * (Real.log n : ℂ))) =
      primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 N s n *
        (window B (Real.log n) : ℂ) *
          heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)) := by
  by_cases hn : primeCorrectionCoefficient D S n = 0
  · simp only [hn, zero_mul, Finset.sum_const_zero]
  have hx := primeCorrection_log_ne_zero hD S hS hn
  simp_rw [primeFilterKernel_one]
  have h := factorialHeat_eq_leibniz B N hx q (s + 2 * (B : ℂ) * (Real.log n : ℂ))
  calc
    _ = (primeCorrectionCoefficient D S n * zetaPrimeFeature s n * (window B (Real.log n) : ℂ)) *
        (∑ k ∈ Finset.range (N + 1), (Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ) *
          transport B (signedDerivativePolynomial q k) (s + 2 * (B : ℂ) * (Real.log n : ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [← h]; ring

/-- The literal combined prime series has a genuine sum equal to the
original complete corrected prime heat. Finite/infinite interchange is
justified by the established summability of every exact Leibniz row. -/
theorem hasSum_clearedHeatPrime_operator {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 N s n *
      (window B (Real.log n) : ℂ) *
        heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)))
      (clearedHeatPrimeResponse B q D S N s) := by
  have h := hasSum_sum (s := Finset.range (N + 1)) (fun k _ ↦
    (summable_polynomialHeatPrimeResponse hB (signedDerivativePolynomial q k) 1 D S hS (N - k) hs).hasSum)
  simp_rw [clearedHeatPrimeTerm_eq_operator B q hD S hS N s] at h
  exact h

/-- The actual complete arithmetic heat is one exact prime series with
the full polynomial operator inside each original oscillatory summand. -/
theorem clearedHeatPrimeResponse_eq_operator {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    clearedHeatPrimeResponse B q D S N s =
      ∑' n : ℕ, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 N s n *
        (window B (Real.log n) : ℂ) *
          heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)) :=
  (hasSum_clearedHeatPrime_operator hB q hD S hS N hs).tsum_eq.symm

/-- An arbitrary cofactor and linear clearing root give an exact
three-channel arithmetic formula, retaining the derivative and adjacent
factorial orders in the same prime sum. -/
theorem clearedHeatPrimeResponse_factor {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) (r : ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    clearedHeatPrimeResponse B ((Polynomial.X - Polynomial.C r) * q) D S (N + 1) s =
      ∑' n : ℕ, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 (N + 1) s n *
        (window B (Real.log n) : ℂ) *
          (let x := (Real.log n : ℂ); let z := s + 2 * (B : ℂ) * x;
            (z - r) * heat B (N + 1) x q z - 2 * (B : ℂ) * heat B (N + 1) x q.derivative z -
              (((N : ℂ) + 1) * x⁻¹) * heat B N x q z) := by
  rw [clearedHeatPrimeResponse_eq_operator hB _ hD S hS _ hs]
  simp_rw [heat_factor_mul_succ hB]

/-- A squared clearing factor in the actual prime series has the full
factorial displacement and the exact subtractive budget `2B+N/log(n)²`. -/
theorem clearedHeatPrimeResponse_factor_sq {B : ℝ} (hB : 0 < B) (r : ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    clearedHeatPrimeResponse B ((Polynomial.X - Polynomial.C r) ^ 2) D S N s =
      ∑' n : ℕ, primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 N s n *
        (window B (Real.log n) : ℂ) *
          ((s + 2 * (B : ℂ) * (Real.log n : ℂ) - r - (N : ℂ) * (Real.log n : ℂ)⁻¹) ^ 2 -
            (2 * (B : ℂ) + (N : ℂ) * ((Real.log n : ℂ)⁻¹) ^ 2)) := by
  rw [clearedHeatPrimeResponse_eq_operator hB _ hD S hS _ hs]
  simp_rw [heat_factor_sq hB]

/-- At the displaced root the squared-factor multiplier is strictly
negative, even though the original real square is nonnegative. This is a
sign test for the multiplier, not a claim about the sign of the prime sum. -/
theorem clearedHeatSquareMultiplier_displaced_root_neg {B : ℝ} (hB : 0 < B)
    (N : ℕ) (x : ℝ) (r : ℂ) :
    (heat B N (x : ℂ) ((Polynomial.X - Polynomial.C r) ^ 2)
      (r + (N : ℂ) * (x : ℂ)⁻¹)).re < 0 := by
  rw [heat_factor_sq hB]
  simp only [add_sub_cancel_left, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub]
  have he : (2 * (B : ℂ) + (N : ℂ) * ((x : ℂ)⁻¹) ^ 2) =
      ((2 * B + (N : ℝ) * x⁻¹ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.neg_re, Complex.ofReal_re]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg x⁻¹)]

/-- The actual source-normalized cleared heat uses precisely this
complete operator on its genuine divisor polynomial. Its previously
proved negative source and residual bounds therefore refer to the same
oscillatory prime expression exposed here. -/
theorem normalizedClearedPrimeHeat_eq_operator {B : ℝ} (hB : 0 < B)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (rho : NontrivialZetaZero) (N : ℕ) :
    normalizedClearedPrimeHeat D S rho N B = (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
      ∑' n : ℕ, primeCorrectionCoefficient D S n *
        zetaPrimeFilterKernel 1 N (zetaWronskianMomentCenter rho) n * (window B (Real.log n) : ℂ) *
          heat B N (Real.log n : ℂ) (normalizedPrimeTailClearingPolynomial D S rho)
            (zetaWronskianMomentCenter rho + 2 * (B : ℂ) * (Real.log n : ℂ)) := by
  unfold normalizedClearedPrimeHeat
  rw [clearedHeatPrimeResponse_eq_operator hB _ hD S hS N (by norm_num [zetaWronskianMomentCenter])]

end
end RiemannGaussian.SquarefreeEulerQuadratic
