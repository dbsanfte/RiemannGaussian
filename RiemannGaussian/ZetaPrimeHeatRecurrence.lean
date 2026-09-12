/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeClearedHeatOperator

/-!
# A closed three-order recurrence for the actual cleared prime heat

The polynomial derivative channel cancels exactly against the Gaussian
displacement when one more factorial order is retained. The resulting
recurrence involves only the same complete prime heat at three adjacent
orders. All three orders have the same Gaussian width, cutoff and sieve.
At a quadratic width its source-normalized upper-order coefficient is
exactly `2c/(N+1)`. No signed prime lower bound is inferred from this identity.
-/

namespace RiemannGaussian.FactorialPolynomialTransport
noncomputable section
open GaussianPolynomialTransport

/-- The adjacent factorial step retains its complete derivative channel
after Gaussian transport. -/
theorem heat_succ (B : ℝ) (N : ℕ) (x : ℂ) (q : Polynomial ℂ) (z : ℂ) :
    heat B (N + 1) x q z = heat B N x q z - x⁻¹ * heat B N x q.derivative z := by
  rw [heat, shift_succ, transport_sub, transport_C_mul, derivative_shift]
  rfl

/-- At the actual displaced argument, the derivative channel cancels
against the displacement into the next order. The lower adjacent order
remains explicit with its original negative sign. -/
theorem heat_factor_closed {B : ℝ} (hB : 0 < B) (N : ℕ) {x : ℂ} (hx : x ≠ 0)
    (q : Polynomial ℂ) (r s : ℂ) :
    heat B (N + 1) x ((Polynomial.X - Polynomial.C r) * q) (s + 2 * (B : ℂ) * x) =
      (s - r) * heat B (N + 1) x q (s + 2 * (B : ℂ) * x) +
        2 * (B : ℂ) * x * heat B (N + 2) x q (s + 2 * (B : ℂ) * x) -
        (((N : ℂ) + 1) * x⁻¹) * heat B N x q (s + 2 * (B : ℂ) * x) := by
  rw [heat_factor_mul_succ hB, show N + 2 = (N + 1) + 1 by omega, heat_succ B (N + 1)]
  field_simp
  ring

end
end RiemannGaussian.FactorialPolynomialTransport

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open GaussianPolynomialTransport GaussianFermiZeroPair FactorialPolynomialTransport GaussianSimplePoleHeat

private theorem factorial_monomial_succ (N : ℕ) (x : ℂ) :
    ((N : ℂ) + 1) * (x ^ (N + 1) / ((N + 1).factorial : ℂ)) =
      x * (x ^ N / (N.factorial : ℂ)) := by
  have hN : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNp : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

private theorem coefficient_log_ne_zero {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : primeCorrectionCoefficient D S n ≠ 0) :
    (Real.log n : ℂ) ≠ 0 := by
  have hp : n.Prime := by
    by_contra h
    simp [primeCorrectionCoefficient_eq_prime_tail hD S hS, h] at hn
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

private theorem operator_term_closed {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) (r : ℂ)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) (s : ℂ) (n : ℕ) :
    let f := fun k p ↦ primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 k s n *
      (window B (Real.log n) : ℂ) * heat B k (Real.log n : ℂ) p (s + 2 * (B : ℂ) * (Real.log n : ℂ));
    f (N + 1) ((Polynomial.X - Polynomial.C r) * q) =
      (s - r) * f (N + 1) q - f N q + 2 * (B : ℂ) * ((N : ℂ) + 2) * f (N + 2) q := by
  dsimp only
  by_cases hn : primeCorrectionCoefficient D S n = 0
  · simp only [hn, zero_mul, mul_zero, sub_zero, add_zero]
  have hx := coefficient_log_ne_zero hD S hS hn
  rw [heat_factor_closed hB N hx]
  simp_rw [primeFilterKernel_one]
  have hdown := factorial_monomial_succ N (Real.log n : ℂ)
  have hup := factorial_monomial_succ (N + 1) (Real.log n : ℂ)
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hup
  have hinv : (Real.log n : ℂ) * (Real.log n : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hx
  linear_combination
    (primeCorrectionCoefficient D S n * zetaPrimeFeature s n * (window B (Real.log n) : ℂ) *
      heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)) * (Real.log n : ℂ)⁻¹) * (-hdown) +
    (2 * (B : ℂ) * primeCorrectionCoefficient D S n * zetaPrimeFeature s n * (window B (Real.log n) : ℂ) *
      heat B (N + 2) (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ))) * (-hup) +
    (primeCorrectionCoefficient D S n * zetaPrimeFeature s n * (window B (Real.log n) : ℂ) *
      heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)) *
      ((Real.log n : ℂ) ^ N / (N.factorial : ℂ))) * (-hinv)

/-- Multiplying any clearing cofactor by a linear factor has a closed
three-order identity for the complete actual prime heat. The derivative
channel has cancelled exactly; all sums are genuinely convergent. -/
theorem clearedHeatPrimeResponse_three_order {B : ℝ} (hB : 0 < B)
    (q : Polynomial ℂ) (r : ℂ) {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    clearedHeatPrimeResponse B ((Polynomial.X - Polynomial.C r) * q) D S (N + 1) s =
      (s - r) * clearedHeatPrimeResponse B q D S (N + 1) s -
        clearedHeatPrimeResponse B q D S N s +
        2 * (B : ℂ) * ((N : ℂ) + 2) * clearedHeatPrimeResponse B q D S (N + 2) s := by
  have hsource := hasSum_clearedHeatPrime_operator hB ((Polynomial.X - Polynomial.C r) * q)
    hD S hS (N + 1) hs
  have h := ((hasSum_clearedHeatPrime_operator hB q hD S hS (N + 1) hs).mul_left (s - r)).sub
    (hasSum_clearedHeatPrime_operator hB q hD S hS N hs)
  have ht := h.add ((hasSum_clearedHeatPrime_operator hB q hD S hS (N + 2) hs).mul_left
    (2 * (B : ℂ) * ((N : ℂ) + 2)))
  have he := operator_term_closed hB q r hD S hS N s
  have heq : (fun n ↦ primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 (N + 1) s n *
      (window B (Real.log n) : ℂ) * heat B (N + 1) (Real.log n : ℂ)
        ((Polynomial.X - Polynomial.C r) * q) (s + 2 * (B : ℂ) * (Real.log n : ℂ))) =
      (fun n ↦ (s - r) * (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 (N + 1) s n *
        (window B (Real.log n) : ℂ) * heat B (N + 1) (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ))) -
        primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 N s n * (window B (Real.log n) : ℂ) *
          heat B N (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)) +
        (2 * (B : ℂ) * ((N : ℂ) + 2)) * (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel 1 (N + 2) s n *
          (window B (Real.log n) : ℂ) * heat B (N + 2) (Real.log n : ℂ) q (s + 2 * (B : ℂ) * (Real.log n : ℂ)))) :=
    funext he
  rw [heq] at hsource
  exact hsource.unique ht

/-- At the genuine selected zero, the closed recurrence retains the
same source normalization in all three adjacent orders. Its left side
contains the extra factor that removes that selected pole. -/
theorem normalizedClearedPrimeHeat_three_order {B : ℝ} (hB : 0 < B)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (rho : NontrivialZetaZero) (N : ℕ) :
    (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
      clearedHeatPrimeResponse B
        ((Polynomial.X - Polynomial.C rho.1) * normalizedPrimeTailClearingPolynomial D S rho)
        D S (N + 1) (zetaWronskianMomentCenter rho) =
      normalizedClearedPrimeHeat D S rho (N + 1) B - normalizedClearedPrimeHeat D S rho N B +
        (2 * (B : ℂ) * ((N : ℂ) + 2) / (clearedPrimeSourceDistance rho : ℂ) ^ 2) *
          normalizedClearedPrimeHeat D S rho (N + 2) B := by
  rw [clearedHeatPrimeResponse_three_order hB _ rho.1 hD S hS N (by norm_num [zetaWronskianMomentCenter]),
    zetaWronskianMomentCenter_sub]
  change (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
    ((clearedPrimeSourceDistance rho : ℂ) * _ - _ + _) = _
  have hu : (clearedPrimeSourceDistance rho : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (clearedPrimeSourceDistance_pos rho).ne'
  unfold normalizedClearedPrimeHeat
  simp only [show N + 1 + 1 = N + 2 by omega, show N + 2 + 1 = N + 3 by omega]
  field_simp
  ring

/-- On the explicit quadratic schedule the upper-order coefficient is
exactly `2c/(N+1)`. All three orders are evaluated at the same `N`-th
width; this identity does not silently replace it by neighboring widths. -/
theorem normalizedClearedPrimeHeat_three_order_quadraticWidth {c : ℝ} (hc : 0 < c)
    {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (rho : NontrivialZetaZero) (N : ℕ) :
    let B := quadraticWidth c (clearedPrimeSourceDistance rho) N;
    (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
      clearedHeatPrimeResponse B
        ((Polynomial.X - Polynomial.C rho.1) * normalizedPrimeTailClearingPolynomial D S rho)
        D S (N + 1) (zetaWronskianMomentCenter rho) =
      normalizedClearedPrimeHeat D S rho (N + 1) B - normalizedClearedPrimeHeat D S rho N B +
        (2 * (c : ℂ) / ((N : ℂ) + 1)) * normalizedClearedPrimeHeat D S rho (N + 2) B := by
  dsimp only
  rw [normalizedClearedPrimeHeat_three_order (quadraticWidth_pos hc (clearedPrimeSourceDistance_pos rho) N)
    hD S hS rho N]
  have hu : (clearedPrimeSourceDistance rho : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (clearedPrimeSourceDistance_pos rho).ne'
  have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hN2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  congr 2
  unfold quadraticWidth
  push_cast
  field_simp

end
end RiemannGaussian.SquarefreeEulerQuadratic
