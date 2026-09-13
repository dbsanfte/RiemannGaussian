/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaCubicBoundaryTest
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!+# Signed logarithmic phase expansion for the Vinogradov--Korobov method

The logarithmic phase admits an exact polynomial expansion with a signed
integral remainder. The remainder bound holds for every nonnegative argument,
including the endpoint one, without an infinite-series convergence premise.
The complex phase identity is retained before invoking the repository's
unit-phase Lipschitz estimate.

This is the elementary phase-expansion step used in Bellotti (2023),
Section 8, Lemma 8.2: <https://arxiv.org/html/2306.10680v1#S8>.
It supplies no Vinogradov mean-value bound or zeta zero-free region by itself.
-/

namespace RiemannGaussian.VinogradovKorobovLogPhase
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators Interval

/-- The degree-`k` logarithmic polynomial, retaining its alternating signs. -/
def logarithmPolynomial (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * x ^ (j + 1) / (j + 1)

/-- The positive amplitude of the exact signed logarithmic remainder. -/
def remainder (k : ℕ) (x : ℝ) : ℝ :=
  ∫ u : ℝ in 0..x, u ^ k / (1 + u)

/-- The remainder integral has no singularity on the nonnegative interval. -/
theorem intervalIntegrable_remainder (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun u : ℝ => u ^ k / (1 + u)) volume 0 x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  exact (continuous_pow k).continuousOn.div (by fun_prop) (fun u hu => by linarith [hu.1])

/-- Consecutive remainder amplitudes sum to the exact integrated monomial. -/
theorem remainder_add_succ (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    remainder k x + remainder (k + 1) x = x ^ (k + 1) / (k + 1) := by
  unfold remainder
  rw [← intervalIntegral.integral_add (intervalIntegrable_remainder k hx)
    (intervalIntegrable_remainder (k + 1) hx)]
  have he : (∫ u : ℝ in 0..x, u ^ k / (1 + u) + u ^ (k + 1) / (1 + u)) =
      ∫ u : ℝ in 0..x, u ^ k := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := (uIcc_of_le hx ▸ hu).1
    have hd : 1 + u ≠ 0 := by linarith
    dsimp only
    rw [← add_div, pow_succ]
    field_simp
  rw [he, integral_pow]
  simp

/-- The initial remainder is the actual real logarithm. -/
theorem remainder_zero {x : ℝ} (hx : 0 ≤ x) : remainder 0 x = Real.log (1 + x) := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) x,
      HasDerivAt (fun v : ℝ => Real.log (1 + v)) (u ^ 0 / (1 + u)) u := by
    intro u hu
    have hu0 : 0 ≤ u := (uIcc_of_le hx ▸ hu).1
    simpa using ((hasDerivAt_id u).const_add 1).log (by linarith : 1 + u ≠ 0)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_remainder 0 hx)
  simpa [remainder] using he

/-- The full logarithm is the polynomial plus its parity-signed integral remainder. -/
theorem logarithm_eq_polynomial_add_remainder (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) = logarithmPolynomial k x + (-1 : ℝ) ^ k * remainder k x := by
  induction k with
  | zero => simp [logarithmPolynomial, remainder_zero hx]
  | succ k ih =>
    have hr := remainder_add_succ k hx
    have hp : logarithmPolynomial (k + 1) x = logarithmPolynomial k x +
        (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1) := by
      exact Finset.sum_range_succ _ _
    rw [hp, pow_succ (-1 : ℝ), ih, mul_div_assoc, ← hr]
    ring

/-- The signed remainder amplitude is nonnegative. -/
theorem remainder_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ remainder k x := by
  apply intervalIntegral.integral_nonneg hx
  intro u hu
  exact div_nonneg (pow_nonneg hu.1 k) (by linarith [hu.1])

/-- The entire exact remainder is bounded by the next integrated monomial. -/
theorem remainder_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    remainder k x ≤ x ^ (k + 1) / (k + 1) := by
  linarith [remainder_add_succ k hx, remainder_nonneg (k + 1) hx]

/-- The next-term Taylor bound holds for all nonnegative arguments. -/
theorem abs_logarithm_sub_polynomial_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - logarithmPolynomial k x| ≤ x ^ (k + 1) / (k + 1) := by
  rw [logarithm_eq_polynomial_add_remainder k hx, add_sub_cancel_left, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (remainder_nonneg k hx)]
  exact remainder_le k hx

/-- The exact complex correction retains the sign and the whole phase. -/
theorem phase_eq_polynomial_mul_remainder (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Complex.exp (((-t * Real.log (1 + x) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-t * logarithmPolynomial k x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-t * (-1 : ℝ) ^ k * remainder k x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add, logarithm_eq_polynomial_add_remainder k hx]
  congr 1
  push_cast
  ring

/-- The complex phase error pays only the next logarithmic monomial. -/
theorem phase_error_le (k : ℕ) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (((-t * Real.log (1 + x) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((-t * logarithmPolynomial k x : ℝ) : ℂ) * Complex.I)‖ ≤
        |t| * x ^ (k + 1) / (k + 1) := by
  have h := norm_exp_ofReal_mul_I_sub_le (-t * Real.log (1 + x)) (-t * logarithmPolynomial k x)
  have he : -t * Real.log (1 + x) - -t * logarithmPolynomial k x =
      -t * (Real.log (1 + x) - logarithmPolynomial k x) := by ring
  rw [he, abs_mul, abs_neg] at h
  exact h.trans (by
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left (abs_logarithm_sub_polynomial_le k hx) (abs_nonneg t))

end
end RiemannGaussian.VinogradovKorobovLogPhase
