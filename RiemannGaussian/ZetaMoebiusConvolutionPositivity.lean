/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusWronskianArithmetic

/-!
# Positivity from the complete composite Möbius convolution

Keeping the logarithmic convolution inside the signed Möbius sum gives
an exact nonnegative arithmetic function. The intermediate divisor sum
is the prime-divisor logarithmic sum minus von Mangoldt. This is a
coefficient identity at every integer, independent of any selected zeta
zero or filter family. The associated Dirichlet series is identified
with actual zeta using genuine absolute convergence.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The logarithm restricted to prime indices, as an arithmetic function. -/
def zetaPrimeLogArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n.Prime then Real.log n else 0, by simp⟩

/-- The signed composite Möbius logarithm, before convolution or estimates. -/
def zetaMoebiusCompositeArithmetic : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n.Prime then 0 else (μ n : ℝ) * Real.log n, by simp⟩

/-- The complete prime-divisor logarithmic sum minus von Mangoldt. -/
def zetaMixedPrimeArithmetic : ArithmeticFunction ℝ :=
  (ζ : ArithmeticFunction ℝ) * zetaPrimeLogArithmetic - ArithmeticFunction.vonMangoldt

/-- One logarithmic convolution of the signed composite Möbius coefficients. -/
def zetaPositiveCompositeArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.log * zetaMoebiusCompositeArithmetic

/-- The real arithmetic coefficient is exactly the previously retained
complex coefficient, with no alteration of its Möbius sign. -/
theorem zetaMoebiusCompositeArithmetic_cast (n : ℕ) :
    (zetaMoebiusCompositeArithmetic n : ℂ) = zetaMoebiusCompositeDerivativeCoefficient n := by
  by_cases hn : n.Prime <;>
    simp [zetaMoebiusCompositeArithmetic, zetaMoebiusCompositeDerivativeCoefficient,
      zetaMoebiusDerivativeCoefficient, hn]

private theorem composite_arithmetic_eq :
    zetaMoebiusCompositeArithmetic = (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log +
      zetaPrimeLogArithmetic := by
  ext n
  rw [ArithmeticFunction.add_apply]
  by_cases hn : n.Prime
  · simp [zetaMoebiusCompositeArithmetic, zetaPrimeLogArithmetic, hn,
      ArithmeticFunction.pmul_apply, ArithmeticFunction.moebius_apply_prime hn]
  · simp [zetaMoebiusCompositeArithmetic, zetaPrimeLogArithmetic, hn,
      ArithmeticFunction.pmul_apply]

private theorem zeta_mul_moebius_log :
    (ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log =
      -ArithmeticFunction.vonMangoldt := by
  ext n
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.neg_apply] using
    (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))

/-- Summing all composite Möbius divisors cancels their signs exactly
to the prime-divisor defect. No triangle inequality is used. -/
theorem zeta_mul_compositeArithmetic :
    (ζ : ArithmeticFunction ℝ) * zetaMoebiusCompositeArithmetic = zetaMixedPrimeArithmetic := by
  rw [composite_arithmetic_eq, mul_add, zeta_mul_moebius_log, zetaMixedPrimeArithmetic]
  abel

/-- The mixed-prime coefficient retains its explicit finite divisor sum. -/
theorem zetaMixedPrimeArithmetic_apply (n : ℕ) :
    zetaMixedPrimeArithmetic n =
      (∑ d ∈ n.divisors, if d.Prime then Real.log d else 0) - ArithmeticFunction.vonMangoldt n := by
  change ((ζ : ArithmeticFunction ℝ) * zetaPrimeLogArithmetic) n -
    ArithmeticFunction.vonMangoldt n = _
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rfl

private theorem prime_log_nonneg (n : ℕ) : 0 ≤ zetaPrimeLogArithmetic n := by
  by_cases hn : n.Prime <;>
    simp [zetaPrimeLogArithmetic, hn, Real.log_natCast_nonneg]

/-- The exact divisor defect is nonnegative at every integer, including
prime powers; the contribution of their prime base accounts for von Mangoldt. -/
theorem zetaMixedPrimeArithmetic_nonneg (n : ℕ) : 0 ≤ zetaMixedPrimeArithmetic n := by
  change 0 ≤ ((ζ : ArithmeticFunction ℝ) * zetaPrimeLogArithmetic) n -
    ArithmeticFunction.vonMangoldt n
  rw [sub_nonneg, ArithmeticFunction.coe_zeta_mul_apply]
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hmem : p ∈ (p ^ k).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_pow_self p hk.ne', pow_ne_zero _ hp.ne_zero⟩
    simpa only [zetaPrimeLogArithmetic, ArithmeticFunction.coe_mk, if_pos hp] using
      (Finset.single_le_sum (fun d _ ↦ prime_log_nonneg d) hmem)
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    exact Finset.sum_nonneg (fun d _ ↦ prime_log_nonneg d)

/-- The signed logarithmic convolution is exactly a convolution of two
nonnegative arithmetic functions. -/
theorem zetaPositiveCompositeArithmetic_eq :
    zetaPositiveCompositeArithmetic = ArithmeticFunction.vonMangoldt * zetaMixedPrimeArithmetic := by
  rw [zetaPositiveCompositeArithmetic, ← ArithmeticFunction.vonMangoldt_mul_zeta,
    mul_assoc, zeta_mul_compositeArithmetic]

private theorem arithmetic_mul_nonneg {f g : ArithmeticFunction ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun d _ ↦ mul_nonneg (hf d.1) (hg d.2))

/-- The full signed composite Möbius logarithmic convolution has
nonnegative coefficients, without a cutoff or a chosen phase family. -/
theorem zetaPositiveCompositeArithmetic_nonneg (n : ℕ) :
    0 ≤ zetaPositiveCompositeArithmetic n := by
  rw [zetaPositiveCompositeArithmetic_eq]
  exact arithmetic_mul_nonneg (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    zetaMixedPrimeArithmetic_nonneg n

/-- Adding the second logarithmic factor used in the Wronskian response
also preserves the exact coefficientwise positivity. -/
theorem zetaDoubleLogCompositeArithmetic_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.log ^ 2 * zetaMoebiusCompositeArithmetic) n := by
  rw [pow_two, mul_assoc]
  exact arithmetic_mul_nonneg (fun n ↦ Real.log_natCast_nonneg n)
    zetaPositiveCompositeArithmetic_nonneg n

/-- The nonnegative coefficient still equals the literal signed finite
sum over exact products, so its cancellation information remains available. -/
theorem zetaPositiveCompositeArithmetic_convolution :
    (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ)) =
      (fun n : ℕ ↦ (Real.log n : ℂ)) ⍟ zetaMoebiusCompositeDerivativeCoefficient := by
  funext n
  simp only [zetaPositiveCompositeArithmetic, ArithmeticFunction.mul_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, ArithmeticFunction.log_apply, zetaMoebiusCompositeArithmetic_cast,
    LSeries.convolution_def]

private theorem LSeriesHasSum_log {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (Real.log n : ℂ)) s (-deriv riemannZeta s) := by
  have hm := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hm
  have h := hm.convolution (LSeriesHasSum_one hs)
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one,
    div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re hs)] at h
  simpa only [← Complex.natCast_log] using h

/-- The universal zeta response represented by the nonnegative
composite convolution; it does not depend on a selected zero. -/
def zetaPositiveCompositeResponse (s : ℂ) : ℂ :=
  -deriv riemannZeta s * (deriv riemannZeta s / riemannZeta s ^ 2 -
    (logDeriv riemannZeta s + zetaProperPrimePowerSeries s))

/-- The positive arithmetic response is a genuine absolutely convergent
Dirichlet series throughout the Euler half-plane. -/
theorem LSeriesHasSum_zetaPositiveCompositeResponse {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ)) s
      (zetaPositiveCompositeResponse s) := by
  rw [zetaPositiveCompositeArithmetic_convolution]
  exact (LSeriesHasSum_log hs).convolution (LSeriesHasSum_zetaMoebiusCompositeDerivative hs)

/-- The positive response separates into its universal logarithmic
square and the two lower-order zeta terms, retaining every sign. -/
theorem zetaPositiveCompositeResponse_eq (s : ℂ) :
    zetaPositiveCompositeResponse s = -(logDeriv riemannZeta s) ^ 2 +
      deriv riemannZeta s * logDeriv riemannZeta s +
        deriv riemannZeta s * zetaProperPrimePowerSeries s := by
  simp only [zetaPositiveCompositeResponse, logDeriv_apply, div_pow]
  ring

end

end RiemannGaussian
