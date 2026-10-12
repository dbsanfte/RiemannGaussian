/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorLcmAudit

/-!
# Nonlinear LCM cutoff: exact joined quadratic and Gamma-phase gate

Two distinct divisor columns are retained. The literal floor kernel counts
their common multiples, including the cutoff endpoint. Its PSD statement
is free: it holds for every complex column array. Evaluating the actual
Gamma specialization after twisting requires the cofactor phase too;
then the entire quadratic loses its height dependence. Cancelling its
density by height codes therefore cancels every source as well.

This freezes the common-multiple Gram/complete-Gamma prototype, not an
estimate for a signed, prime-specific cross-column discrepancy.
-/

namespace RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
noncomputable section
open scoped BigOperators ComplexConjugate
open ArithmeticOperatorKummerCutoff ArithmeticOperatorGcdAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation

/-- Complete nonlinear pair kernel, with all integer multiples retained. -/
def cutoffPair (X : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 X,
    f d*g e*((X/Nat.lcm d e : ℕ) : ℂ)

/-- Both divisor columns meet the same literal row. -/
def cutoffRows (X : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, divisorObservation f n*divisorObservation g n

private theorem observation_eq_finite {X n : ℕ} (hn : 0 < n) (hnX : n ≤ X)
    (f : ℕ → ℂ) :
    divisorObservation f n = ∑ d ∈ Finset.Icc 1 X, if d ∣ n then f d else 0 := by
  classical
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hn.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hnX⟩, hd⟩
  rw [← Finset.sum_filter, he]
  rfl

/-- Literal LCM/cutoff reindexing. No prime support, phase, or positivity
assumption occurs, and no endpoint is lost. -/
theorem cutoffPair_eq_rows (X : ℕ) (f g : ℕ → ℂ) :
    cutoffPair X f g = cutoffRows X f g := by
  classical
  have hc (d e : ℕ) :
      (∑ n ∈ Finset.Icc 1 X, if d ∣ n ∧ e ∣ n then (1 : ℂ) else 0) =
        ((X/Nat.lcm d e : ℕ) : ℂ) := by
    simp_rw [← Nat.lcm_dvd_iff]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    convert Nat.Ioc_filter_dvd_card_eq_div X (Nat.lcm d e) using 1
    congr 2
  unfold cutoffPair cutoffRows
  simp_rw [← hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [observation_eq_finite (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
    observation_eq_finite (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he]

/-- The full cross-column quadratic, rather than denominatorwise norms. -/
theorem cutoffPair_eq_squared_rows (X : ℕ) (f : ℕ → ℂ) :
    cutoffPair X f (fun d => conj (f d)) =
      ∑ n ∈ Finset.Icc 1 X, ((‖divisorObservation f n‖^2 : ℝ) : ℂ) := by
  rw [cutoffPair_eq_rows]
  unfold cutoffRows divisorObservation
  simp only [map_sum, Complex.sq_norm, ← Complex.mul_conj]

/-- Positivity is valid for every complex column array, including smooth
or generalized-prime arrays on this incidence lattice. By itself it is
not an additional source-sensitive restriction on the actual primes. -/
theorem cutoffPair_nonnegative (X : ℕ) (f : ℕ → ℂ) :
    0 ≤ (cutoffPair X f (fun d => conj (f d))).re := by
  rw [cutoffPair_eq_squared_rows, Complex.re_sum]
  simpa only [Complex.ofReal_re] using
    (Finset.sum_nonneg (fun n _ => sq_nonneg ‖divisorObservation f n‖))

/-- Actual untwisted factorization evaluates the whole quadratic exactly.
This Gamma identity is not asserted for arbitrary column arrays. -/
theorem cutoffPair_mangoldt (X : ℕ) :
    cutoffPair X (fun d => (ArithmeticFunction.vonMangoldt d : ℂ))
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) =
      ∑ n ∈ Finset.Icc 1 X, (((Real.log n)^2 : ℝ) : ℂ) := by
  rw [cutoffPair_eq_rows]
  unfold cutoffRows
  simp only [divisorObservation_vonMangoldt, ← pow_two, Complex.ofReal_pow]

/-- Complete cofactor-phase insertion is the exact Gamma-compatible
twist, with every prime power retained. -/
def gammaQuadratic (X : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, ‖coupledDivisor (primePhase y) n‖^2

/-- The Gamma-compatible quadratic is height independent. It therefore
cannot expose a height-matched zero source by a modulation code. -/
theorem gammaQuadratic_eq (X : ℕ) (y : ℝ) :
    gammaQuadratic X y = ∑ n ∈ Finset.Icc 1 X, (Real.log n)^2 := by
  unfold gammaQuadratic
  apply Finset.sum_congr rfl
  intro n hn
  rw [coupledDivisor_primePhase y (Finset.mem_Icc.mp hn).1, norm_mul,
    norm_primePhase, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Any finite complex height code cancelling this density cancels the
ENTIRE Gamma-compatible statistic exactly, at every integer cutoff.
No asymptotic or zeta hypothesis is used. -/
theorem gamma_height_code_eq_zero {ι : Type*} (S : Finset ι)
    (coeff : ι → ℂ) (height : ι → ℝ)
    (hcenter : ∑ i ∈ S, coeff i = 0) (X : ℕ) :
    (∑ i ∈ S, coeff i*(gammaQuadratic X (height i) : ℂ)) = 0 := by
  simp_rw [gammaQuadratic_eq]
  rw [← Finset.sum_mul, hcenter, zero_mul]

end
end RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
