/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusDivisorBoundary

/-!
# Two finite prefixes for a complete coprime factor sector

After complete divisor fibres cancel, their logarithms separate into a
cofactor logarithm and a fixed factor logarithm. For a mixed-prime factor,
the literal restricted coefficient is therefore a sum of two Dirichlet
convolutions whose signed first factors have finite support through `D`.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The complete signed slope of the retained divisor fibre. -/
def zetaMoebiusFibreSlope (D P d : ℕ) : ℂ :=
  ∑ a ∈ P.divisors, if D < a * d then (μ a : ℂ) else 0

/-- The factor logarithm left after separating the cofactor coordinate. -/
def zetaMoebiusFibreIntercept (D P d : ℕ) : ℂ :=
  ∑ a ∈ P.divisors, if D < a * d then
    (μ a : ℂ) * ((Real.log P : ℂ) - (Real.log a : ℂ)) else 0

/-- The affine decomposition retains the same strict cutoff in both
coefficients; the moving divisor does not enter the intercept logarithm. -/
theorem zetaMoebiusLogDivisorFibre_eq_affine (D : ℕ) {P n d : ℕ}
    (hP : 0 < P) (hd : d ∈ n.divisors) :
    zetaMoebiusLogDivisorFibre D P n d =
      zetaMoebiusFibreSlope D P d * (Real.log (n / d : ℕ) : ℂ) +
        zetaMoebiusFibreIntercept D P d := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have hn0 := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hlog : Real.log (n / d : ℕ) = Real.log n - Real.log d := by
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast hd0.ne'),
      Real.log_div (by exact_mod_cast hn0.ne') (by exact_mod_cast hd0.ne')]
  rw [zetaMoebiusLogDivisorFibre, zetaMoebiusFibreSlope, zetaMoebiusFibreIntercept,
    Finset.sum_mul, ← Finset.sum_add_distrib, hlog]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcut : D < a * d
  · rw [if_pos hcut, if_pos hcut, if_pos hcut,
      Real.log_mul (x := (P : ℝ)) (y := (n : ℝ))
        (by exact_mod_cast hP.ne') (by exact_mod_cast hn0.ne'),
      Real.log_mul (x := (a : ℝ)) (y := (d : ℝ))
        (by exact_mod_cast (Nat.pos_of_mem_divisors ha).ne') (by exact_mod_cast hd0.ne')]
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  · simp [hcut]

/-- The actual slope prefix, with coprimality and the finite cutoff retained. -/
def zetaMoebiusFactorSlope (D P d : ℕ) : ℂ :=
  if d ≤ D ∧ P.Coprime d then (μ d : ℂ) * zetaMoebiusFibreSlope D P d else 0

/-- The actual intercept prefix with the same divisor signs and support. -/
def zetaMoebiusFactorIntercept (D P d : ℕ) : ℂ :=
  if d ≤ D ∧ P.Coprime d then (μ d : ℂ) * zetaMoebiusFibreIntercept D P d else 0

/-- The positive-index coprimality indicator used in genuine Dirichlet series. -/
def zetaCoprimeCoefficient (P n : ℕ) : ℂ := if n ≠ 0 ∧ P.Coprime n then 1 else 0

/-- The logarithm on the exact same coprime support. -/
def zetaCoprimeLogCoefficient (P n : ℕ) : ℂ :=
  zetaCoprimeCoefficient P n * (Real.log n : ℂ)

/-- The original coefficient on products with the selected factor,
before the fixed dilation by `P` is reinserted into its Dirichlet weight. -/
def zetaMoebiusFactorCoefficient (D P n : ℕ) : ℂ :=
  if P.Coprime n then zetaMoebiusLogTailCoefficient D (P * n) else 0

/-- Both finite signed prefixes vanish at the zero index. -/
theorem zetaMoebiusFactorPrefix_zero (D P : ℕ) :
    zetaMoebiusFactorSlope D P 0 = 0 ∧ zetaMoebiusFactorIntercept D P 0 = 0 := by
  simp [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept]

/-- Neither signed prefix has support beyond the original cutoff. -/
theorem zetaMoebiusFactorPrefix_support (D P : ℕ) {d : ℕ} (hd : D < d) :
    zetaMoebiusFactorSlope D P d = 0 ∧ zetaMoebiusFactorIntercept D P d = 0 := by
  simp [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept, not_le.mpr hd]

private theorem convolution_divisors (a b : ℕ → ℂ) (n : ℕ) :
    (a ⍟ b) n = ∑ d ∈ n.divisors, a d * b (n / d) := by
  rw [LSeries.convolution_def]
  exact Nat.sum_divisorsAntidiagonal (fun d r ↦ a d * b r)

/-- The literal mixed-prime sector is exactly two convolutions with
finite signed prefixes. Every discarded large-divisor term is proved zero. -/
theorem zetaMoebiusFactorCoefficient_eq_convolutions (D : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) :
    zetaMoebiusFactorCoefficient D P =
      zetaMoebiusFactorSlope D P ⍟ zetaCoprimeLogCoefficient P +
        zetaMoebiusFactorIntercept D P ⍟ zetaCoprimeCoefficient P := by
  funext n
  simp only [Pi.add_apply, convolution_divisors, ← Finset.sum_add_distrib]
  by_cases hn : n = 0
  · subst n
    simp [zetaMoebiusFactorCoefficient, zetaMoebiusLogTailCoefficient]
  by_cases hcop : P.Coprime n
  · rw [zetaMoebiusFactorCoefficient, if_pos hcop,
      zetaMoebiusLogTailCoefficient_eq_fibres D hcop]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_mem_divisors hd
    have hr0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hd0
    have hcd := hcop.of_dvd_right hdn
    have hcr := hcop.of_dvd_right (Nat.div_dvd_of_dvd hdn)
    have hZ : zetaCoprimeCoefficient P (n / d) = 1 := if_pos ⟨hr0.ne', hcr⟩
    simp only [zetaCoprimeLogCoefficient, hZ, one_mul, mul_one]
    by_cases hcut : d ≤ D
    · rw [zetaMoebiusLogDivisorFibre_eq_affine D hP hd]
      have hcut' : d ≤ D ∧ P.Coprime d := ⟨hcut, hcd⟩
      simp only [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept, if_pos hcut']
      ring
    · rw [(zetaMoebiusFactorPrefix_support D P (by omega)).1,
        (zetaMoebiusFactorPrefix_support D P (by omega)).2,
        zetaMoebiusLogDivisorFibre_eq_zero_outside hP1 hmix (by omega)]
      simp
  · rw [zetaMoebiusFactorCoefficient, if_neg hcop]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hnot : ¬(P.Coprime d ∧ P.Coprime (n / d)) := by
      intro hc
      apply hcop
      have h := hc.1.mul_right hc.2
      rwa [Nat.mul_div_cancel' hdn] at h
    by_cases hcd : P.Coprime d
    · have hcr : ¬P.Coprime (n / d) := by tauto
      simp [zetaCoprimeLogCoefficient, zetaCoprimeCoefficient, hcr]
    · simp [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept, hcd]

private theorem norm_moebius_le_one (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- The whole signed slope has a cutoff-independent coefficient bound. -/
theorem norm_zetaMoebiusFibreSlope_le (D P d : ℕ) :
    ‖zetaMoebiusFibreSlope D P d‖ ≤ P.divisors.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ P.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact norm_moebius_le_one a
      · simp
    _ = _ := by simp

/-- The intercept also has a cutoff-independent coefficient bound;
the estimate involves only the fixed factor logarithm. -/
theorem norm_zetaMoebiusFibreIntercept_le (D P d : ℕ) :
    ‖zetaMoebiusFibreIntercept D P d‖ ≤ (P.divisors.card : ℝ) * Real.log P := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ P.divisors, Real.log P := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs
      · have haP := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2)
          (Nat.dvd_of_mem_divisors ha)
        have hlog : Real.log a ≤ Real.log P := Real.log_le_log
          (by exact_mod_cast Nat.pos_of_mem_divisors ha)
          (by exact_mod_cast haP)
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr hlog)]
        have h := mul_le_mul_of_nonneg_right (norm_moebius_le_one a) (sub_nonneg.mpr hlog)
        nlinarith [Real.log_natCast_nonneg a]
      · simpa only [norm_zero] using Real.log_natCast_nonneg P
    _ = _ := by simp

/-- Both actual finite prefix coefficient bounds are uniform in `D`.
No estimate for a Möbius partial sum is assumed. -/
theorem norm_zetaMoebiusFactorPrefix_le (D P d : ℕ) :
    ‖zetaMoebiusFactorSlope D P d‖ ≤ P.divisors.card ∧
      ‖zetaMoebiusFactorIntercept D P d‖ ≤ (P.divisors.card : ℝ) * Real.log P := by
  by_cases hcut : d ≤ D ∧ P.Coprime d
  · simp only [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept, if_pos hcut, norm_mul]
    constructor
    · exact (mul_le_mul_of_nonneg_right (norm_moebius_le_one d) (norm_nonneg _)).trans
        (by simpa only [one_mul] using norm_zetaMoebiusFibreSlope_le D P d)
    · exact (mul_le_mul_of_nonneg_right (norm_moebius_le_one d) (norm_nonneg _)).trans
        (by simpa only [one_mul] using norm_zetaMoebiusFibreIntercept_le D P d)
  · simp only [zetaMoebiusFactorSlope, zetaMoebiusFactorIntercept, if_neg hcut, norm_zero]
    exact ⟨by positivity, mul_nonneg (by positivity) (Real.log_natCast_nonneg P)⟩

end
end RiemannGaussian
