/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailConvolution
import Mathlib.Data.Finset.NatDivisors

/-!
# Complete signed Möbius fibres and their cutoff boundary

For coprime factors `P` and `n`, the actual logarithmic tail splits into
complete divisor fibres over `P`. A fully retained fibre has exactly its
von Mangoldt value. In particular, if `P > 1` is not a prime power, every
complete fibre cancels before taking a norm. Only divisors `d` of `n` with
`d ≤ D < P*d` can then contribute.

The identity is coefficientwise, so arbitrary complex weights and phases
can be retained downstream. The boundary is not asserted to decay.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original tail coefficient as a sum over its signed divisors. -/
theorem zetaMoebiusLogTailCoefficient_divisors (D n : ℕ) :
    zetaMoebiusLogTailCoefficient D n =
      ∑ d ∈ n.divisors, if D < d then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq]
  exact Nat.sum_divisorsAntidiagonal
    (fun d k ↦ if D < d then (μ d : ℂ) * (Real.log k : ℂ) else 0)

/-- All divisors of coprime factors are retained, with no multiplicity
or phase loss in the product reindexing. -/
theorem sum_divisors_coprime_product {P n : ℕ} (hcop : P.Coprime n) (f : ℕ → ℂ) :
    (∑ b ∈ (P * n).divisors, f b) = ∑ d ∈ n.divisors, ∑ a ∈ P.divisors, f (a * d) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hcop.mul_injOn_divisors,
    Finset.sum_product]
  exact Finset.sum_comm

private theorem log_nat_div {n d : ℕ} (hd : d ∈ n.divisors) :
    Real.log (n / d : ℕ) = Real.log n - Real.log d := by
  have hdn := Nat.dvd_of_mem_divisors hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hn0 := (Nat.mem_divisors.mp hd).2
  rw [Nat.cast_div hdn (by exact_mod_cast hd0.ne'),
    Real.log_div (by exact_mod_cast hn0) (by exact_mod_cast hd0.ne')]

private theorem sum_moebius_complex (P : ℕ) :
    (∑ a ∈ P.divisors, (μ a : ℂ)) = if P = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ ↦ f P)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

/-- A complete affine logarithmic fibre has only the exact prime-power
leakage. Its constant logarithmic offset cancels whenever `P ≠ 1`. -/
theorem sum_moebius_log_affine (P : ℕ) (t : ℂ) :
    (∑ a ∈ P.divisors, (μ a : ℂ) * (t - (Real.log a : ℂ))) =
      (if P = 1 then 1 else 0) * t + (ArithmeticFunction.vonMangoldt P : ℂ) := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_moebius_complex]
  have h : (∑ a ∈ P.divisors, (μ a : ℂ) * (Real.log a : ℂ)) =
      -(ArithmeticFunction.vonMangoldt P : ℂ) := by
    exact_mod_cast (ArithmeticFunction.sum_moebius_mul_log_eq (n := P))
  rw [h, sub_neg_eq_add]

/-- One exact signed divisor fibre; the full product determines the
logarithm, and the original strict divisor cutoff is unchanged. -/
def zetaMoebiusLogDivisorFibre (D P n d : ℕ) : ℂ :=
  ∑ a ∈ P.divisors, if D < a * d then
    (μ a : ℂ) * ((Real.log (P * n) : ℂ) - (Real.log (a * d) : ℂ)) else 0

/-- Multiplicative reindexing of the literal coefficient keeps every
Möbius sign and every cutoff comparison inside its complete fibre. -/
theorem zetaMoebiusLogTailCoefficient_eq_fibres (D : ℕ) {P n : ℕ}
    (hcop : P.Coprime n) :
    zetaMoebiusLogTailCoefficient D (P * n) =
      ∑ d ∈ n.divisors, (μ d : ℂ) * zetaMoebiusLogDivisorFibre D P n d := by
  rw [zetaMoebiusLogTailCoefficient_divisors, sum_divisors_coprime_product hcop]
  apply Finset.sum_congr rfl
  intro d hd
  rw [zetaMoebiusLogDivisorFibre, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have had : a * d ∈ (P * n).divisors := Nat.mem_divisors.mpr
    ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hd),
      mul_ne_zero (Nat.mem_divisors.mp ha).2 (Nat.mem_divisors.mp hd).2⟩
  have hca := (hcop.of_dvd_left (Nat.dvd_of_mem_divisors ha)).of_dvd_right
    (Nat.dvd_of_mem_divisors hd)
  by_cases hcut : D < a * d
  · rw [if_pos hcut, if_pos hcut, log_nat_div had,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hca]
    push_cast
    ring
  · simp [hcut]

/-- A fully retained fibre is evaluated before any absolute value is
taken. For a factor with multiple distinct primes it is exactly zero. -/
theorem zetaMoebiusLogDivisorFibre_complete (D P n : ℕ) {d : ℕ} (hd : D < d) :
    zetaMoebiusLogDivisorFibre D P n d =
      (if P = 1 then 1 else 0) * ((Real.log (P * n) : ℂ) - (Real.log d : ℂ)) +
        (ArithmeticFunction.vonMangoldt P : ℂ) := by
  rw [zetaMoebiusLogDivisorFibre]
  calc
    _ = ∑ a ∈ P.divisors, (μ a : ℂ) *
        (((Real.log (P * n) : ℂ) - (Real.log d : ℂ)) - (Real.log a : ℂ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 := Nat.pos_of_mem_divisors ha
      have hd0 : 0 < d := by omega
      rw [if_pos (hd.trans_le (by nlinarith)),
        Real.log_mul (x := (a : ℝ)) (by exact_mod_cast ha0.ne') (by exact_mod_cast hd0.ne')]
      push_cast
      ring
    _ = _ := sum_moebius_log_affine _ _

/-- A fibre entirely below the strict cutoff has no retained term. -/
theorem zetaMoebiusLogDivisorFibre_empty (D P n d : ℕ) (hcut : P * d ≤ D) :
    zetaMoebiusLogDivisorFibre D P n d = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have haP := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2)
    (Nat.dvd_of_mem_divisors ha)
  exact if_neg (not_lt.mpr ((Nat.mul_le_mul_right d haP).trans hcut))

/-- The only possible nonzero fibres for a factor with multiple distinct
primes lie across the actual divisor cutoff. -/
theorem zetaMoebiusLogDivisorFibre_eq_zero_outside {D P n d : ℕ}
    (hP : P ≠ 1) (hprime : ¬IsPrimePow P) (hcut : ¬(d ≤ D ∧ D < P * d)) :
    zetaMoebiusLogDivisorFibre D P n d = 0 := by
  by_cases hd : d ≤ D
  · exact zetaMoebiusLogDivisorFibre_empty _ _ _ _ (by omega)
  · rw [zetaMoebiusLogDivisorFibre_complete D P n (by omega), if_neg hP,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hprime]
    simp

/-- Complete mixed-prime fibres cancel, leaving only the explicit
multiplicative annulus `d ≤ D < P*d`. This is the actual coefficient. -/
theorem zetaMoebiusLogTailCoefficient_eq_boundary (D : ℕ) {P n : ℕ}
    (hcop : P.Coprime n) (hP : P ≠ 1) (hprime : ¬IsPrimePow P) :
    zetaMoebiusLogTailCoefficient D (P * n) =
      ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ D ∧ D < P * d),
        (μ d : ℂ) * zetaMoebiusLogDivisorFibre D P n d := by
  rw [zetaMoebiusLogTailCoefficient_eq_fibres D hcop, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ D ∧ D < P * d
  · rw [if_pos hd]
  · rw [if_neg hd, zetaMoebiusLogDivisorFibre_eq_zero_outside hP hprime hd, mul_zero]

private theorem norm_moebius_le_one (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

private theorem log_product_nonneg (P n : ℕ) : 0 ≤ Real.log ((P : ℝ) * n) := by
  simpa only [Nat.cast_mul] using Real.log_natCast_nonneg (P * n)

/-- A boundary fibre has a finite elementary budget. This estimate is
applied only after every complete fibre has cancelled exactly. -/
theorem norm_zetaMoebiusLogDivisorFibre_le (D P : ℕ) {n d : ℕ} (hd : d ∈ n.divisors) :
    ‖zetaMoebiusLogDivisorFibre D P n d‖ ≤
      (P.divisors.card : ℝ) * Real.log ((P : ℝ) * n) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ P.divisors, Real.log ((P : ℝ) * n) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hcut : D < a * d
      · rw [if_pos hcut, norm_mul, ← Complex.ofReal_sub, Complex.norm_real]
        have had0 : (0 : ℝ) < (a : ℝ) * d := by
          exact_mod_cast Nat.mul_pos (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hd)
        have hadle : (a : ℝ) * d ≤ (P : ℝ) * n := by
          exact_mod_cast Nat.mul_le_mul
            (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2)
              (Nat.dvd_of_mem_divisors ha))
            (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
              (Nat.dvd_of_mem_divisors hd))
        have hlog := Real.log_le_log had0 hadle
        rw [Real.norm_of_nonneg (sub_nonneg.mpr hlog)]
        calc
          _ ≤ 1 * (Real.log ((P : ℝ) * n) - Real.log ((a : ℝ) * d)) :=
            mul_le_mul_of_nonneg_right (norm_moebius_le_one a) (sub_nonneg.mpr hlog)
          _ ≤ _ := by linarith [log_product_nonneg a d]
      · simpa only [if_neg hcut, norm_zero] using log_product_nonneg P n
    _ = _ := by simp

/-- The actual coefficient is bounded using only divisors crossing the
cutoff. The norm of all cancelled interior fibres contributes nothing. -/
theorem norm_zetaMoebiusLogTailCoefficient_le_boundary (D : ℕ) {P n : ℕ}
    (hcop : P.Coprime n) (hP : P ≠ 1) (hprime : ¬IsPrimePow P) :
    ‖zetaMoebiusLogTailCoefficient D (P * n)‖ ≤
      ((n.divisors.filter (fun d ↦ d ≤ D ∧ D < P * d)).card : ℝ) *
        ((P.divisors.card : ℝ) * Real.log ((P : ℝ) * n)) := by
  rw [zetaMoebiusLogTailCoefficient_eq_boundary D hcop hP hprime]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d ↦ d ≤ D ∧ D < P * d),
        (P.divisors.card : ℝ) * Real.log ((P : ℝ) * n) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_moebius_le_one d) (norm_nonneg _)).trans
        (by simpa only [one_mul] using
          norm_zetaMoebiusLogDivisorFibre_le D P (Finset.mem_filter.mp hd).1)
    _ = _ := by simp

/-- If the multiplicative annulus contains no divisor, the original
coefficient vanishes; no estimate on the remaining Möbius signs is needed. -/
theorem zetaMoebiusLogTailCoefficient_eq_zero_of_boundary_empty (D : ℕ) {P n : ℕ}
    (hcop : P.Coprime n) (hP : P ≠ 1) (hprime : ¬IsPrimePow P)
    (hempty : n.divisors.filter (fun d ↦ d ≤ D ∧ D < P * d) = ∅) :
    zetaMoebiusLogTailCoefficient D (P * n) = 0 := by
  rw [zetaMoebiusLogTailCoefficient_eq_boundary D hcop hP hprime, hempty, Finset.sum_empty]

end
end RiemannGaussian
