/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughMoebiusHyperbola

/-!
# Exact prime insertion recurrences for Mobius divisor prefixes

Inserting a new prime p splits a weighted divisor prefix into two complete
prefixes, at D and floor(D/p), before any sign or complex weight is lost.
The mask and its logarithmic companion retain the resulting shell and
prime-logarithm term. At the reflected cutoff floor(p*m/(D+1)), the lower
endpoint is exactly floor(m/(D+1)); this dependence is not estimated away.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughMoebiusPrimeRecurrence
noncomputable section
open RoughMoebiusIncidence RoughMoebiusHyperbola

/-- Exact weighted prime insertion, before any sign or phase is discarded. -/
theorem weighted_prefix_prime (D : ℕ) {p m : ℕ} (hp : p.Prime)
    (hpm : ¬p ∣ m) (w : ℕ → ℂ) :
    (∑ d ∈ (p * m).divisors, if d ≤ D then (μ d : ℂ) * w d else 0) =
      (∑ d ∈ m.divisors, if d ≤ D then (μ d : ℂ) * w d else 0) -
      ∑ d ∈ m.divisors, if d ≤ D / p then (μ d : ℂ) * w (p * d) else 0 := by
  have hcop := hp.coprime_iff_not_dvd.mpr hpm
  rw [sum_divisors_coprime_product hcop, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp.sum_divisors]
  have hpd := hcop.of_dvd_right (Nat.dvd_of_mem_divisors hd)
  have hcut : p * d ≤ D ↔ d ≤ D / p := by
    rw [Nat.le_div_iff_mul_le hp.pos, Nat.mul_comm]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpd]
  simp only [one_mul, ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg,
    neg_one_mul, hcut]
  by_cases h1 : d ≤ D <;> by_cases h2 : d ≤ D / p <;> simp [h1, h2]
  ring

/-- Inserting a new prime leaves the exact difference of two divisor prefixes. -/
theorem mask_prime (D : ℕ) {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬p ∣ m) :
    mask D (p * m) = mask D m - mask (D / p) m := by
  rw [mask, sum_prefix_eq_divisors D (Nat.mul_pos hp.pos hm),
    mask, sum_prefix_eq_divisors D hm, mask, sum_prefix_eq_divisors (D / p) hm]
  simpa using weighted_prefix_prime D hp hpm (fun _ ↦ 1)

/-- The logarithmic companion retains the prime logarithm and lower prefix. -/
theorem logMask_prime (D : ℕ) {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬p ∣ m) :
    logMask D (p * m) = logMask D m - logMask (D / p) m -
      (Real.log p : ℂ) * mask (D / p) m := by
  rw [logMask, sum_prefix_eq_divisors D (Nat.mul_pos hp.pos hm),
    weighted_prefix_prime D hp hpm, logMask, sum_prefix_eq_divisors D hm,
    logMask, sum_prefix_eq_divisors (D / p) hm, mask,
    sum_prefix_eq_divisors (D / p) hm, Finset.mul_sum]
  rw [sub_sub, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases h : d ≤ D / p
  · simp only [if_pos h, Nat.cast_mul, Real.log_mul hp0 hd0, Complex.ofReal_add]
    ring
  · simp [h]

/-- The lower endpoint at a reflected prime product is exactly the
reflected cutoff of its cofactor. -/
theorem reflected_cutoff_div_prime (D p m : ℕ) (hp : 0 < p) :
    (p * m / (D + 1)) / p = m / (D + 1) := by
  rw [Nat.div_right_comm, Nat.mul_div_right _ hp]

/-- The actual adaptive mask is the prime-generated quotient shell. -/
theorem reflected_mask_prime (D : ℕ) {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬p ∣ m) :
    mask (p * m / (D + 1)) (p * m) =
      mask (p * m / (D + 1)) m - mask (m / (D + 1)) m := by
  rw [mask_prime _ hp hm hpm, reflected_cutoff_div_prime D p m hp.pos]

/-- The exact adaptive logarithmic companion keeps its lower-mask term. -/
theorem reflected_logMask_prime (D : ℕ) {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬p ∣ m) :
    logMask (p * m / (D + 1)) (p * m) =
      logMask (p * m / (D + 1)) m - logMask (m / (D + 1)) m -
        (Real.log p : ℂ) * mask (m / (D + 1)) m := by
  rw [logMask_prime _ hp hm hpm, reflected_cutoff_div_prime D p m hp.pos]

end
end RiemannGaussian.RoughMoebiusPrimeRecurrence
