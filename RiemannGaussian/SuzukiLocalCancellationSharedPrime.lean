/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaMoebiusPrimeProduct
import RiemannGaussian.ZetaMoebiusDivisorBoundary

/-!
# Exact cancellation of shared-prime Vaughan fibres

When the prime underlying the von Mangoldt factor also divides the Möbius
factor, completing the latter's strict cutoff leaves only pure powers of
that prime and an explicit finite head. This module proves the finite
coefficient identity. The subsequent kernel-sampling estimate is separate.
-/

open scoped Classical ArithmeticFunction.Moebius

set_option warningAsError true

namespace RiemannGaussian.SuzukiLocalCancellationSharedPrime
noncomputable section

/-- The complete prime-free Möbius divisor sum detects only the remaining
cofactor one; the prime exponent is arbitrary, including zero. -/
theorem primeFree_divisor_sum {p b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) (r : ℕ) :
    (∑ a ∈ (p ^ r * b).divisors, if p ∣ a then (0 : ℂ) else (μ a : ℂ)) =
      if b = 1 then 1 else 0 := by
  rw [sum_divisors_coprime_product ((hp.coprime_iff_not_dvd.mpr hpb).pow_left r)]
  have he : (∑ e ∈ b.divisors, ∑ a ∈ (p ^ r).divisors,
      if p ∣ a * e then (0 : ℂ) else (μ (a * e) : ℂ)) =
      ∑ e ∈ b.divisors, (μ e : ℂ) := by
    apply Finset.sum_congr rfl
    intro e he
    have hpe : ¬p ∣ e := fun h => hpb (h.trans (Nat.dvd_of_mem_divisors he))
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
    have hz : (∑ i ∈ Finset.range r,
        if p ∣ p ^ (i + 1) * e then (0 : ℂ) else (μ (p ^ (i + 1) * e) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hd : p ∣ p ^ (i + 1) * e := ⟨p ^ i * e, by ring⟩
      simp only [ite_eq_left hd]
    simp only [hz, pow_zero, one_mul, ite_eq_right hpe, zero_add]
  rw [he]
  have hm := congrArg (fun f : ArithmeticFunction ℂ => f b)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using hm

/-- Inserting the shared prime reverses the complete prime-free divisor
sum; square-factor Möbius zeros are retained automatically. -/
theorem shared_divisor_sum {p b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) (r : ℕ) :
    (∑ a ∈ (p ^ r * b).divisors, (μ (p * a) : ℂ)) =
      -(if b = 1 then 1 else 0) := by
  rw [← primeFree_divisor_sum hp hpb r, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [moebius_prime_mul_eq_not_dvd hp]
  by_cases ha : p ∣ a <;> simp [ha]

/-- The actual strict Möbius cutoff in a shared-prime convolution fibre. -/
def sharedTailCoefficient (U p n : ℕ) : ℂ :=
  ∑ a ∈ n.divisors, if U < p * a then (μ (p * a) : ℂ) else 0

/-- Completing the original strict cutoff produces one pure-prime-power
term and its explicit prime-free finite head, with their exact signs. -/
theorem sharedTailCoefficient_eq_completed_head {p b : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (r U : ℕ) :
    sharedTailCoefficient U p (p ^ r * b) =
      -(if b = 1 then 1 else 0) +
        ∑ a ∈ (p ^ r * b).divisors,
          if p * a ≤ U ∧ ¬p ∣ a then (μ a : ℂ) else 0 := by
  rw [← shared_divisor_sum hp hpb r, sharedTailCoefficient,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [moebius_prime_mul_eq_not_dvd hp]
  by_cases hpa : p ∣ a <;> by_cases hU : U < p * a <;>
    simp [hpa, hU, Nat.le_of_not_gt, Nat.not_le_of_gt]

/-- Above the original cutoff the shared-prime fibre cancels completely
unless its remaining cofactor is itself a power of that same prime. -/
theorem sharedTailCoefficient_eq_of_cutoff_lt_prime {p b U : ℕ}
    (hp : p.Prime) (hpb : ¬p ∣ b) (hUp : U < p) (r : ℕ) :
    sharedTailCoefficient U p (p ^ r * b) = -(if b = 1 then 1 else 0) := by
  rw [sharedTailCoefficient_eq_completed_head hp hpb]
  have hz : (∑ a ∈ (p ^ r * b).divisors,
      if p * a ≤ U ∧ ¬p ∣ a then (μ a : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hpa : U < p * a := hUp.trans_le (Nat.le_mul_of_pos_right p ha0)
    simp [Nat.not_le_of_gt hpa]
  rw [hz, add_zero]

end
end RiemannGaussian.SuzukiLocalCancellationSharedPrime
