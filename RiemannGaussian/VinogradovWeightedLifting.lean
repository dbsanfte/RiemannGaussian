/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPrimePowerRigidity

/-!
# Weighted nonsingular prime-power lifting

The exact Taylor remainder and the full Jacobian retain every integer weight.
Weights nonzero modulo the prime preserve uniqueness through every prime-power
precision within a fixed nonsingular ordered residue class. In particular,
this includes all fixed positive/negative sign patterns.
-/

namespace RiemannGaussian.VinogradovWeightedLifting
noncomputable section
open scoped BigOperators
open VinogradovPrimePowerRigidity

/-- Weighted power sums retain an exact integer square-step remainder. -/
theorem weighted_power_remainder {k : ℕ} (c v w : Fin k → ℤ) (q : ℤ) (n : ℕ) :
    ∃ E : ℤ, (∑ j, c j * (v j + q * w j) ^ (n + 1)) =
      (∑ j, c j * v j ^ (n + 1)) +
        q * (∑ j, c j * (n + 1) * v j ^ n * w j) + q ^ 2 * E := by
  choose E hE using fun j => power_remainder (v j) q (w j) n
  refine ⟨∑ j, c j * E j, ?_⟩
  simp_rw [hE]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Dividing a complete weighted power difference by its coarse step
retains the weights in the first-order congruence. -/
theorem weighted_linearized_divisibility {k : ℕ} (c v w : Fin k → ℤ) {p q : ℤ}
    (hq : q ≠ 0) (hpq : p ∣ q) (n : ℕ)
    (h : p * q ∣ (∑ j, c j * (v j + q * w j) ^ (n + 1)) -
      ∑ j, c j * v j ^ (n + 1)) :
    p ∣ ∑ j, c j * (n + 1) * v j ^ n * w j := by
  obtain ⟨E, hE⟩ := weighted_power_remainder c v w q n
  have he : (∑ j, c j * (v j + q * w j) ^ (n + 1)) -
      (∑ j, c j * v j ^ (n + 1)) =
      q * ((∑ j, c j * (n + 1) * v j ^ n * w j) + q * E) := by
    rw [hE]
    ring
  rw [he, mul_comm p q] at h
  have hc : p ∣ (∑ j, c j * (n + 1) * v j ^ n * w j) + q * E :=
    (mul_dvd_mul_iff_left hq).mp h
  have ht : p ∣ q * E := dvd_mul_of_dvd_left hpq E
  simpa only [add_sub_cancel_right] using dvd_sub hc ht

/-- Unit weights do not destroy the nonsingular Jacobian. Every compatible
nonlinear lift increment vanishes modulo the prime. -/
theorem weighted_prime_lift_increment {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (c v w : Fin k → ℤ) (hc : ∀ j, (c j : ZMod p) ≠ 0)
    {q : ℤ} (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hv : Function.Injective (fun i => (v i : ZMod p)))
    (h : ∀ i : Fin k, (p : ℤ) * q ∣
      (∑ j, c j * (v j + q * w j) ^ (i.val + 1)) -
        ∑ j, c j * v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) ∣ w j := by
  have hlin (i : Fin k) := weighted_linearized_divisibility c v w hq hpq i.val (h i)
  have hzero : (fun j => (c j : ZMod p) * (w j : ZMod p)) = 0 := by
    apply prime_linearized_injective hkp (fun i => (v i : ZMod p)) hv
    intro i
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hlin i)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Int.cast_pow, Nat.cast_add, Nat.cast_one,
      mul_comm, mul_left_comm, mul_assoc] using hz
  intro j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  exact (mul_eq_zero.mp (congrFun hzero j)).resolve_left (hc j)

/-- The weighted nonlinear lift applies to any two tuples in the same
ordered coarse residue class. -/
theorem weighted_prime_lift_step {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (c v u : Fin k → ℤ) (hc : ∀ j, (c j : ZMod p) ≠ 0)
    {q : ℤ} (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hv : Function.Injective (fun i => (v i : ZMod p)))
    (hcoarse : ∀ j, q ∣ u j - v j)
    (hpowers : ∀ i : Fin k, (p : ℤ) * q ∣
      (∑ j, c j * u j ^ (i.val + 1)) - ∑ j, c j * v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) * q ∣ u j - v j := by
  choose w hw using hcoarse
  have hu (j) : u j = v j + q * w j := by linarith [hw j]
  have hlift := weighted_prime_lift_increment hkp c v w hc hq hpq hv
    (by simpa only [← hu] using hpowers)
  intro j
  obtain ⟨a, ha⟩ := hlift j
  refine ⟨a, ?_⟩
  rw [hw j, ha]
  ring

/-- Equality of the first k weighted powers determines all prime-power
digits within a nonsingular ordered prime residue class. -/
theorem weighted_prime_power_rigidity {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (c v u : Fin k → ℤ) (hc : ∀ j, (c j : ZMod p) ≠ 0)
    (hv : Function.Injective (fun i => (v i : ZMod p)))
    (hfirst : ∀ j, (p : ℤ) ∣ u j - v j) (n : ℕ)
    (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, c j * u j ^ (i.val + 1)) - ∑ j, c j * v j ^ (i.val + 1)) :
    ∀ j, (p : ℤ) ^ n ∣ u j - v j := by
  induction n with
  | zero => intro j; simp
  | succ n ih =>
    by_cases hn : n = 0
    · simpa only [hn, zero_add, pow_one] using hfirst
    have hp : (p : ℤ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hcoarse := ih (fun i => dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) (hpowers i))
    have hnext := weighted_prime_lift_step hkp c v u hc (pow_ne_zero n hp)
      (dvd_pow_self (p : ℤ) hn) hv hcoarse
      (by simpa only [pow_succ, mul_comm] using hpowers)
    simpa only [pow_succ, mul_comm] using hnext

end
end RiemannGaussian.VinogradovWeightedLifting
