/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityMaskTails

/-!
# The original allocation is small throughout the full parity box

This is uniform over all prime counts up to the proved ceiling, rather
than a special estimate for the triple or quintuple subfamilies.
-/
namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency ZetaRieszBalancedCompanion
open ZetaRieszParityPacket ZetaRieszPrimeEndpoint

theorem interior_allocation_log_rate :
    Real.log (153/160:ℝ)+(13/32:ℝ)*Real.log (10/9:ℝ) ≤ -(1/1000:ℝ) := by
  have h := log_rate_of_power (q := 9/10) (b := 153/160) (c := 1/1000)
    (by norm_num) (by norm_num) 13 32 (by decide) (by norm_num)
  have he : Real.log (9/10:ℝ) = -Real.log (10/9:ℝ) := by
    rw [show (9/10:ℝ) = (10/9:ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he] at h
  norm_num at h
  linarith

/-- The original unpaid majority orders have exponentially small mass when the cofactor carries at least seven sixteenths of the product logarithm. -/
theorem unpaid_mass_interior_le (N : ℕ) {x : ℝ} (hx : (7/16:ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N:ℝ)/1000) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (10/9:ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0:ℝ) ≤ 9/10)
    (Real.exp_pos ((13/32:ℝ)*N*Real.log (10/9:ℝ))).le ?_
  · have hb : ((9/10:ℝ)*x+(1-x))^(N+1) ≤ (153/160:ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32:ℝ)*N*Real.log (10/9:ℝ)) * (153/160:ℝ)^(N+1) =
        (153/160:ℝ)*Real.exp ((N:ℝ)*(Real.log (153/160:ℝ)+(13/32:ℝ)*Real.log (10/9:ℝ))) := by
      rw [pow_succ]
      have hp : (153/160:ℝ)^N = Real.exp ((N:ℝ)*Real.log (153/160:ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<153/160)]
      rw [hp]
      rw [show (N:ℝ)*(Real.log (153/160:ℝ)+(13/32:ℝ)*Real.log (10/9:ℝ)) =
        (13/32:ℝ)*N*Real.log (10/9:ℝ)+(N:ℝ)*Real.log (153/160:ℝ) by ring, Real.exp_add]
      ring
    have hrate : Real.exp ((N:ℝ)*(Real.log (153/160:ℝ)+(13/32:ℝ)*Real.log (10/9:ℝ))) ≤
        Real.exp (-(N:ℝ)/1000) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left interior_allocation_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32:ℝ)*N*Real.log (10/9:ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N:ℝ)/1000)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k:ℝ) ≤ (13/32:ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32:ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (9/10:ℝ) = Real.exp (-Real.log (10/9:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<10/9)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- If all eligible selected primes are balanced, the complete assigned fraction has an exponential saving with its exact prime-count factor. -/
theorem share_small_of_selected_primes_interior (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (9/16:ℝ)*Real.log n) :
    allocationShare A N n ≤ (n.primeFactors.card:ℝ)*Real.exp (-(N:ℝ)/1000) := by
  rw [share_eq_binomial_sum A N hn hn1]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N:ℝ)/1000) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hel : p ∈ A ∧ eligibleCofactor p (n/p)
      · rw [if_pos hel]
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        have hlog : Real.log (n/p:ℕ) = Real.log n-Real.log p := by
          rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero), Real.log_div
            (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
        have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
        apply unpaid_mass_interior_le
        · apply (le_div_iff₀ hln).mpr
          rw [hlog]
          linarith [hbal p hp hel.1 hel.2]
        · apply (div_le_one hln).mpr
          rw [hlog]
          linarith [Real.log_natCast_nonneg p]
      · rw [if_neg hel]
        exact (Real.exp_pos _).le
    _ = _ := by simp

/-- Every selected prime in the actual interior box has small original
allocated mass. The count ceiling supplies a fixed factor of 39. -/
theorem fullParityBox_boundedShare {n : ℕ} (h : FullParityBox n) (A : Finset ℕ) (N : ℕ) :
    boundedShare A N n ≤ 39*Real.exp (-(N:ℝ)/1000) := by
  unfold boundedShare
  split_ifs
  · have hb := share_small_of_selected_primes_interior A N h.squarefree h.nontrivial (by
      intro p hp _ _
      have hne : n.primeFactors.Nonempty := ⟨p,hp⟩
      have hpl : p ≤ largestPrime n := by
        rw [largestPrime, dif_pos hne]
        exact Finset.le_max' _ _ hp
      exact (Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by exact_mod_cast hpl)).trans h.largest_upper)
    exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast fullParityBox_count_le h)
      (Real.exp_pos _).le)
  · positivity

end
end RiemannGaussian.ZetaRieszParityOrderTail
