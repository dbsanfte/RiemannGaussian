/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointAllocationFloor

/-!
# Allocation tails paid at the local radial scale

The original allocated fraction decays up to prime share 591/1000.
Its slower rate is used only relative to the local signed-population
budget, without asserting source-normalized decay of this bound.
-/
namespace RiemannGaussian.ZetaRieszWideSixAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszBalancedCompanion ZetaRieszParityOrderTail

/-- A rationally certified pre-source allocation rate. -/
theorem allocation_log_rate :
    Real.log (99591/100000 : ℝ)+(13/32 : ℝ)*Real.log (100/99 : ℝ) ≤ -(1/100000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 409/199591)
    (by norm_num : (409/199591 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have he : Real.log (99591/100000 : ℝ) = -Real.log (100000/99591 : ℝ) := by
    rw [show (99591/100000 : ℝ) = (100000/99591)⁻¹ by norm_num,Real.log_inv]
  have hhi : Real.log (100/99 : ℝ) ≤ 12563/1250000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12563/1250000) 4
    norm_num [Finset.sum_range_succ] at hh
    linarith
  rw [he]
  linarith

/-- The original unpaid majority orders have exponentially small mass when the cofactor carries at least `409/1000` of the product logarithm. -/
theorem unpaid_mass_interior_le (N : ℕ) {x : ℝ} (hx : (409/1000:ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N:ℝ)/100000) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (100/99:ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0:ℝ) ≤ 99/100)
    (Real.exp_pos ((13/32:ℝ)*N*Real.log (100/99:ℝ))).le ?_
  · have hb : ((99/100:ℝ)*x+(1-x))^(N+1) ≤ (99591/100000:ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32:ℝ)*N*Real.log (100/99:ℝ)) * (99591/100000:ℝ)^(N+1) =
        (99591/100000:ℝ)*Real.exp ((N:ℝ)*(Real.log (99591/100000:ℝ)+(13/32:ℝ)*Real.log (100/99:ℝ))) := by
      rw [pow_succ]
      have hp : (99591/100000:ℝ)^N = Real.exp ((N:ℝ)*Real.log (99591/100000:ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<99591/100000)]
      rw [hp]
      rw [show (N:ℝ)*(Real.log (99591/100000:ℝ)+(13/32:ℝ)*Real.log (100/99:ℝ)) =
        (13/32:ℝ)*N*Real.log (100/99:ℝ)+(N:ℝ)*Real.log (99591/100000:ℝ) by ring, Real.exp_add]
      ring
    have hrate : Real.exp ((N:ℝ)*(Real.log (99591/100000:ℝ)+(13/32:ℝ)*Real.log (100/99:ℝ))) ≤
        Real.exp (-(N:ℝ)/100000) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left allocation_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32:ℝ)*N*Real.log (100/99:ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N:ℝ)/100000)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k:ℝ) ≤ (13/32:ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32:ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (99/100:ℝ) = Real.exp (-Real.log (100/99:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<100/99)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- If all eligible selected primes are balanced, the complete assigned fraction has an exponential saving with its exact prime-count factor. -/
theorem share_small_of_selected_primes_interior (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ (591/1000:ℝ)*Real.log n) :
    allocationShare A N n ≤ (n.primeFactors.card:ℝ)*Real.exp (-(N:ℝ)/100000) := by
  rw [share_eq_binomial_sum A N hn hn1]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N:ℝ)/100000) := by
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

/-- The exact six-prime allocated fraction has geometric relative
saving for every finite eligible prime set. -/
theorem boundedShare_six_le (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ (591/1000 : ℝ)*Real.log n) :
    boundedShare A N n ≤ 6*Real.exp (-(N : ℝ)/100000) := by
  have hn1 : 1 < n := by
    have hn0 := hs.ne_zero
    have hne : n ≠ 1 := by intro h; simp [h] at hc
    omega
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  rw [boundedShare,if_pos ⟨hs,hn1,hnp⟩]
  simpa only [hc,Nat.cast_ofNat] using
    share_small_of_selected_primes_interior A N hs hn1 (fun p hp _ _ => hmax p hp)

/-- This allowance vanishes before source scaling; no envelope requiring
it to beat log(2u) is introduced. -/
theorem tendsto_allocation_factor :
    Tendsto (fun N : ℕ => 6*Real.exp (-(N : ℝ)/100000)) atTop (𝓝 0) := by
  have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 1/100000)
  have ht := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hh)
  simpa only [Function.comp_def,mul_zero,neg_mul,div_mul_eq_mul_div,one_mul,neg_div]
    using ht.const_mul 6

end
end RiemannGaussian.ZetaRieszWideSixAllocation
