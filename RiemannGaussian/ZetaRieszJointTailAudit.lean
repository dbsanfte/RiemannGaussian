/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointRadialFloor
import RiemannGaussian.ZetaRieszAllowanceGrowth

/-!
# Exact central allocation tails

This audit uses the existing binomial allocation, not a new carrier. It
distinguishes growth of the actual scalar tails from failure of a chosen
upper envelope. It does not estimate the signed arithmetic core.
-/

namespace RiemannGaussian.ZetaRieszJointTailAudit
noncomputable section
open scoped BigOperators
open Filter Topology ZetaRieszJointAllocation

/-- Adjacent weights obey the exact binomial balance law. -/
theorem mass_balance (N j : ℕ) (hj : j < N) (p : ℝ) :
    ((j : ℝ)+1)*(1-p)*mass N (j+1) p =
      ((N : ℝ)-j)*p*mass N j p := by
  have hc : (N.choose (j+1) : ℝ)*((j : ℝ)+1) =
      (N.choose j : ℝ)*((N : ℝ)-j) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (le_of_lt hj)] using
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq N j)
  have hn : N-j = N-(j+1)+1 := by omega
  unfold mass
  rw [hn, pow_succ, pow_succ]
  linear_combination (p^j*(1-p)^(N-(j+1))*p*(1-p))*hc

/-- If the mean is an integer, its binomial atom is maximal. -/
theorem mass_le_at_mean {N k : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hk : k ≤ N) (hmean : (N : ℝ)*p = k) :
    ∀ j ≤ N, mass N j p ≤ mass N k p := by
  have hup : ∀ j < k, mass N j p ≤ mass N (j+1) p := by
    intro j hj
    have hjN : j < N := by omega
    have hb := mass_balance N j hjN p
    have hm := mass_nonneg N j hp.le hp1.le
    have hpos : 0 < ((j : ℝ)+1)*(1-p) := by positivity
    have hjR : (j : ℝ)+1 ≤ k := by exact_mod_cast hj
    have hcoef : ((j : ℝ)+1)*(1-p) ≤ ((N : ℝ)-j)*p := by nlinarith
    exact le_of_mul_le_mul_left
      (by nlinarith only [hb,mul_le_mul_of_nonneg_right hcoef hm]) hpos
  have hdown : ∀ j, k ≤ j → j < N → mass N (j+1) p ≤ mass N j p := by
    intro j hkj hjN
    have hb := mass_balance N j hjN p
    have hm := mass_nonneg N j hp.le hp1.le
    have hpos : 0 < ((j : ℝ)+1)*(1-p) := by positivity
    have hjR : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have hcoef : ((N : ℝ)-j)*p ≤ ((j : ℝ)+1)*(1-p) := by nlinarith
    exact le_of_mul_le_mul_left
      (by nlinarith only [hb,mul_le_mul_of_nonneg_right hcoef hm]) hpos
  intro j hj
  by_cases hjk : j ≤ k
  · have h : ∀ i ≤ k, mass N (k-i) p ≤ mass N k p := by
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
        have hi' : i ≤ k := by omega
        have hki : k-(i+1) < k := by omega
        have he : k-(i+1)+1 = k-i := by omega
        have hs : mass N (k-(i+1)) p ≤ mass N (k-i) p := by
          simpa only [he] using hup (k-(i+1)) hki
        exact hs.trans (ih hi')
    simpa only [Nat.sub_sub_self hjk] using h (k-j) (Nat.sub_le _ _)
  · have h : ∀ i, k+i ≤ N → mass N (k+i) p ≤ mass N k p := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        intro hi
        have hp' := hdown (k+i) (by omega) (by omega)
        exact hp'.trans (ih (by omega))
    have he : k+(j-k) = j := Nat.add_sub_of_le (by omega)
    simpa only [he] using h (j-k) (by omega)

/-- A modal atom carries at least the reciprocal of the number of atoms.
This elementary lower bound keeps the correct exponential rate. -/
theorem mean_mass_lower {N k : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hk : k ≤ N) (hmean : (N : ℝ)*p = k) :
    1/((N : ℝ)+1) ≤ mass N k p := by
  have ht := mass_total N p
  have hs : ∑ j ∈ Finset.range (N+1), mass N j p ≤
      ∑ _j ∈ Finset.range (N+1), mass N k p := by
    apply Finset.sum_le_sum
    intro j hj
    exact mass_le_at_mean hp hp1 hk hmean j (by simpa using Finset.mem_range.mp hj)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hs
  rw [ht] at hs
  exact (div_le_iff₀ (by positivity : 0 < (N : ℝ)+1)).mpr (by nlinarith)

/-- Changing the binomial parameter keeps its exact likelihood ratio. -/
theorem mass_change_parameter (N k : ℕ) {p : ℝ} (hp : p ≠ 0)
    (hp1 : 1-p ≠ 0) (x : ℝ) :
    mass N k x = mass N k p * (x/p)^k * ((1-x)/(1-p))^(N-k) := by
  unfold mass
  rw [div_pow,div_pow]
  field_simp

/-- A lower bound at the exact upper unpaid-order endpoint, with its
true exponential rate and only a polynomial prefactor. -/
theorem endpoint_mass_lower (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ((x/(13/32 : ℝ))^13*((1-x)/(19/32 : ℝ))^19)^m / (32*(m : ℝ)+1) ≤
      mass (32*m) (13*m) x := by
  have hp : 0 < (13/32 : ℝ) := by norm_num
  have hp1 : (13/32 : ℝ) < 1 := by norm_num
  have hm := mean_mass_lower hp hp1 (show 13*m ≤ 32*m by omega)
    (show ((32*m : ℕ) : ℝ)*(13/32) = (13*m : ℕ) by push_cast; ring)
  have he : 32*m-13*m = 19*m := by omega
  have hb : 0 ≤ ((x/(13/32 : ℝ))^13*((1-x)/(19/32 : ℝ))^19)^m := by positivity
  have h := mul_le_mul_of_nonneg_right hm hb
  rw [mass_change_parameter (32*m) (13*m) hp.ne' (by norm_num) x]
  norm_num only [show (1-(13/32 : ℝ)) = 19/32 by norm_num] at *
  rw [he,pow_mul,pow_mul]
  simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,div_eq_mul_inv,one_mul,
    mul_assoc,mul_comm,mul_left_comm] using h

/-- Adding one trial leaves at least its failure multiple of the old atom. -/
theorem mass_succ_same_lower {N k : ℕ} (hk : k ≤ N) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (1-x)*mass N k x ≤ mass (N+1) k x := by
  have hn : N+1-k = (N-k)+1 := by omega
  have hc : (N.choose k : ℝ) ≤ ((N+1).choose k : ℝ) := by
    exact_mod_cast Nat.choose_le_succ N k
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ x^k*(1-x)^(N-k)*(1-x) by positivity)
  unfold mass
  rw [hn,pow_succ]
  nlinarith only [hh]

/-- Adding one trial leaves at least its success multiple at the next atom. -/
theorem mass_succ_next_lower (N k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x*mass N k x ≤ mass (N+1) (k+1) x := by
  have hc : (N.choose k : ℝ) ≤ ((N+1).choose (k+1) : ℝ) := by
    exact_mod_cast (show N.choose k ≤ (N+1).choose (k+1) by
      rw [Nat.choose_succ_succ']; omega)
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ x^k*x*(1-x)^(N-k) by positivity)
  unfold mass
  rw [Nat.add_sub_add_right,pow_succ]
  nlinarith only [hh]

/-- A single omitted atom is a lower bound for the actual missing mass. -/
theorem mass_le_missing {N k : ℕ} (hk : k < N+2)
    (hkU : k ∉ ZetaRieszWingHighOrders.unpaidOrders N) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    mass (N+1) k x ≤
      1-∑ j ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) j x := by
  let S := Finset.range (N+2)
  let U := ZetaRieszWingHighOrders.unpaidOrders N
  have hUS : U ⊆ S := by
    intro j hj
    have h := unpaid_orders_submajority N j hj
    simp only [S,Finset.mem_range]
    omega
  have ht : (∑ j ∈ S \ U, mass (N+1) j x) =
      1-∑ j ∈ U, mass (N+1) j x := by
    have h := Finset.sum_sdiff (f := fun j => mass (N+1) j x) hUS
    have hh : (∑ j ∈ S, mass (N+1) j x) = 1 := mass_total (N+1) x
    linarith
  rw [← ht]
  exact Finset.single_le_sum (fun j _ => mass_nonneg (N+1) j hx hx1)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hk,hkU⟩)

/-- Exact rational certification, without logarithmic enclosures: the
59% assigned-tail endpoint grows after the source scaling. -/
theorem assigned_endpoint_rate :
    (1001/1000 : ℝ) ≤ (10001/10000 : ℝ)^32 *
      ((41/100 : ℝ)/(13/32))^13*((59/100 : ℝ)/(19/32))^19 := by norm_num

/-- The corresponding 60% unassigned-tail endpoint also genuinely grows. -/
theorem missing_endpoint_rate :
    (2001/2000 : ℝ) ≤ (10001/10000 : ℝ)^32 *
      ((2/5 : ℝ)/(13/32))^13*((3/5 : ℝ)/(19/32))^19 := by norm_num

private theorem scaled_endpoint_lower (m : ℕ) {x b r : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hrate : r ≤ b^32*((x/(13/32))^13*((1-x)/(19/32))^19)) :
    r^m/(32*(m : ℝ)+1) ≤ b^(32*m)*mass (32*m) (13*m) x := by
  have hd : 0 < 32*(m : ℝ)+1 := by positivity
  have hpow := pow_le_pow_left₀ hr hrate m
  have h := mul_le_mul_of_nonneg_left (endpoint_mass_lower m hx hx1)
    (pow_nonneg hb (32*m))
  calc
    _ ≤ (b^32*((x/(13/32))^13*((1-x)/(19/32))^19))^m /
        (32*(m : ℝ)+1) := div_le_div_of_nonneg_right hpow hd.le
    _ = b^(32*m) *
        (((x/(13/32))^13*((1-x)/(19/32))^19)^m/(32*(m : ℝ)+1)) := by
      rw [mul_pow,pow_mul]
      ring
    _ ≤ _ := h

/-- At a 59% prime share, the actual unpaid-order mass cannot have a
vanishing source-scaled scalar allowance. This is a lower bound on the
literal binomial sum, not merely a failure of an exponential tilt. -/
theorem assigned_tail_lower (m : ℕ) (hm : 10 ≤ m) :
    (1001/1000 : ℝ)^m / (3*(32*(m : ℝ)+1)) ≤
      (10001/10000 : ℝ)^(32*m+1)*
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m),
          mass (32*m+1) k (41/100) := by
  have hk : 13*m ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m) := by
    apply (mem_unpaid_iff (by omega : 320 ≤ 32*m)).mpr
    constructor <;> omega
  have hs : mass (32*m+1) (13*m) (41/100) ≤
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m),
        mass (32*m+1) k (41/100) :=
    Finset.single_le_sum (fun k _ => mass_nonneg _ k (by norm_num) (by norm_num)) hk
  have hm1 := mass_succ_same_lower (show 13*m ≤ 32*m by omega)
    (by norm_num : (0 : ℝ) ≤ 41/100) (by norm_num : (41/100 : ℝ) ≤ 1)
  have he := scaled_endpoint_lower m (by norm_num : (0 : ℝ) ≤ 41/100)
    (by norm_num : (41/100 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 10001/10000)
    (by norm_num : (0 : ℝ) ≤ 1001/1000) (by
      convert assigned_endpoint_rate using 1; ring)
  have hp : 0 ≤ (10001/10000 : ℝ)^(32*m) := by positivity
  have h := mul_le_mul_of_nonneg_left (hm1.trans hs) hp
  have ht := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 10001/10000)
  have hnon : 0 ≤ (1001/1000 : ℝ)^m/(32*(m : ℝ)+1) := by positivity
  rw [pow_succ]
  have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤
    (10001/10000)*(1-41/100))
  rw [show (1001/1000 : ℝ)^m/(3*(32*(m : ℝ)+1)) =
    (1/3)*((1001/1000 : ℝ)^m/(32*(m : ℝ)+1)) by
      simp only [div_eq_mul_inv,mul_inv_rev]; ring]
  nlinarith only [ht,he',hnon]

/-- At a 60% prime share the actual unassigned mass has the same
obstruction, even though its eventual growth is slower. -/
theorem missing_tail_lower (m : ℕ) (hm : 10 ≤ m) :
    (2001/2000 : ℝ)^m / (3*(32*(m : ℝ)+1)) ≤
      (10001/10000 : ℝ)^(32*m+1)*
        (1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m),
          mass (32*m+1) k (2/5)) := by
  have hk : 13*m+1 ∉ ZetaRieszWingHighOrders.unpaidOrders (32*m) := by
    intro hk
    have h := (mem_unpaid_iff (by omega : 320 ≤ 32*m)).mp hk
    omega
  have hs := mass_le_missing (by omega : 13*m+1 < 32*m+2) hk
    (by norm_num : (0 : ℝ) ≤ 2/5) (by norm_num : (2/5 : ℝ) ≤ 1)
  have hm1 := mass_succ_next_lower (32*m) (13*m)
    (by norm_num : (0 : ℝ) ≤ 2/5) (by norm_num : (2/5 : ℝ) ≤ 1)
  have he := scaled_endpoint_lower m (by norm_num : (0 : ℝ) ≤ 2/5)
    (by norm_num : (2/5 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 10001/10000)
    (by norm_num : (0 : ℝ) ≤ 2001/2000) (by
      convert missing_endpoint_rate using 1; ring)
  have hp : 0 ≤ (10001/10000 : ℝ)^(32*m) := by positivity
  have h := mul_le_mul_of_nonneg_left (hm1.trans hs) hp
  have ht := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 10001/10000)
  have hnon : 0 ≤ (2001/2000 : ℝ)^m/(32*(m : ℝ)+1) := by positivity
  rw [pow_succ]
  have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤
    (10001/10000)*(2/5))
  rw [show (2001/2000 : ℝ)^m/(3*(32*(m : ℝ)+1)) =
    (1/3)*((2001/2000 : ℝ)^m/(32*(m : ℝ)+1)) by
      simp only [div_eq_mul_inv,mul_inv_rev]; ring]
  nlinarith only [ht,he',hnon]

private theorem growth_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun m : ℕ => r^m/(3*(32*(m : ℝ)+1))) atTop atTop := by
  have ht := (ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto hr).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1/96)
  apply tendsto_atTop_mono (fun m => ?_) ht
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hd : 3*(32*(m : ℝ)+1) ≤ 96*((m : ℝ)+1)^4 := by nlinarith [sq_nonneg (m : ℝ)]
  have hh := div_le_div_of_nonneg_left (pow_nonneg (by linarith : 0 ≤ r) m)
    (by positivity : 0 < 3*(32*(m : ℝ)+1)) hd
  convert hh using 1; simp only [div_eq_mul_inv,mul_inv_rev]; ring

/-- The exact assigned tail diverges under the source scaling at the
upper radius. In particular no fixed cofinal scalar allowance works. -/
theorem assigned_tail_tendsto_atTop :
    Tendsto (fun m : ℕ => (10001/10000 : ℝ)^(32*m+1)*
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m),
        mass (32*m+1) k (41/100)) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (growth_tendsto (by norm_num : (1 : ℝ) < 1001/1000))
  filter_upwards [eventually_ge_atTop 10] with m hm
  exact assigned_tail_lower m hm

/-- The exact missing tail diverges as well; this is not a numerical
conclusion drawn from an optimized Chernoff bound. -/
theorem missing_tail_tendsto_atTop :
    Tendsto (fun m : ℕ => (10001/10000 : ℝ)^(32*m+1)*
      (1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders (32*m),
        mass (32*m+1) k (2/5))) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (growth_tendsto (by norm_num : (1 : ℝ) < 2001/2000))
  filter_upwards [eventually_ge_atTop 10] with m hm
  exact missing_tail_lower m hm

private theorem dyadic_order_eq (j : ℕ) :
    ZetaRieszPrimeCountFrequency.dyadicMomentOrder j = 32*(2*(j+4)*2^j) := by
  simp only [ZetaRieszPrimeCountFrequency.dyadicMomentOrder,
    ZetaRieszPrimeCountFrequency.dyadicPrimeCount,pow_add]
  ring

private theorem dyadic_blocks_tendsto :
    Tendsto (fun j : ℕ => 2*(j+4)*2^j) atTop atTop := by
  apply tendsto_atTop_mono (fun j => ?_) tendsto_id
  change j ≤ 2*(j+4)*2^j
  have hp : 1 ≤ 2^j := Nat.one_le_pow j 2 (by norm_num)
  nlinarith

/-- The growth persists on the proof's original cofinal moment schedule.
This remains a scalar-tail theorem; it is not a signed prime-sum estimate. -/
theorem assigned_dyadic_tail_tendsto_atTop :
    Tendsto (fun j =>
      (2*ZetaRieszWideOwnerAudit.radiusCeiling)^
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
          mass (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1) k (41/100))
      atTop atTop := by
  have h := assigned_tail_tendsto_atTop.comp dyadic_blocks_tendsto
  simpa only [Function.comp_def,dyadic_order_eq,ZetaRieszWideOwnerAudit.radiusCeiling,
    show (2 : ℝ)*(10001/20000) = 10001/10000 by norm_num] using h

/-- The same exact obstruction holds for the missing mass on the
original moment schedule, including the integer unpaid-order endpoints. -/
theorem missing_dyadic_tail_tendsto_atTop :
    Tendsto (fun j =>
      (2*ZetaRieszWideOwnerAudit.radiusCeiling)^
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
        (1-∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j),
          mass (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1) k (2/5)))
      atTop atTop := by
  have h := missing_tail_tendsto_atTop.comp dyadic_blocks_tendsto
  simpa only [Function.comp_def,dyadic_order_eq,ZetaRieszWideOwnerAudit.radiusCeiling,
    show (2 : ℝ)*(10001/20000) = 10001/10000 by norm_num] using h

end
end RiemannGaussian.ZetaRieszJointTailAudit
