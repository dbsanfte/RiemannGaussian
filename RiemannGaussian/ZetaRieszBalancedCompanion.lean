/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCancellingSector

/-!
# The balanced companion is independently small

The exact binomial allocations give exp(-N/64) per eligible balanced selected prime. The full finite sum has a height-uniform geometric source-scale allowance; the original balanced carrier is not asserted small.
-/

namespace RiemannGaussian.ZetaRieszBalancedCompanion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency

/-- A selected binomial allocation has the exact finite exponential-moment bound. -/
theorem selected_tilt_bound (M : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (M+1))
    {x q B : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hq : 0 ≤ q) (hB0 : 0 ≤ B)
    (hB : ∀ k ∈ S, 1 ≤ B * q^k) :
    (∑ k ∈ S, mass M k x) ≤ B * (q*x + (1-x))^M := by
  calc
    _ ≤ ∑ k ∈ S, B * (q^k * mass M k x) := by
      apply Finset.sum_le_sum
      intro k hk
      nlinarith [mul_le_mul_of_nonneg_right (hB k hk) (mass_nonneg M k hx hx1)]
    _ ≤ ∑ k ∈ Finset.range (M+1), B * (q^k * mass M k x) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun k _ _ => by
        exact mul_nonneg hB0 (mul_nonneg (pow_nonneg hq k) (mass_nonneg M k hx hx1)))
    _ = _ := by rw [← Finset.mul_sum, mass_tilt]

/-- Exact logarithmic inequalities certify the decay rate of an unpaid majority allocation at a balanced selected prime. -/
theorem balanced_log_rate : Real.log (5/6:ℝ)+(13/32:ℝ)*Real.log (3/2:ℝ) ≤ -(1/64:ℝ) := by
  have h6 : Real.log (6:ℝ) = Real.log 3 + Real.log 2 := by
    rw [show (6:ℝ)=3*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (6:ℝ) ≠ 0),
    Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0), h6]
  linarith [Real.log_five_lt_d9, Real.log_three_gt_d9, Real.log_two_gt_d9]

/-- The original unpaid majority orders have exponentially small mass when the cofactor carries at least half the product logarithm. -/
theorem unpaid_mass_balanced_le (N : ℕ) {x : ℝ} (hx : (1/2:ℝ) ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(N:ℝ)/64) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (3/2:ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hh := selected_tilt_bound (N+1) _ hUS hx0 hx1
    (by norm_num : (0:ℝ) ≤ 2/3)
    (Real.exp_pos ((13/32:ℝ)*N*Real.log (3/2:ℝ))).le ?_
  · have hb : ((2/3:ℝ)*x+(1-x))^(N+1) ≤ (5/6:ℝ)^(N+1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have he : Real.exp ((13/32:ℝ)*N*Real.log (3/2:ℝ)) * (5/6:ℝ)^(N+1) =
        (5/6:ℝ)*Real.exp ((N:ℝ)*(Real.log (5/6:ℝ)+(13/32:ℝ)*Real.log (3/2:ℝ))) := by
      rw [pow_succ]
      have hp : (5/6:ℝ)^N = Real.exp ((N:ℝ)*Real.log (5/6:ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<5/6)]
      rw [hp]
      rw [show (N:ℝ)*(Real.log (5/6:ℝ)+(13/32:ℝ)*Real.log (3/2:ℝ)) =
        (13/32:ℝ)*N*Real.log (3/2:ℝ)+(N:ℝ)*Real.log (5/6:ℝ) by ring, Real.exp_add]
      ring
    have hrate : Real.exp ((N:ℝ)*(Real.log (5/6:ℝ)+(13/32:ℝ)*Real.log (3/2:ℝ))) ≤
        Real.exp (-(N:ℝ)/64) := Real.exp_le_exp.mpr (by
      nlinarith [mul_le_mul_of_nonneg_left balanced_log_rate (Nat.cast_nonneg (α:=ℝ) N)])
    have hprod := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos ((13/32:ℝ)*N*Real.log (3/2:ℝ))).le
    rw [he] at hprod
    nlinarith [Real.exp_pos (-(N:ℝ)/64)]
  · intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k:ℝ) ≤ (13/32:ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32:ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (2/3:ℝ) = Real.exp (-Real.log (3/2:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<3/2)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- The companion fraction is exactly the sum of its eligible prime binomial allocations, retaining every incidence. -/
theorem share_eq_binomial_sum (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) :
    allocationShare A N n = ∑ p ∈ n.primeFactors,
      if p ∈ A ∧ eligibleCofactor p (n/p) then
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N+1) k (Real.log (n/p:ℕ)/Real.log n) else 0 := by
  rw [allocationShare, assignedAmplitude, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hlog : Real.log (n/p:ℕ) + Real.log p = Real.log n := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero), Real.log_div
      (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    ring
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  by_cases hel : p ∈ A ∧ eligibleCofactor p (n/p)
  · simp only [if_pos hel, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ N+1 := by have := unpaid_orders_submajority N k hk; omega
    have h := mass_as_factorials (N+1) k hkM (Real.log (n/p:ℕ)) (Real.log p)
      (by rw [hlog]; exact hln.ne')
    simpa only [hlog] using h.symm
  · simp [hel]

/-- If all eligible selected primes are balanced, the complete assigned fraction has an exponential saving with its exact prime-count factor. -/
theorem share_small_of_selected_primes_balanced (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n / 2) :
    allocationShare A N n ≤ (n.primeFactors.card:ℝ)*Real.exp (-(N:ℝ)/64) := by
  rw [share_eq_binomial_sum A N hn hn1]
  calc
    _ ≤ ∑ _p ∈ n.primeFactors, Real.exp (-(N:ℝ)/64) := by
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
        apply unpaid_mass_balanced_le
        · apply (le_div_iff₀ hln).mpr
          rw [hlog]
          linarith [hbal p hp hel.1 hel.2]
        · apply (div_le_one hln).mpr
          rw [hlog]
          linarith [Real.log_natCast_nonneg p]
      · rw [if_neg hel]
        exact (Real.exp_pos _).le
    _ = _ := by simp

/-- The complete reserve-range logarithmic window bounds the actual squarefree prime count by four times the moment order. -/
theorem card_le_four_order (N : ℕ) {n : ℕ} (hn : Squarefree n) (hnW : n ∈ literalWindow N) :
    (n.primeFactors.card:ℝ) ≤ 4*N := by
  have h := ZetaRieszExtremePrimeCount.prime_subset_log_budget hn n.primeFactors
    (Finset.Subset.refl _) (Real.log 2) (fun p hp =>
      Real.log_le_log (by norm_num) (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le))
  have hW := ((mem_literalWindow N n).mp hnW).2
  nlinarith [Real.log_two_gt_d9, Nat.cast_nonneg (α:=ℝ) n.primeFactors.card,
    Nat.cast_nonneg (α:=ℝ) N]


/-- The balanced companion coefficient has an independent exponential bound throughout the literal finite window. -/
theorem norm_assigned_balanced_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {n : ℕ}
    (hnW : n ∈ literalWindow N)
    (hbal : ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n / 2) :
    ‖assignedCoefficient A L N n‖ ≤
      (4*((N:ℝ)+1)*Real.exp (-(N:ℝ)/64))*zetaMoebiusLogMajorant n := by
  by_cases hn : Squarefree n ∧ 1<n ∧ ¬n.Prime
  · have hs := share_small_of_selected_primes_balanced A N hn.1 hn.2.1 hbal
    have hc := card_le_four_order N hn.1 hnW
    have hshare : allocationShare A N n ≤ 4*((N:ℝ)+1)*Real.exp (-(N:ℝ)/64) := by
      nlinarith [Real.exp_pos (-(N:ℝ)/64)]
    rw [assignedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (boundedShare_bounds A N n).1, boundedShare, if_pos hn]
    exact mul_le_mul hshare (SquarefreeVaughanLogSource.norm_coefficient_le hL n)
      (norm_nonneg _) (by positivity)
  · simp only [assignedCoefficient, boundedShare, if_neg hn, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (zetaMoebiusLogMajorant_nonneg n)

/-- The complete selected balanced companion sum has a uniform source-normalized geometric allowance, including its order factor. -/
theorem balanced_companion_bound (A D : Finset ℕ) {L : ℝ} (hL : 0<L) (N : ℕ)
    (hD : D ⊆ literalWindow N)
    (hbal : ∀ n ∈ D, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n/2)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    ‖(u:ℂ)^(N+1) * ∑ n ∈ D, assignedCoefficient A L N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*((N:ℝ)+1)/3) * (sectorRate^N *
        ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  let C : ℝ := 4*((N:ℝ)+1)/3
  have hC : 0<C := by dsimp [C]; positivity
  let a : ℕ → ℂ := fun n => assignedCoefficient A L N n / (C:ℂ)
  have ha : ∀ n ∈ D, ‖a n‖ ≤ 3*Real.exp (-(N:ℝ)/140)*zetaMoebiusLogMajorant n := by
    intro n hn
    have hb := norm_assigned_balanced_le A hL N (hD hn) (hbal n hn)
    have he : Real.exp (-(N:ℝ)/64) ≤ Real.exp (-(N:ℝ)/140) :=
      Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) N])
    have hb' : ‖assignedCoefficient A L N n‖ ≤
        (4*((N:ℝ)+1)*Real.exp (-(N:ℝ)/140))*zetaMoebiusLogMajorant n :=
      hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity))
        (zetaMoebiusLogMajorant_nonneg n))
    rw [show a n = assignedCoefficient A L N n/(C:ℂ) from rfl, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    apply (div_le_iff₀ hC).mpr
    exact hb'.trans_eq (by dsimp [C]; ring)
  have hb := normalized_sector_bound N D a ha y hu huU
  have hs : (u:ℂ)^(N+1) * (∑ n ∈ D, assignedCoefficient A L N n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      (C:ℂ)*((u:ℂ)^(N+1)*∑ n ∈ D, a n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [a]
    have hCc : (C:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    field_simp
  rw [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact mul_le_mul_of_nonneg_left hb hC.le

/-- Every changing balanced companion subband independently vanishes, with arbitrary heights, prime selections and positive lengths. -/
theorem tendsto_balanced_companion (A D : ℕ → Finset ℕ) (L y : ℕ → ℝ)
    (hL : ∀ N, 0<L N) (hD : ∀ N, D N ⊆ literalWindow N)
    (hbal : ∀ N n, n ∈ D N → ∀ p ∈ n.primeFactors, p ∈ A N → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n/2)
    {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    Tendsto (fun N => (u:ℂ)^(N+1) * ∑ n ∈ D N, assignedCoefficient (A N) (L N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y N) n) atTop (𝓝 0) := by
  have hr : 0 < sectorRate := by unfold sectorRate; positivity
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hr sectorRate_bounds.2).mul_const
    ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))
  simp only [pow_one, zero_mul] at ht
  apply squeeze_zero_norm (a := fun N : ℕ => ((N:ℝ)+1)*sectorRate^N *
    ((4/3:ℝ)*((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)))) ?_ ht
  intro N
  exact (balanced_companion_bound (A N) (D N) (hL N) N (hD N) (hbal N) (y N) hu huU).trans_eq (by ring)



end
end RiemannGaussian.ZetaRieszBalancedCompanion
