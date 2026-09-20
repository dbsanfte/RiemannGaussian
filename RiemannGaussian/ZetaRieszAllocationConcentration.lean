/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompanionWindow

/-!
# Binomial concentration of the actual derivative allocation

The exact unpaid-order interval captures all but 3 exp(-N/140) of the allocation when the eligible cofactor log fraction lies between 17/64 and 11/32. This yields an actual exponentially small finite coefficient with every original arithmetic mask retained.
-/

namespace RiemannGaussian.ZetaRieszJointAllocation
noncomputable section
open scoped BigOperators Classical

/-- The actual unpaid orders have exactly the two surviving integer endpoints after order 320. -/
theorem mem_unpaid_iff {N k : ℕ} (hN : 320 ≤ N) :
    k ∈ ZetaRieszWingHighOrders.unpaidOrders N ↔
      k ≤ 13 * N / 32 ∧ 5 * (N + 1 - k) < 4 * N := by
  constructor
  · intro hk
    exact (ZetaRieszWingHighOrders.unpaidOrders_support hk).2
  · intro hk
    simp only [ZetaRieszWingHighOrders.unpaidOrders, Finset.mem_sdiff,
      ZetaRieszReflectedCompletion.lowerWing, ZetaRieszPairOrders.middleOrders,
      Finset.mem_filter, Finset.mem_range, ZetaRieszWingReserve.reserveOrders,
      Finset.mem_Icc, ZetaRieszWingHighOrders.highOrders]
    omega

/-- A binomial allocation weight with the full complementary factorial order. -/
def mass (M k : ℕ) (x : ℝ) : ℝ :=
  x ^ k * (1-x) ^ (M-k) * (M.choose k : ℝ)

/-- Every allocation weight is nonnegative on the unit interval. -/
theorem mass_nonneg (M k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ mass M k x := by
  unfold mass
  positivity

/-- The complete derivative allocation has total mass one. -/
theorem mass_total (M : ℕ) (x : ℝ) : ∑ k ∈ Finset.range (M+1), mass M k x = 1 := by
  simp only [mass]
  rw [← add_pow]
  simp

/-- Exact exponential-tilt generating function for the derivative allocation. -/
theorem mass_tilt (M : ℕ) (x q : ℝ) :
    ∑ k ∈ Finset.range (M+1), q^k * mass M k x = (q*x + (1-x))^M := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mass, mul_pow]
  ring

/-- Both missing allocation tails are bounded together using their literal integer cuts. -/
theorem missed_mass_bound (N : ℕ) (hN : 320 ≤ N) {x Bh Bl qh ql : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hBh : 0 ≤ Bh) (hBl : 0 ≤ Bl)
    (hqh : 0 ≤ qh) (hql : 0 ≤ ql)
    (hhi : ∀ k ∈ Finset.range (N+2), 13*N/32 < k → 1 ≤ Bh * qh^k)
    (hlo : ∀ k ∈ Finset.range (N+2), 5*(N+1-k) ≥ 4*N → 1 ≤ Bl * ql^k) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Bh * (qh*x+(1-x))^(N+1) + Bl * (ql*x+(1-x))^(N+1) := by
  let U := ZetaRieszWingHighOrders.unpaidOrders N
  let S := Finset.range (N+2)
  have hUS : U ⊆ S := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [S, Finset.mem_range]
    omega
  have he : 1 - (∑ k ∈ U, mass (N+1) k x) = ∑ k ∈ S \ U, mass (N+1) k x := by
    have hs := Finset.sum_sdiff (f := fun k => mass (N+1) k x) hUS
    have ht := mass_total (N+1) x
    change _ + _ = ∑ k ∈ Finset.range (N+2), mass (N+1) k x at hs
    linarith
  rw [he]
  calc
    _ ≤ ∑ k ∈ S \ U, (Bh * qh^k + Bl * ql^k) * mass (N+1) k x := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hks, hkU⟩ := Finset.mem_sdiff.mp hk
      have hmass := mass_nonneg (N+1) k hx hx1
      have hp : 1 ≤ Bh * qh^k + Bl * ql^k := by
        by_cases h : 13*N/32 < k
        · have := hhi k hks h
          nlinarith [mul_nonneg hBl (pow_nonneg hql k)]
        · have hl : 5*(N+1-k) ≥ 4*N := by
            by_contra h'
            exact hkU ((mem_unpaid_iff hN).mpr ⟨by omega, by omega⟩)
          have := hlo k hks hl
          nlinarith [mul_nonneg hBh (pow_nonneg hqh k)]
      nlinarith [mul_le_mul_of_nonneg_right hp hmass]
    _ ≤ ∑ k ∈ S, (Bh * qh^k + Bl * ql^k) * mass (N+1) k x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun k _ _ =>
        mul_nonneg (add_nonneg (mul_nonneg hBh (pow_nonneg hqh k))
          (mul_nonneg hBl (pow_nonneg hql k))) (mass_nonneg (N+1) k hx hx1))
    _ = _ := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, S]
      rw [mass_tilt, mass_tilt]

/-- Exact rational enclosures for the logarithm used in both allocation tilts. -/
theorem log_tilt_bounds : (223 / 1000 : ℝ) ≤ Real.log (5/4:ℝ) ∧
    Real.log (5/4:ℝ) ≤ (224/1000:ℝ) := by
  have he : Real.log (5/4:ℝ) = Real.log 5 - 2*Real.log 2 := by
    rw [Real.log_div (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)]
    have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
  rw [he]
  constructor <;> linarith [Real.log_five_gt_d9, Real.log_five_lt_d9,
    Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The actual unpaid allocation misses at most two explicit binomial-tail allowances. -/
theorem missing_allocation_bound (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : (17/64:ℝ) ≤ x) (hx1 : x ≤ (11/32:ℝ)) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      Real.exp (-(13/32:ℝ)*N*Real.log (5/4:ℝ)) * (139/128:ℝ)^(N+1) +
      Real.exp (((N:ℝ)/5+1)*Real.log (5/4:ℝ)) * (303/320:ℝ)^(N+1) := by
  have hx0 : 0 ≤ x := by linarith
  have hxone : x ≤ 1 := by linarith
  have ht : 0 ≤ Real.log (5/4:ℝ) := by linarith [log_tilt_bounds.1]
  have h := missed_mass_bound N hN hx0 hxone
    (Real.exp_pos (-(13/32:ℝ)*N*Real.log (5/4:ℝ))).le
    (Real.exp_pos (((N:ℝ)/5+1)*Real.log (5/4:ℝ))).le
    (by norm_num : (0:ℝ) ≤ 5/4) (by norm_num : (0:ℝ) ≤ 4/5) ?_ ?_
  · apply h.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (by linarith : 0 ≤ 5/4*x+(1-x)) (by linarith) _
    · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (by linarith : 0 ≤ 4/5*x+(1-x)) (by linarith) _
  · intro k hk hcut
    have hc : (13/32:ℝ)*N ≤ k := by
      have hn : 13*N < 32*k := by omega
      have hnR : (13:ℝ)*N < 32*k := by exact_mod_cast hn
      linarith
    rw [← Real.exp_log (by norm_num : (0:ℝ)<5/4), ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k hk hcut
    have hkN : k ≤ N+1 := by have := Finset.mem_range.mp hk; omega
    have hc : (k:ℝ) ≤ (N:ℝ)/5+1 := by
      have hn : 5*k ≤ N+5 := by omega
      have hnR : (5:ℝ)*k ≤ N+5 := by exact_mod_cast hn
      linarith
    have he : (4/5:ℝ) = Real.exp (-Real.log (5/4:ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<5/4)]
      norm_num
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]

/-- An exact exponential-series certificate for the upper-tail scalar bound. -/
theorem upper_log_bound : Real.log (139/128:ℝ) ≤ (83/1000:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<139/128)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 83/1000) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Both missing allocation tails decay at rate exp(-N/140) on the stated cofactor-log sector. -/
theorem missing_allocation_exponential (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : (17/64:ℝ) ≤ x) (hx1 : x ≤ (11/32:ℝ)) :
    1 - (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k x) ≤
      3 * Real.exp (-(N:ℝ)/140) := by
  have hbhi : Real.log (139/128:ℝ) - (13/32:ℝ)*Real.log (5/4:ℝ) ≤ -(1/140:ℝ) := by
    linarith [upper_log_bound, log_tilt_bounds.1]
  have hblo : Real.log (303/320:ℝ) + (1/5:ℝ)*Real.log (5/4:ℝ) ≤ -(1/140:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<303/320)
    linarith [log_tilt_bounds.2]
  have hehi : Real.exp (-(13/32:ℝ)*N*Real.log (5/4:ℝ)) * (139/128:ℝ)^(N+1) =
      (139/128:ℝ) * Real.exp ((N:ℝ)*(Real.log (139/128:ℝ) - (13/32:ℝ)*Real.log (5/4:ℝ))) := by
    rw [pow_succ]
    have hp : (139/128:ℝ)^N = Real.exp ((N:ℝ)*Real.log (139/128:ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<139/128)]
    rw [hp]
    rw [show (N:ℝ)*(Real.log (139/128:ℝ) - (13/32:ℝ)*Real.log (5/4:ℝ)) =
      -(13/32:ℝ)*N*Real.log (5/4:ℝ)+(N:ℝ)*Real.log (139/128:ℝ) by ring, Real.exp_add]
    ring
  have helo : Real.exp (((N:ℝ)/5+1)*Real.log (5/4:ℝ)) * (303/320:ℝ)^(N+1) =
      (5/4:ℝ)*(303/320:ℝ) * Real.exp ((N:ℝ)*(Real.log (303/320:ℝ) + (1/5:ℝ)*Real.log (5/4:ℝ))) := by
    rw [pow_succ]
    have hp : (303/320:ℝ)^N = Real.exp ((N:ℝ)*Real.log (303/320:ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<303/320)]
    rw [hp]
    rw [show ((N:ℝ)/5+1)*Real.log (5/4:ℝ) =
      (N:ℝ)/5*Real.log (5/4:ℝ)+Real.log (5/4:ℝ) by ring, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ)<5/4)]
    rw [show (N:ℝ)*(Real.log (303/320:ℝ)+(1/5:ℝ)*Real.log (5/4:ℝ)) =
      (N:ℝ)/5*Real.log (5/4:ℝ)+(N:ℝ)*Real.log (303/320:ℝ) by ring, Real.exp_add]
    ring
  have hhi : Real.exp ((N:ℝ)*(Real.log (139/128:ℝ)-(13/32:ℝ)*Real.log (5/4:ℝ))) ≤
      Real.exp (-(N:ℝ)/140) := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) N])
  have hlo : Real.exp ((N:ℝ)*(Real.log (303/320:ℝ)+(1/5:ℝ)*Real.log (5/4:ℝ))) ≤
      Real.exp (-(N:ℝ)/140) := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) N])
  have h := missing_allocation_bound N hN hx hx1
  rw [hehi, helo] at h
  nlinarith [Real.exp_pos (-(N:ℝ)/140)]

/-- The normalized binomial mass equals the original complementary factorial weights exactly. -/
theorem mass_as_factorials (M k : ℕ) (hk : k ≤ M) (a b : ℝ) (hab : a+b ≠ 0) :
    mass M k (a/(a+b)) =
      (a^k / (k.factorial:ℝ) * (b^(M-k) / ((M-k).factorial:ℝ))) /
        ((a+b)^M / (M.factorial:ℝ)) := by
  have he : 1-a/(a+b) = b/(a+b) := by field_simp; ring
  rw [mass, he, div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hk,
    factorial_split _ _ _ _ hk, Nat.choose_symm hk]
  have hf : (M.factorial:ℝ) ≠ 0 := by positivity
  have hp : (a+b)^M ≠ 0 := pow_ne_zero M hab
  field_simp


/-- One eligible actual prime contributes its full binomial allocation to the companion share. -/
theorem single_prime_mass_le_share (A : Finset ℕ) (N : ℕ) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hp : p ∈ n.primeFactors)
    (hpA : p ∈ A) (hel : eligibleCofactor p (n/p)) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (Real.log (n/p:ℕ) / Real.log n)) ≤ allocationShare A N n := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hlog : Real.log (n/p:ℕ) + Real.log p = Real.log n := by
    rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero), Real.log_div
      (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    ring
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hbase : 0 < Real.log n ^ (N+1) / ((N+1).factorial:ℝ) := by positivity
  have he : (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (Real.log (n/p:ℕ) / Real.log n)) =
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      Real.log (n/p:ℕ)^k / (k.factorial:ℝ) *
        (Real.log p^(N+1-k) / ((N+1-k).factorial:ℝ))) /
      (Real.log n^(N+1) / ((N+1).factorial:ℝ)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k ≤ N+1 := by have := unpaid_orders_submajority N k hk; omega
    have h := mass_as_factorials (N+1) k hkM (Real.log (n/p:ℕ)) (Real.log p)
      (by rw [hlog]; exact hln.ne')
    simpa only [hlog] using h
  rw [he, allocationShare]
  apply div_le_div_of_nonneg_right _ hbase.le
  unfold assignedAmplitude
  have h := Finset.single_le_sum (f := fun q => ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      if q ∈ A ∧ eligibleCofactor q (n/q) then
      Real.log (n/q:ℕ)^k / (k.factorial:ℝ) *
        (Real.log q^(N+1-k) / ((N+1-k).factorial:ℝ)) else 0)
    (fun q _ => Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity)) hp
  simpa only [if_pos (show p ∈ A ∧ eligibleCofactor p (n/p) from ⟨hpA, hel⟩)] using h

/-- The original companion cancels all but an exponentially small fraction on the selected prime-log sector. -/
theorem allocation_missing_exponential (A : Finset ℕ) (N : ℕ) (hN : 320 ≤ N) {n p : ℕ}
    (hn : Squarefree n) (hn1 : 1 < n) (hp : p ∈ n.primeFactors)
    (hpA : p ∈ A) (hel : eligibleCofactor p (n/p))
    (hlo : (17/64:ℝ) ≤ Real.log (n/p:ℕ) / Real.log n)
    (hhi : Real.log (n/p:ℕ) / Real.log n ≤ (11/32:ℝ)) :
    0 ≤ 1-allocationShare A N n ∧
      1-allocationShare A N n ≤ 3 * Real.exp (-(N:ℝ)/140) := by
  have hs := single_prime_mass_le_share A N hn hn1 hp hpA hel
  have ht := missing_allocation_exponential N hN hlo hhi
  have hb := allocationShare_bounds A N hn hn1
  constructor <;> linarith

/-- The actual finite signed coefficient has an exponential saving on the retained selected-prime sector. -/
theorem finite_coefficient_sector_bound (u : ℝ) (N K : ℕ) (hN : 320 ≤ N) {n p : ℕ}
    (hnS : n ∈ LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K)
      (7/4) (9/4) N)
    (hn : Squarefree n) (hn1 : 1 < n) (hnp : ¬n.Prime) (hp : p ∈ n.primeFactors)
    (hpA : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (hel : eligibleCofactor p (n/p))
    (hlo : (17/64:ℝ) ≤ Real.log (n/p:ℕ) / Real.log n)
    (hhi : Real.log (n/p:ℕ) / Real.log n ≤ (11/32:ℝ)) :
    ‖finiteCoefficient u N K n‖ ≤
      3 * Real.exp (-(N:ℝ)/140) * zetaMoebiusLogMajorant n := by
  have hb := allocation_missing_exponential _ N hN hn hn1 hp hpA hel hlo hhi
  have he : finiteWeight u N K n =
      1-allocationShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n := by
    rw [finiteWeight, if_pos hnS, boundedShare, if_pos ⟨hn, hn1, hnp⟩]
  rw [finiteCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs, he, abs_of_nonneg hb.1]
  exact mul_le_mul hb.2
    (SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N) n)
    (norm_nonneg _) (by positivity)



end
end RiemannGaussian.ZetaRieszJointAllocation
