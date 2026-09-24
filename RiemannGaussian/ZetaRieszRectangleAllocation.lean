/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangle

/-!
# The old allocated part of the concrete rectangle is exponentially small

The two selections are bounded jointly, uniformly in the prime-log share.
Every old prime incidence is retained, including the two nonowner incidences.
The saving is stronger than the source growth at u = 10001/20000.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszBalancedCompanion
open ZetaRieszPrimeEndpoint

private theorem small_order_tilt (N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (N + 2)) {a x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hcut : ∀ k ∈ S, (k : ℝ) ≤ a * N) :
    (∑ k ∈ S, mass (N + 1) k x) ≤
      Real.exp (a * N * Real.log (25 / 24)) * ((24 / 25 : ℝ) * x + (1 - x)) ^ (N + 1) := by
  apply selected_tilt_bound (N + 1) S hS hx hx1 (by norm_num) (Real.exp_pos _).le
  intro k hk
  have ht : 0 ≤ Real.log (25 / 24 : ℝ) := Real.log_nonneg (by norm_num)
  have he : (24 / 25 : ℝ) = Real.exp (-Real.log (25 / 24 : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.one_le_exp_iff.mpr
  nlinarith [mul_le_mul_of_nonneg_right (hcut k hk) ht]

/-- Exact rational enclosures for the joint lower-tail rate. -/
theorem rectangle_allocation_log_rate :
    2 * Real.log (49 / 50 : ℝ) + (157 / 160 : ℝ) * Real.log (25 / 24) ≤ -(1 / 3200) := by
  have hlo : (20202 / 1000000 : ℝ) ≤ Real.log (50 / 49) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 99)
      (by norm_num : (1 / 99 : ℝ) < 1) 2
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : Real.log (25 / 24 : ℝ) ≤ 40823 / 1000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 40823 / 1000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he : Real.log (49 / 50 : ℝ) = -Real.log (50 / 49) := by
    rw [show (49 / 50 : ℝ) = (50 / 49)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  linarith

/-- The old allocation at any prime no larger than the owner has an
exponentially small joint overlap with the rectangle's largest-prime order. -/
theorem unpaid_mul_rectangleMarginal (N : ℕ) {x z : ℝ}
    (hx : 0 ≤ x) (hxz : x ≤ z) (hz : z ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k z) *
      rectangleMarginal N x ≤ Real.exp (-(N : ℝ) / 3200) := by
  have hx1 : x ≤ 1 := hxz.trans hz
  have hz0 : 0 ≤ z := hx.trans hxz
  have hU : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N + 2) := by
    intro k hk
    have := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have halloc := small_order_tilt N _ hU hz0 hz (a := 13 / 32) (by
    intro k hk
    have hn : 32 * k ≤ 13 * N := by
      have := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
      omega
    have hr : 32 * (k : ℝ) ≤ 13 * N := by exact_mod_cast hn
    linarith)
  have hrect := small_order_tilt N _ (Finset.filter_subset _ _)
    (by linarith : 0 ≤ 1 - x) (by linarith : 1 - x ≤ 1) (a := 23 / 40) (by
      intro j hj
      have hr : 40 * (j : ℝ) ≤ 23 * N := by exact_mod_cast (Finset.mem_filter.mp hj).2
      linarith)
  change rectangleMarginal N x ≤ _ at hrect
  simp only [sub_sub_cancel] at hrect
  let a : ℝ := (24 / 25) * z + (1 - z)
  let b : ℝ := (24 / 25) * (1 - x) + x
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a * b ≤ (49 / 50 : ℝ) ^ 2 := by
    have hh : a ≤ (24 / 25 : ℝ) * x + (1 - x) := by dsimp [a]; linarith
    have hm := mul_le_mul_of_nonneg_right hh hb
    dsimp [b] at hm ⊢
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hraw : (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k z) *
      rectangleMarginal N x ≤ Real.exp ((13 / 32 : ℝ) * N * Real.log (25 / 24)) *
      Real.exp ((23 / 40 : ℝ) * N * Real.log (25 / 24)) *
        ((49 / 50 : ℝ) ^ 2) ^ (N + 1) := by
    calc
      _ ≤ (Real.exp ((13 / 32 : ℝ) * N * Real.log (25 / 24)) * a ^ (N + 1)) *
          (Real.exp ((23 / 40 : ℝ) * N * Real.log (25 / 24)) * b ^ (N + 1)) := by
        exact mul_le_mul halloc hrect (rectangleMarginal_bounds N hx hx1).1
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg ha _))
      _ = Real.exp ((13 / 32 : ℝ) * N * Real.log (25 / 24)) *
          Real.exp ((23 / 40 : ℝ) * N * Real.log (25 / 24)) * (a * b) ^ (N + 1) := by
        rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg ha hb) hab _) (by positivity)
  have he : Real.exp ((13 / 32 : ℝ) * N * Real.log (25 / 24)) *
      Real.exp ((23 / 40 : ℝ) * N * Real.log (25 / 24)) *
        ((49 / 50 : ℝ) ^ 2) ^ (N + 1) =
      (49 / 50 : ℝ) ^ 2 * Real.exp ((N : ℝ) *
        (2 * Real.log (49 / 50) + (157 / 160) * Real.log (25 / 24))) := by
    have hp : ((49 / 50 : ℝ) ^ 2) ^ N =
        Real.exp ((N : ℝ) * (2 * Real.log (49 / 50))) := by
      rw [show (2 : ℝ) * Real.log (49 / 50) = Real.log ((49 / 50 : ℝ) ^ 2) by
        rw [Real.log_pow]; norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [pow_succ, hp]
    calc
      _ = (49 / 50 : ℝ) ^ 2 *
          (Real.exp ((13 / 32 : ℝ) * N * Real.log (25 / 24)) *
            Real.exp ((23 / 40 : ℝ) * N * Real.log (25 / 24)) *
              Real.exp ((N : ℝ) * (2 * Real.log (49 / 50)))) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  rw [he] at hraw
  have hr := Real.exp_le_exp.mpr
    (show (N : ℝ) * (2 * Real.log (49 / 50) + (157 / 160) * Real.log (25 / 24)) ≤
      -(N : ℝ) / 3200 by
      nlinarith [mul_le_mul_of_nonneg_left rectangle_allocation_log_rate
        (Nat.cast_nonneg (α := ℝ) N)])
  nlinarith [Real.exp_pos (-(N : ℝ) / 3200)]

/-- The complete old allocated fraction, not only the owner's incidence,
has joint exponential decay on the actual squarefree triple. -/
theorem boundedShare_mul_rectangleMass (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 3) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    boundedShare A N n *
      rectangleMass N (Real.log (n / largestPrime n : ℕ) / Real.log n) c ≤
        3 * Real.exp (-(N : ℝ) / 3200) := by
  have hp := largestPrime_mem_of_three hc
  have hn1 : 1 < n := (Nat.prime_of_mem_primeFactors hp).one_lt.trans_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) (Nat.dvd_of_mem_primeFactors hp))
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hx : 0 ≤ Real.log (n / largestPrime n : ℕ) / Real.log n :=
    div_nonneg (Real.log_natCast_nonneg _) hln.le
  have howner : Real.log (n / largestPrime n : ℕ) = Real.log n - Real.log (largestPrime n) := by
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp)
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero),
      Real.log_div (by exact_mod_cast hn.ne_zero)
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  have hx1 : Real.log (n / largestPrime n : ℕ) / Real.log n ≤ 1 := by
    apply (div_le_one hln).mpr
    rw [howner]
    linarith [Real.log_natCast_nonneg (largestPrime n)]
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors, Finset.card_singleton] at hc; omega
  have hb := (rectangleMass_bounds N hx hx1 hc0 hc1).2
  apply (mul_le_mul_of_nonneg_left hb (boundedShare_bounds A N n).1).trans
  rw [boundedShare, if_pos ⟨hn, hn1, hnp⟩, share_eq_binomial_sum A N hn hn1,
    Finset.sum_mul]
  have hs : (∑ p ∈ n.primeFactors,
      (if p ∈ A ∧ eligibleCofactor p (n / p) then
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N + 1) k (Real.log (n / p : ℕ) / Real.log n) else 0) *
            rectangleMarginal N (Real.log (n / largestPrime n : ℕ) / Real.log n)) ≤
      ∑ _p ∈ n.primeFactors, Real.exp (-(N : ℝ) / 3200) := by
    apply Finset.sum_le_sum
    intro p hp'
    split_ifs
    · have hpp := Nat.prime_of_mem_primeFactors hp'
      have hpd := Nat.dvd_of_mem_primeFactors hp'
      have hlogs : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
        rw [Nat.cast_div hpd (by exact_mod_cast hpp.ne_zero),
          Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
      have hmax : p ≤ largestPrime n := by
        rw [largestPrime, dif_pos (show n.primeFactors.Nonempty from ⟨p, hp'⟩)]
        exact Finset.le_max' _ _ hp'
      have hl : Real.log (p : ℝ) ≤ Real.log (largestPrime n) :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hmax)
      apply unpaid_mul_rectangleMarginal N hx
      · apply div_le_div_of_nonneg_right _ hln.le
        rw [hlogs, howner]
        linarith
      · apply (div_le_one hln).mpr
        rw [hlogs]
        linarith [Real.log_natCast_nonneg p]
    · simpa only [zero_mul] using (Real.exp_pos (-(N : ℝ) / 3200)).le
  simpa only [Finset.sum_const, hc, nsmul_eq_mul, Nat.cast_ofNat] using hs

/-- The source-normalized geometric ratio for this allocated error. -/
def rectangleAllocationRate : ℝ :=
  radiusCeiling * (131071 / 262144 : ℝ)⁻¹ * Real.exp (-(1 / 3200 : ℝ))

theorem rectangleAllocationRate_bounds :
    0 ≤ rectangleAllocationRate ∧ rectangleAllocationRate < 1 := by
  constructor
  · unfold rectangleAllocationRate radiusCeiling; positivity
  · rw [rectangleAllocationRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1 / 3200 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

end
end RiemannGaussian.ZetaRieszSkewAllocation
