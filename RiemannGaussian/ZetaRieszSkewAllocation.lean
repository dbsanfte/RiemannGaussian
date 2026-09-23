/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWideOwnerAudit

/-!
# The proposed skew box overlaps the old factorial allocation

The concrete box forces the largest-prime order above 121N/200. Its
binomial tail and the old missing allocation must be estimated together.
Their product is at most 3 exp(-N/8100), including the narrow overlap
where neither factor alone supplies the required source-scale saving.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit

/-- The largest-prime order forced by the requested quarter-gap box. -/
def highOrders (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 2)).filter (fun j => 121 * N ≤ 200 * j)

/-- The complete largest-prime marginal containing the proposed box.
The argument is its complementary logarithmic share. -/
def highMass (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ highOrders N, mass (N + 1) j (1 - x)

theorem highMass_bounds (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ highMass N x ∧ highMass N x ≤ 1 := by
  have hm := fun j => mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x)
    (by linarith : 1 - x ≤ 1)
  refine ⟨Finset.sum_nonneg (fun j _ => hm j), ?_⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun j _ _ => hm j)).trans_eq (mass_total _ _)

/-- A fixed rational tilt, before using any prime-phase information. -/
theorem highMass_tilt (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    highMass N x ≤ Real.exp (-(121 / 200 : ℝ) * N * Real.log (41 / 40)) *
      ((41 / 40 : ℝ) * (1 - x) + x) ^ (N + 1) := by
  let B := Real.exp (-(121 / 200 : ℝ) * N * Real.log (41 / 40))
  have ht : 0 ≤ Real.log (41 / 40 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := fun j => mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x)
    (by linarith : 1 - x ≤ 1)
  have hb (j : ℕ) (hj : j ∈ highOrders N) : 1 ≤ B * (41 / 40 : ℝ) ^ j := by
    have hc : (121 / 200 : ℝ) * N ≤ j := by
      have h : 121 * (N : ℝ) ≤ 200 * j := by
        exact_mod_cast (Finset.mem_filter.mp hj).2
      linarith
    dsimp [B]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  calc
    highMass N x ≤ ∑ j ∈ highOrders N, B * (41 / 40 : ℝ) ^ j *
        mass (N + 1) j (1 - x) :=
      Finset.sum_le_sum (fun j hj => by nlinarith [mul_le_mul_of_nonneg_right (hb j hj) (hm j)])
    _ ≤ ∑ j ∈ Finset.range (N + 2), B * (41 / 40 : ℝ) ^ j *
        mass (N + 1) j (1 - x) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => mul_nonneg (by dsimp [B]; positivity) (hm j))
    _ = _ := by
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [mass_tilt]
      simp only [sub_sub_cancel, B, mul_assoc]

/-- The joint-tail exponent is strictly stronger than the source growth.
Only exact rational exponential/logarithmic enclosures are used. -/
theorem joint_log_rate :
    2 * Real.log (81 / 80 : ℝ) - (809 / 800 : ℝ) * Real.log (41 / 40) ≤
      -(1 / 8100) := by
  have hlo : (24692 / 1000000 : ℝ) ≤ Real.log (41 / 40) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 81)
      (by norm_num : (1 / 81 : ℝ) < 1) 2
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : Real.log (81 / 80 : ℝ) ≤ 12423 / 1000000 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 81 / 80)).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 12423 / 1000000) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  linarith

/-- The two distinct factorial allocations cannot both have substantial
mass in the proposed skew sector. No log-share hard cutoff is imposed. -/
theorem missing_mul_highMass (N : ℕ) (hN : 320 ≤ N) {x : ℝ}
    (hx : (7 / 20 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) *
      highMass N x ≤ 3 * Real.exp (-(N : ℝ) / 8100) := by
  have hx0 : 0 ≤ x := by linarith
  let H := Real.exp (-(13 / 32 : ℝ) * N * Real.log (41 / 40))
  let J := Real.exp (-(121 / 200 : ℝ) * N * Real.log (41 / 40))
  let B := Real.exp (((N : ℝ) / 5 + 1) * Real.log (5 / 4))
  let a := (41 / 40 : ℝ) * x + (1 - x)
  let b := (41 / 40 : ℝ) * (1 - x) + x
  let c := (4 / 5 : ℝ) * x + (1 - x)
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hh : 0 ≤ H := (Real.exp_pos _).le
  have hj : 0 ≤ J := (Real.exp_pos _).le
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have ht : 0 ≤ Real.log (41 / 40 : ℝ) := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (5 / 4 : ℝ) := Real.log_nonneg (by norm_num)
  have hmiss := missed_mass_bound N hN hx0 hx1 hh hB
    (by norm_num : (0 : ℝ) ≤ 41 / 40) (by norm_num : (0 : ℝ) ≤ 4 / 5) ?_ ?_
  · have hcap := highMass_tilt N hx0 hx1
    have hbounds := highMass_bounds N hx0 hx1
    have hab : a * b ≤ (81 / 80 : ℝ) ^ 2 := by
      dsimp [a, b]
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hc' : c ≤ (93 / 100 : ℝ) := by dsimp [c]; linarith
    have hraw :
        (1 - ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N + 1) k x) *
          highMass N x ≤ H * J * ((81 / 80 : ℝ) ^ 2) ^ (N + 1) +
            B * (93 / 100 : ℝ) ^ (N + 1) := by
      calc
        _ ≤ (H * a ^ (N + 1) + B * c ^ (N + 1)) * highMass N x :=
          mul_le_mul_of_nonneg_right hmiss hbounds.1
        _ ≤ H * a ^ (N + 1) * (J * b ^ (N + 1)) + B * c ^ (N + 1) := by
          dsimp only [J, b] at hcap ⊢
          nlinarith [mul_le_mul_of_nonneg_left hcap (mul_nonneg hh (pow_nonneg ha (N + 1))),
            mul_le_mul_of_nonneg_left hbounds.2 (mul_nonneg hB (pow_nonneg hc (N + 1)))]
        _ = H * J * (a * b) ^ (N + 1) + B * c ^ (N + 1) := by rw [mul_pow]; ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg ha hb) hab _) (mul_nonneg hh hj))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc hc' _) hB)
    have hu : H * J * ((81 / 80 : ℝ) ^ 2) ^ (N + 1) ≤
        (81 / 80 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 8100) := by
      have he : H * J * ((81 / 80 : ℝ) ^ 2) ^ (N + 1) =
          (81 / 80 : ℝ) ^ 2 * Real.exp ((N : ℝ) *
            (2 * Real.log (81 / 80) - (809 / 800) * Real.log (41 / 40))) := by
        have hpow : ((81 / 80 : ℝ) ^ 2) ^ N =
            Real.exp ((N : ℝ) * (2 * Real.log (81 / 80))) := by
          rw [show (2 : ℝ) * Real.log (81 / 80) = Real.log ((81 / 80 : ℝ) ^ 2) by
            rw [Real.log_pow]; norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        rw [pow_succ, hpow]
        calc
          _ = (81 / 80 : ℝ) ^ 2 * (H * J *
              Real.exp ((N : ℝ) * (2 * Real.log (81 / 80)))) := by ring
          _ = (81 / 80 : ℝ) ^ 2 * Real.exp
              (-(13 / 32 : ℝ) * N * Real.log (41 / 40) +
                -(121 / 200 : ℝ) * N * Real.log (41 / 40) +
                  N * (2 * Real.log (81 / 80))) := by
            rw [Real.exp_add, Real.exp_add]
          _ = _ := by congr 2; ring
      rw [he]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left joint_log_rate (Nat.cast_nonneg (α := ℝ) N)]
    have hlrate : Real.log (93 / 100 : ℝ) + (1 / 5 : ℝ) * Real.log (5 / 4) ≤ -(1 / 8100) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 93 / 100)
      linarith [log_tilt_bounds.2]
    have hlo : B * (93 / 100 : ℝ) ^ (N + 1) ≤
        (5 / 4 : ℝ) * (93 / 100) * Real.exp (-(N : ℝ) / 8100) := by
      have he : B * (93 / 100 : ℝ) ^ (N + 1) = (5 / 4 : ℝ) * (93 / 100) *
          Real.exp ((N : ℝ) * (Real.log (93 / 100) + (1 / 5) * Real.log (5 / 4))) := by
        dsimp [B]
        rw [pow_succ]
        rw [show ((N : ℝ) / 5 + 1) * Real.log (5 / 4) =
          Real.log (5 / 4) + (N : ℝ) / 5 * Real.log (5 / 4) by ring, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 5 / 4)]
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 93 / 100), ← Real.exp_nat_mul]
        simp only [Real.log_exp]
        rw [show (N : ℝ) * (Real.log (93 / 100) + (1 / 5) * Real.log (5 / 4)) =
          N * Real.log (93 / 100) + (N : ℝ) / 5 * Real.log (5 / 4) by ring, Real.exp_add]
        ring
      rw [he]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hlrate (Nat.cast_nonneg (α := ℝ) N)]
    nlinarith [Real.exp_pos (-(N : ℝ) / 8100)]
  · intro k _ hk
    have hc : (13 / 32 : ℝ) * N ≤ k := by
      have hi : 13 * N < 32 * k := by omega
      have hir : 13 * (N : ℝ) < 32 * k := by exact_mod_cast hi
      linarith
    dsimp [H]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40),
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    simp only [Real.log_exp]
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  · intro k _ hk
    have hc : (k : ℝ) ≤ (N : ℝ) / 5 + 1 := by
      have hi : 5 * k ≤ N + 5 := by omega
      have hir : 5 * (k : ℝ) ≤ N + 5 := by exact_mod_cast hi
      linarith
    have he : (4 / 5 : ℝ) = Real.exp (-Real.log (5 / 4 : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    dsimp [B]
    rw [he, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hl]

/-- The joint binomial saving survives the exact requested radius and a
summable arithmetic exponent; no zero hypothesis is needed. -/
def skewRate : ℝ :=
  radiusCeiling * (131071 / 262144 : ℝ)⁻¹ * Real.exp (-(1 / 8100 : ℝ))

theorem skewRate_bounds : 0 ≤ skewRate ∧ skewRate < 1 := by
  constructor
  · unfold skewRate radiusCeiling; positivity
  · rw [skewRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1 / 8100 : ℝ)
    norm_num [radiusCeiling] at h ⊢
    linarith

end
end RiemannGaussian.ZetaRieszSkewAllocation
