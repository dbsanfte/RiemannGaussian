/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordClosedDefect

/-!
# Ford's original coefficient scale

For omega = 0.06 the complete small-endpoint base fits the original
`W = k^(4.11*k)`. All logarithmic and exponential numerical enclosures
are checked from signed Taylor bounds and mathlib's bounds for log 2
and exp 1. No decimal computation supplies an analytic premise.
-/

namespace RiemannGaussian.VinogradovFordCoefficientScale
noncomputable section
open VinogradovFordPotential VinogradovFordTailThreshold

/-- A rational lower anchor for the logarithm at the original degree cutoff. -/
theorem log_thousand_ge : (13815 / 2000 : ℝ) ≤ Real.log 1000 := by
  have h₁ := log_le_cubic (by norm_num : (-1 : ℝ) < -(1 / 9))
  have h₂ := log_le_cubic (by norm_num : (-1 : ℝ) < -(1 / 10))
  norm_num at h₁ h₂
  have he : Real.log (1000 : ℝ) = 9 * Real.log 2 -
      3 * (Real.log (8 / 9) + Real.log (9 / 10)) := by
    rw [← Real.log_mul (by norm_num : (8 / 9 : ℝ) ≠ 0) (by norm_num : (9 / 10 : ℝ) ≠ 0)]
    rw [show (8 / 9 : ℝ) * (9 / 10) = 4 / 5 by norm_num]
    rw [show (1000 : ℝ) = 2 ^ 9 / (4 / 5) ^ 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

/-- The signed cubic bound supplies the required upper logarithm of 300. -/
theorem log_three_hundred_le : Real.log (300 : ℝ) ≤ 713 / 125 := by
  have hh := log_le_cubic (by norm_num : (-1 : ℝ) < 11 / 64)
  norm_num at hh
  have he : Real.log (300 : ℝ) = 8 * Real.log 2 + Real.log (75 / 64) := by
    rw [show (300 : ℝ) = 2 ^ 8 * (75 / 64) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_lt_d9]

/-- The logarithm of seven is enclosed using a negative cubic argument. -/
theorem log_seven_le : Real.log (7 : ℝ) ≤ 973 / 500 := by
  have hh := log_le_cubic (by norm_num : (-1 : ℝ) < -(1 / 8))
  norm_num at hh
  have he : Real.log (7 : ℝ) = 3 * Real.log 2 + Real.log (7 / 8) := by
    rw [show (7 : ℝ) = 2 ^ 3 * (7 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_lt_d9]

/-- Ford's packet-width logarithm is bounded before dividing by log k. -/
theorem log_width_le : Real.log (53 / 50 : ℝ) ≤ 1821 / 31250 := by
  have hh := log_le_cubic (by norm_num : (-1 : ℝ) < 3 / 50)
  norm_num at hh ⊢
  exact hh

/-- The paper's early-defect numerical anchor, with its original precision. -/
theorem early_exponential_anchor :
    (24119 / 2500000 : ℝ) ≤ (1 / 2) * Real.exp (-(1970 / 499)) := by
  have hu := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
  rw [← Real.exp_nat_mul] at hu
  norm_num at hu
  have hl := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 26 / 499) 4
  norm_num [Finset.sum_range_succ] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Real.exp_pos (1970 / 499)).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  have hb : Real.exp (1970 / 499 : ℝ) ≤ 1250000 / 24119 := by
    nlinarith only [hu, hm]
  rw [Real.exp_neg]
  change (24119 / 2500000 : ℝ) ≤ (1 / 2) / Real.exp (1970 / 499)
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- The original fixed coefficient scale W. -/
def coefficientScale (k : ℕ) : ℝ := (k : ℝ) ^ ((411 / 100) * (k : ℝ))

/-- The original scale is at least one in the entire required degree range. -/
theorem coefficientScale_ge_one {k : ℕ} (hk : 1000 ≤ k) : 1 ≤ coefficientScale k := by
  apply Real.one_le_rpow (by exact_mod_cast (show 1 ≤ k by omega))
  positivity

/-- Both branches of the literal published base fit the same fixed power. -/
theorem publishedBase_le {k : ℕ} (hk : 1000 ≤ k) :
    publishedBase k (3 / 50) ≤ Real.exp ((4110 / 1001) * Real.log k) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have ht : 13815 / 2000 ≤ Real.log (k : ℝ) :=
    log_thousand_ge.trans (Real.log_le_log (by norm_num) hkR)
  have htpos : 0 < Real.log (k : ℝ) := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos htpos (by norm_num : (0 : ℝ) < 7))
  rw [Real.log_div htpos.ne' (by norm_num : (7 : ℝ) ≠ 0)] at hlog
  have hpoly : Real.log (300 * (k : ℝ) ^ 3 * Real.log k) ≤
      (4110 / 1001) * Real.log k := by
    rw [Real.log_mul (by positivity) htpos.ne',
      Real.log_mul (by norm_num : (300 : ℝ) ≠ 0) (pow_ne_zero _ hkpos.ne'), Real.log_pow]
    norm_num
    linarith [log_three_hundred_le, log_seven_le]
  unfold publishedBase
  norm_num
  constructor
  · linarith
  · exact (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).mp
      (by simpa only [Real.log_exp] using hpoly)

/-- The complete published starting height is bounded by Ford's W,
with the original 4.11 coefficient and k>=1000 threshold. -/
theorem published_height_le {k : ℕ} (hk : 1000 ≤ k) :
    publishedBase k (3 / 50) ^ (k + 1) ≤ coefficientScale k := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have ht : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hV : 0 ≤ publishedBase k (3 / 50) :=
    (Real.exp_pos _).le.trans (le_max_left _ _)
  have hb := pow_le_pow_left₀ hV (publishedBase_le hk) (k + 1)
  rw [← Real.exp_nat_mul] at hb
  refine hb.trans ?_
  unfold coefficientScale
  rw [Real.rpow_def_of_pos hkpos]
  apply Real.exp_le_exp.mpr
  have hh : ((k : ℝ) + 1) * (4110 / 1001) ≤ (411 / 100) * k := by linarith
  have hm := mul_le_mul_of_nonneg_right hh ht
  push_cast
  nlinarith only [hm]

end
end RiemannGaussian.VinogradovFordCoefficientScale
