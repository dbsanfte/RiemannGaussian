/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordCoefficientScale

/-!
# Paying Ford's early coefficient steps

The actual selected defects stay above the paper's `0.0096476*k^2`
floor throughout the first `1.97*k` steps. Their decrease pays the
packet branch of the original maximum coefficient before any product
is bounded.
-/

namespace RiemannGaussian.VinogradovFordEarlyDefect
noncomputable section
open VinogradovFordSelectedIteration VinogradovFordLowerDefect
open VinogradovFordPotentialIteration VinogradovFordPotential
open VinogradovFordCoefficientScale

/-- The actual normalized defect retains the simpler geometric envelope
used in the paper's early-stage argument. -/
theorem normalized_geometric_lower {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) :
    (1 / 2) * (1 - 2 / (k : ℝ)) ^ (j + 1) ≤ normalized k j := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hf : 0 ≤ 1 - 2 / (k : ℝ) := by
    have hh : 2 / (k : ℝ) ≤ 1 := (div_le_one hkpos).mpr (by linarith)
    linarith
  have hl := selectedDefect_geometric_lower (by omega : 26 ≤ k) j
  have hn : (1 - 2 / (k : ℝ)) ^ j * ((1 - 1 / k) / 2) ≤ normalized k j := by
    unfold normalized
    apply (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr
    have he : (1 - 2 / (k : ℝ)) ^ j * ((1 - 1 / k) / 2) * (k : ℝ) ^ 2 =
        (1 - 2 / (k : ℝ)) ^ j * ((k : ℝ) * ((k : ℝ) - 1) / 2) := by
      field_simp
    rwa [he]
  have hh : (1 - 2 / (k : ℝ)) / 2 ≤ (1 - 1 / (k : ℝ)) / 2 := by
    have hp : (0 : ℝ) ≤ 1 / k := by positivity
    simp only [div_eq_mul_inv] at hp ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hf j)
  rw [pow_succ]
  nlinarith only [hn, hm]

/-- The logarithm of the exact geometric ratio has the original lower rate. -/
theorem log_ratio_ge {k : ℕ} (hk : 1000 ≤ k) :
    -(2 / ((k : ℝ) - 2)) ≤ Real.log (1 - 2 / (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkm : (k : ℝ) - 2 ≠ 0 := by linarith
  have hf : 0 < 1 - 2 / (k : ℝ) := by
    have hh : 2 / (k : ℝ) < 1 := (div_lt_one hkpos).mpr (by linarith)
    linarith
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - 2 / (k : ℝ)) by positivity)
  rw [Real.log_div one_ne_zero hf.ne', Real.log_one, zero_sub] at hh
  have he : 1 / (1 - 2 / (k : ℝ)) - 1 = 2 / ((k : ℝ) - 2) := by
    field_simp
    ring
  rw [he] at hh
  linarith

/-- Every early selected defect has Ford's exact numerical lower floor. -/
theorem early_normalized_lower {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    (24119 / 2500000 : ℝ) ≤ normalized k j := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hkm : 0 < (k : ℝ) - 2 := by linarith
  have hf : 0 < 1 - 2 / (k : ℝ) := by
    have hh : 2 / (k : ℝ) < 1 := (div_lt_one hkpos).mpr (by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_left (log_ratio_ge hk)
    (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
  have hb : 2 * ((j : ℝ) + 1) / ((k : ℝ) - 2) ≤ 1970 / 499 :=
    (div_le_iff₀ hkm).mpr (by linarith)
  have he : ((j : ℝ) + 1) * (-(2 / ((k : ℝ) - 2))) =
      -(2 * ((j : ℝ) + 1) / ((k : ℝ) - 2)) := by ring
  rw [he] at hm
  have hrate : -(1970 / 499 : ℝ) ≤ ((j : ℝ) + 1) * Real.log (1 - 2 / (k : ℝ)) := by linarith
  have hexp := Real.exp_le_exp.mpr hrate
  have hp : Real.exp (((j : ℝ) + 1) * Real.log (1 - 2 / (k : ℝ))) =
      (1 - 2 / (k : ℝ)) ^ (j + 1) := by
    rw [← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log hf]
  rw [hp] at hexp
  exact early_exponential_anchor.trans
    ((mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      (normalized_geometric_lower hk j))

/-- The early normalized floor keeps the actual recurrence in its active
range; no active-step hypothesis is supplied separately. -/
theorem early_active {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    (k : ℝ) < selectedDefect k j := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hh := (le_div_iff₀ (sq_pos_of_pos hkpos)).mp (early_normalized_lower hk hj)
  have hp := mul_nonneg hkpos.le (show 0 ≤ (k : ℝ) - 1000 by linarith)
  nlinarith

/-- The complete numerical correction in the normalized recurrence fits
the original 0.002 loss in the rate ratio. -/
theorem effective_rate_reserve {k j : ℕ} (hk : 1000 ≤ k)
    (hactive : (k : ℝ) < selectedDefect k j) :
    2 / (k : ℝ) - (beta k - correction k / normalized k j) ≤ 1 / (250 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have he : 2 / (k : ℝ) - (beta k - k * correction k) = 80 / (21 * (k : ℝ) ^ 2) := by
    unfold beta correction
    field_simp
    ring
  have hb : 80 / (21 * (k : ℝ) ^ 2) ≤ 1 / (250 * (k : ℝ)) := by
    field_simp
    nlinarith
  have hh := (effective_rate_bounds hk hactive).1
  linarith

/-- Ford's (3.21), with the original ratio retained rather than replaced
by its uniform lower bound. -/
theorem normalized_drop {k j : ℕ} (hk : 1000 ≤ k)
    (hactive : (k : ℝ) < selectedDefect k j) :
    (2 * normalized k j / k) * (rateRatio (normalized k j) - 1 / 500) ≤
      normalized k j - normalized k (j + 1) := by
  have hd := normalized_bounds (by omega : 26 ≤ k) j
  have ha := rateRatio_bounds hd.1.le hd.2
  have hreserve := effective_rate_reserve hk hactive
  have hpos : 0 ≤ rateRatio (normalized k j) := by linarith
  have hm := mul_le_mul_of_nonneg_left hreserve hpos
  have ha' := mul_le_mul_of_nonneg_right ha.2 (show (0 : ℝ) ≤ 1 / (250 * k) by positivity)
  have hr : rateRatio (normalized k j) *
      (2 / k - (beta k - correction k / normalized k j)) ≤ 1 / (250 * (k : ℝ)) := by
    nlinarith only [hm, ha']
  have hp := mul_le_mul_of_nonneg_left hr hd.1.le
  have hs := normalized_step_le hk hactive
  have he : comparisonStep (normalized k j) (beta k - correction k / normalized k j) =
      normalized k j - (2 * normalized k j / k) * rateRatio (normalized k j) +
        normalized k j * (rateRatio (normalized k j) *
          (2 / k - (beta k - correction k / normalized k j))) := by
    unfold comparisonStep
    ring
  rw [he] at hs
  have hc : normalized k j * (1 / (250 * (k : ℝ))) = (2 * normalized k j / k) * (1 / 500) := by ring
  rw [hc] at hp
  nlinarith only [hp, hs]

/-- On the full early defect interval, the nonlinear rate pays the paper's
original 0.01916 constant. -/
theorem early_ratio_gain {d : ℝ} (hlo : 24119 / 2500000 ≤ d) (hhi : d ≤ 1 / 2) :
    479 / 25000 ≤ 2 * d * (rateRatio d - 1 / 500) := by
  have hd0 : 0 ≤ d := by linarith
  have hB : 0 < 2 - d ^ 2 := by nlinarith
  have hp := mul_nonneg (show 0 ≤ d - 24119 / 2500000 by linarith)
    (show 0 ≤ 499 / 125 - (49521 / 25000) * (d + 24119 / 2500000) by linarith)
  have hcube := pow_nonneg hd0 3
  unfold rateRatio
  field_simp
  nlinarith

/-- Each early step decreases the actual defect by at least 0.01916*k. -/
theorem early_defect_drop {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    (479 / 25000) * (k : ℝ) ≤ selectedDefect k j - selectedDefect k (j + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hn := normalized_drop hk (early_active hk hj)
  have hg := early_ratio_gain (early_normalized_lower hk hj)
    (normalized_bounds (by omega : 26 ≤ k) j).2
  have hd := div_le_div_of_nonneg_right hg hkpos.le
  have he : 2 * normalized k j * (rateRatio (normalized k j) - 1 / 500) / k =
      (2 * normalized k j / k) * (rateRatio (normalized k j) - 1 / 500) := by ring
  rw [he] at hd
  have hm := mul_le_mul_of_nonneg_right (hd.trans hn) (sq_nonneg (k : ℝ))
  have hl : (479 / 25000 / (k : ℝ)) * (k : ℝ) ^ 2 = (479 / 25000) * (k : ℝ) := by field_simp
  have hr : (normalized k j - normalized k (j + 1)) * (k : ℝ) ^ 2 =
      selectedDefect k j - selectedDefect k (j + 1) := by unfold normalized; field_simp
  rwa [hl, hr] at hm

end
end RiemannGaussian.VinogradovFordEarlyDefect
