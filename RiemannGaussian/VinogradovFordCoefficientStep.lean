/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordEarlyDefect

/-!
# Ford's early and late coefficient costs

The first 1.97*k steps pay the entire packet branch from the proved
defect decrease. Later steps retain both factors of the original maximum;
no independent bound on a moment is assumed in this scalar coefficient
calculation.
-/

namespace RiemannGaussian.VinogradovFordCoefficientStep
noncomputable section
open VinogradovFordGlobalStep VinogradovFordSelectedIteration
open VinogradovFordMomentSequence VinogradovFordTailThreshold
open VinogradovFordCoefficientScale VinogradovFordEarlyDefect

/-- The literal packet branch at moment index j, with omega=0.06. -/
def packetCost (k j : ℕ) : ℝ :=
  (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * order k j + k ^ 2)

/-- Every packet cost is at least one. -/
theorem packetCost_ge_one {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) : 1 ≤ packetCost k j := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  · exact one_le_pow₀ (by norm_num)

/-- The early packet cost has Ford's original 0.078*k^2 upper exponent. -/
theorem early_packet_le {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    packetCost k j ≤ (k : ℝ) ^ ((39 / 500) * (k : ℝ) ^ 2) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have ht : 69 / 10 ≤ Real.log (k : ℝ) := by
    have hh := log_thousand_ge.trans (Real.log_le_log (by norm_num) hkR)
    linarith
  have ht0 : 0 ≤ Real.log (k : ℝ) := by linarith
  have hwidth0 : 0 ≤ Real.log (53 / 50 : ℝ) := Real.log_nonneg (by norm_num)
  have horder : ((4 * order k j + k ^ 2 : ℕ) : ℝ) ≤ (222 / 25) * (k : ℝ) ^ 2 := by
    unfold order
    push_cast
    have hm := mul_le_mul_of_nonneg_left hj hkpos.le
    nlinarith
  have hfirst : 3 * (k : ℝ) ≤ (3 / 1000) * (k : ℝ) ^ 2 := by
    have hm := mul_nonneg hkpos.le (show 0 ≤ (k : ℝ) - 1000 by linarith)
    nlinarith
  have hf := mul_le_mul_of_nonneg_right hfirst ht0
  have hw := mul_le_mul_of_nonneg_right horder hwidth0
  have hw' := mul_le_mul_of_nonneg_left log_width_le (show (0 : ℝ) ≤ (222 / 25) * (k : ℝ) ^ 2 by positivity)
  have hr : (222 / 25) * (1821 / 31250 : ℝ) ≤ (3 / 40) * Real.log k := by linarith
  have hr' := mul_le_mul_of_nonneg_right hr (sq_nonneg (k : ℝ))
  apply (Real.log_le_log_iff (by unfold packetCost; positivity)
    (Real.rpow_pos_of_pos hkpos _)).mp
  rw [Real.log_rpow hkpos]
  unfold packetCost
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  push_cast at hw
  nlinarith only [hf, hw, hw', hr']

/-- The complete small-endpoint factor fits the same power of W. -/
theorem small_factor_le {k : ℕ} (hk : 1000 ≤ k) {delta delta' : ℝ}
    (hdrop : delta' ≤ delta) :
    publishedBase k (3 / 50) ^ (((k : ℝ) + 1) * (delta - delta')) ≤
      coefficientScale k ^ (delta - delta') := by
  have hV : 0 ≤ publishedBase k (3 / 50) := (Real.exp_pos _).le.trans (le_max_left _ _)
  have hh := Real.rpow_le_rpow (pow_nonneg hV (k + 1)) (published_height_le hk)
    (sub_nonneg.mpr hdrop)
  rw [← Real.rpow_natCast_mul hV] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- Ford's early comparison (3.20) is strict for the actual selected defects. -/
theorem early_packet_lt_scale {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    packetCost k j < coefficientScale k ^ (selectedDefect k j - selectedDefect k (j + 1)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  refine (early_packet_le hk hj).trans_lt ?_
  unfold coefficientScale
  rw [← Real.rpow_mul hkpos.le]
  apply Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < k)
  have hm := mul_le_mul_of_nonneg_left (early_defect_drop hk hj)
    (show (0 : ℝ) ≤ (411 / 100) * (k : ℝ) by positivity)
  nlinarith [sq_pos_of_pos hkpos]

/-- During the early range the whole original maximum is paid by W. -/
theorem early_step_le {k j : ℕ} (hk : 1000 ≤ k)
    (hj : (j : ℝ) + 1 ≤ (197 / 100) * (k : ℝ)) :
    stepCoefficient k (order k j) (3 / 50) (selectedDefect k j) (selectedDefect k (j + 1)) ≤
      coefficientScale k ^ (selectedDefect k j - selectedDefect k (j + 1)) := by
  unfold stepCoefficient
  norm_num only [show (1 + 3 / 50 : ℝ) = 53 / 50 by norm_num]
  exact max_le (early_packet_lt_scale hk hj).le
    (small_factor_le hk (selectedDefect_antitone (by omega : 26 ≤ k) (by omega : j ≤ j + 1)))

/-- At every later step, retaining both factors pays the original maximum. -/
theorem step_le_product {k : ℕ} (hk : 1000 ≤ k) (j : ℕ) :
    stepCoefficient k (order k j) (3 / 50) (selectedDefect k j) (selectedDefect k (j + 1)) ≤
      packetCost k j * coefficientScale k ^ (selectedDefect k j - selectedDefect k (j + 1)) := by
  have hdrop := selectedDefect_antitone (by omega : 26 ≤ k) (by omega : j ≤ j + 1)
  have hs := small_factor_le hk hdrop
  have hw : 1 ≤ coefficientScale k ^ (selectedDefect k j - selectedDefect k (j + 1)) :=
    Real.one_le_rpow (coefficientScale_ge_one hk) (sub_nonneg.mpr hdrop)
  have hp := packetCost_ge_one hk j
  unfold stepCoefficient
  norm_num only [show (1 + 3 / 50 : ℝ) = 53 / 50 by norm_num]
  apply max_le
  · exact le_mul_of_one_le_right (by positivity) hw
  · exact hs.trans (le_mul_of_one_le_left (by positivity) hp)

end
end RiemannGaussian.VinogradovFordCoefficientStep
