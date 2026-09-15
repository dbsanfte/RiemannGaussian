/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# A strict analytic bound for the retained harmonic cost

The exact combined head and central cost per multiplicity square is below one on the original annulus. This does not bound the three unpaid arithmetic components.
-/

namespace RiemannGaussian.RieszHarmonicCostBounds
noncomputable section
open scoped BigOperators

/-- The combined negative head and central cost per multiplicity square. -/
def paidHarmonicCost (u : ℝ) : ℝ :=
  Real.log (32 / 15) / (-2 * u * Real.log u) - Real.log (17 / 15)

/-- A rational enclosure of the existing annular radius follows from
a finite lower Taylor bound for the exponential. -/
theorem exp_neg_two_thirds_le : Real.exp (-(2 / 3 : ℝ)) ≤ 33 / 64 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) 5
  norm_num [Finset.sum_range_succ] at he
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

/-- The literal limiting length denominator stays above a positive
rational bound throughout the annular source range. -/
theorem source_log_scale_lower {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) : 17 / 25 ≤ -2 * u * Real.log u := by
  have hu0 : 0 < u := by linarith
  have huq : u ≤ 33 / 64 := huh.le.trans exp_neg_two_thirds_le
  have hh := Real.log_le_sub_one_of_pos (show 0 < 2 * u by positivity)
  rw [Real.log_mul (by norm_num) hu0.ne'] at hh
  have hlog2 : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * u by positivity)
  have hml := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2 * u by positivity)
  have hq := mul_nonneg (show 0 ≤ u - 1 / 2 by linarith)
    (show 0 ≤ 33 / 64 - u by linarith)
  nlinarith

/-- An analytic upper bound for the combined reciprocal-interval logarithm. -/
theorem log_thirtytwo_fifteenths_lt : Real.log (32 / 15 : ℝ) < 19 / 25 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
  have he : Real.log (32 / 15 : ℝ) = Real.log 2 + Real.log (16 / 15 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  rw [he]
  linarith [Real.log_two_lt_d9]

/-- The exact combined cost is strictly less than one throughout the
annulus. Multiplicity is not assumed to be one and is not absorbed here. -/
theorem paidHarmonicCost_lt_one {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) : paidHarmonicCost u < 1 := by
  have hD := source_log_scale_lower hu huh
  have hp : 0 < -2 * u * Real.log u := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 17 / 15)
  norm_num only at hlo
  have hm := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 1 + Real.log (17 / 15 : ℝ) by linarith)
  unfold paidHarmonicCost
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ hp).mpr
  nlinarith [log_thirtytwo_fifteenths_lt]

end
end RiemannGaussian.RieszHarmonicCostBounds
