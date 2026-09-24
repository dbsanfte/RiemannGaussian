/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectanglePhase

/-!
# Exact concentration rates for the concrete rectangle's mask cuts

The five prime-leg cuts and both total-window cuts have strict factorial
large-deviation margins. All constants are checked rational inequalities.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit

/-- The common positive kernel tilt leaves a summable arithmetic exponent. -/
def rectangleTilt : ℝ := 131071 / 262144

private theorem log_twenty_twentyone : Real.log (20 / 21 : ℝ) ≤ -(48790 / 1000000) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 41)
    (by norm_num : (1 / 41 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  rw [show (20 / 21 : ℝ) = (21 / 20)⁻¹ by norm_num, Real.log_inv]
  linarith

private theorem log_twentyfive_twentythree : Real.log (25 / 23 : ℝ) ≤ 83382 / 1000000 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 83382 / 1000000) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem log_ten_eleven : Real.log (10 / 11 : ℝ) ≤ -(95310 / 1000000) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 21)
    (by norm_num : (1 / 21 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  rw [show (10 / 11 : ℝ) = (11 / 10)⁻¹ by norm_num, Real.log_inv]
  linarith

private theorem log_hundred_ninetythree : Real.log (100 / 93 : ℝ) ≤ 72571 / 1000000 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 72571 / 1000000) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem log_thirtynine_forty : Real.log (39 / 40 : ℝ) ≤ -(25317 / 1000000) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 79)
    (by norm_num : (1 / 79 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  rw [show (39 / 40 : ℝ) = (40 / 39)⁻¹ by norm_num, Real.log_inv]
  linarith

private theorem log_fortyone_forty : Real.log (41 / 40 : ℝ) ≤ 24693 / 1000000 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 24693 / 1000000) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem log_relative_le {q : ℝ} (hq : 0 < q) :
    Real.log (rectangleTilt / q) ≤ Real.log ((1 / 2) / q) := by
  apply Real.log_le_log (div_pos (by norm_num [rectangleTilt]) hq)
  exact div_le_div_of_nonneg_right (by norm_num [rectangleTilt]) hq.le

/-- The five individual prime-log failures have a common fixed saving;
the additive constant retains the exact successor-order rounding. -/
theorem rectangle_leg_exponents {N j h : ℕ} (hh : h ∈ rectangleOrders N j) :
    (∀ a : ℝ, a ≤ N →
      j * Real.log (rectangleTilt / (21 / 40)) + ((21 / 40) - rectangleTilt) * a ≤
        1 - (N : ℝ) / 2000) ∧
    (∀ a : ℝ, (5 / 4 : ℝ) * N ≤ a →
      j * Real.log (rectangleTilt / (23 / 50)) + ((23 / 50) - rectangleTilt) * a ≤
        1 - (N : ℝ) / 2000) ∧
    (∀ a : ℝ, a ≤ (7 / 10 : ℝ) * N →
      (N + 1 - j - h : ℕ) * Real.log (rectangleTilt / (11 / 20)) +
        ((11 / 20) - rectangleTilt) * a ≤ 1 - (N : ℝ) / 2000) ∧
    (∀ a : ℝ, (N : ℝ) ≤ a →
      (N + 1 - j - h : ℕ) * Real.log (rectangleTilt / (93 / 200)) +
        ((93 / 200) - rectangleTilt) * a ≤ 1 - (N : ℝ) / 2000) ∧
    (∀ a : ℝ, (N : ℝ) / 10 ≤ a →
      (h + 1 : ℕ) * Real.log (rectangleTilt / (2 / 5)) +
        ((2 / 5) - rectangleTilt) * a ≤ 1 - (N : ℝ) / 2000) := by
  obtain ⟨hr, _, hjlo, hjhi, hhlo, hhhi⟩ := Finset.mem_filter.mp hh
  have hr' := Finset.mem_range.mp hr
  have hjloR : 21 * (N : ℝ) ≤ 40 * j := by exact_mod_cast hjlo
  have hjhiR : 40 * (j : ℝ) ≤ 23 * N := by exact_mod_cast hjhi
  have hHhi : 100 * ((h + 1 : ℕ) : ℝ) ≤ 4 * N := by exact_mod_cast hhhi
  have hlo : 77 * N ≤ 200 * (N + 1 - j - h) := by omega
  have hhi : 200 * (N + 1 - j - h) ≤ 93 * N + 400 := by omega
  have hloR : 77 * (N : ℝ) ≤ 200 * (N + 1 - j - h : ℕ) := by exact_mod_cast hlo
  have hhiR : 200 * ((N + 1 - j - h : ℕ) : ℝ) ≤ 93 * N + 400 := by exact_mod_cast hhi
  have hp0 := (log_relative_le (by norm_num : (0 : ℝ) < 21 / 40))
  have hp1 := (log_relative_le (by norm_num : (0 : ℝ) < 23 / 50))
  have hq0 := (log_relative_le (by norm_num : (0 : ℝ) < 11 / 20))
  have hq1 := (log_relative_le (by norm_num : (0 : ℝ) < 93 / 200))
  have hr1 := (log_relative_le (by norm_num : (0 : ℝ) < 2 / 5))
  norm_num only [div_div, one_div, mul_inv_rev, inv_div, div_mul_eq_mul_div,
    div_self, OfNat.ofNat_ne_zero] at hp0 hp1 hq0 hq1 hr1
  have hp0' := mul_le_mul_of_nonneg_left (hp0.trans log_twenty_twentyone) (Nat.cast_nonneg (α := ℝ) j)
  have hp1' := mul_le_mul_of_nonneg_left (hp1.trans log_twentyfive_twentythree) (Nat.cast_nonneg (α := ℝ) j)
  have hq0' := mul_le_mul_of_nonneg_left (hq0.trans log_ten_eleven)
    (Nat.cast_nonneg (α := ℝ) (N + 1 - j - h))
  have hq1' := mul_le_mul_of_nonneg_left (hq1.trans log_hundred_ninetythree)
    (Nat.cast_nonneg (α := ℝ) (N + 1 - j - h))
  have hr1' := mul_le_mul_of_nonneg_left (hr1.trans ZetaRieszJointAllocation.log_tilt_bounds.2)
    (Nat.cast_nonneg (α := ℝ) (h + 1))
  dsimp [rectangleTilt] at hp0' hp1' hq0' hq1' hr1' ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro a ha <;>
    nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Both original total-log window failures retain a source-scale
saving for the correlated total order N+2. -/
theorem rectangle_total_exponents (N : ℕ) :
    (∀ a : ℝ, a ≤ (39 / 20 : ℝ) * N →
      (N + 2 : ℕ) * Real.log (rectangleTilt / (20 / 39)) +
        ((20 / 39) - rectangleTilt) * a ≤ 1 - (N : ℝ) / 4000) ∧
    (∀ a : ℝ, (41 / 20 : ℝ) * N ≤ a →
      (N + 2 : ℕ) * Real.log (rectangleTilt / (20 / 41)) +
        ((20 / 41) - rectangleTilt) * a ≤ 1 - (N : ℝ) / 4000) := by
  have hlo := log_relative_le (by norm_num : (0 : ℝ) < 20 / 39)
  have hhi := log_relative_le (by norm_num : (0 : ℝ) < 20 / 41)
  norm_num at hlo hhi
  have h₀ := mul_le_mul_of_nonneg_left (hlo.trans log_thirtynine_forty)
    (Nat.cast_nonneg (α := ℝ) (N + 2))
  have h₁ := mul_le_mul_of_nonneg_left (hhi.trans log_fortyone_forty)
    (Nat.cast_nonneg (α := ℝ) (N + 2))
  dsimp [rectangleTilt] at h₀ h₁ ⊢
  push_cast at h₀ h₁ ⊢
  constructor <;> intro a ha <;> nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Even the weakest of these mask-error rates beats the full source
growth on the requested closed radius interval. -/
def rectangleMaskRate : ℝ := radiusCeiling / rectangleTilt * Real.exp (-(1 / 4000 : ℝ))

theorem rectangleMaskRate_bounds : 0 ≤ rectangleMaskRate ∧ rectangleMaskRate < 1 := by
  constructor
  · unfold rectangleMaskRate radiusCeiling rectangleTilt; positivity
  · rw [rectangleMaskRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1 / 4000 : ℝ)
    norm_num [radiusCeiling, rectangleTilt] at h ⊢
    linarith

end
end RiemannGaussian.ZetaRieszSkewAllocation
