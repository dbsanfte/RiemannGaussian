/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCubicSchedule
import RiemannGaussian.ZetaVinogradovBalancedScale

/-!
# The cubic profile and its actual enlarged threshold on one schedule

The common VK width keeps its arbitrary coefficient. On degree
floor((L/log L)^(1/3)/64), the normalized radius is 1/4 and the
complete normalized growth cost is five. The required T_(8n)+1
is paid at the actual ordinate, including natural rounding.
-/

namespace RiemannGaussian.ZetaVinogradovCubicScale
noncomputable section
open Filter VinogradovCubicBudget VinogradovScaleSelection
open VinogradovSharperBudget (delta delta_pos)
open VinogradovHeightSchedule (size size_atTop balanced_identity)
open ZetaNearOneBudgetLimit (scale scale_pos scale_atTop)
open ZetaVinogradovBalancedScale (level width level_atTop)
open scoped Topology

/-- The single natural degree used at the actual ordinate. -/
def order (t : ℝ) : ℕ := VinogradovScaledSchedule.degree (scale t)


/-- The actual coefficient-aware natural order tends to infinity. -/
theorem order_atTop : Tendsto order atTop atTop := VinogradovScaledSchedule.degree_atTop.comp scale_atTop


/-- The complete radius has the exact balanced normalization at the
actual ordinate. -/
theorem radius_scaled :
    Tendsto (fun t : ℝ ↦ delta (order t) * size (scale t) ^ 2) atTop (𝓝 (1 / 4)) :=
  VinogradovCubicSchedule.radius_scaled.comp scale_atTop


/-- The entire original height-growth cost has exact normalized limit five. -/
theorem growth_normalized :
    Tendsto (fun t : ℝ ↦ growth (order t) * scale t / level t) atTop (𝓝 5) :=
  VinogradovCubicSchedule.growth_normalized.comp scale_atTop


/-- The full moving-radius normalization keeps its exact coefficient. -/
theorem width_mul_level_div_delta (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t * level t / delta (order t)) atTop (𝓝 (4 * C)) := by
  have h := (tendsto_const_nhds (x := C)).div radius_scaled
    (by norm_num : (1 / 4 : ℝ) ≠ 0)
  rw [show C / (1 / 4 : ℝ) = 4 * C by ring] at h
  apply h.congr'
  filter_upwards [scale_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with t ht
  have hl : 0 < level t := Real.log_pos ht
  have hs : 0 < size (scale t) := by
    unfold size
    positivity [scale_pos t]
  have he := balanced_identity ht
  change size (scale t) ^ 2 * level t = scale t ^ (2 / 3 : ℝ) * level t ^ (1 / 3 : ℝ) at he
  simp only [Pi.div_apply, width]
  rw [← he]
  field_simp


/-- The proposed width is negligible against the full analytic radius
on the same moving schedule. -/
theorem width_div_delta_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t / delta (order t)) atTop (𝓝 0) := by
  have h := (width_mul_level_div_delta C).div_atTop level_atTop
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  field_simp


/-- The expanded block-selection index pays every original physical-height
condition, with its local-disc unit buffer included. -/
theorem eventually_parameters : ∀ᶠ t : ℝ in atTop,
    48 ≤ order t ∧ (heightThreshold (8 * order t) : ℝ) + 1 ≤ t := by
  filter_upwards [ZetaVinogradovScheduledMargin.eventually_parameters,
    order_atTop.eventually (eventually_ge_atTop 48),
    (size_atTop.comp scale_atTop).eventually (eventually_ge_atTop (0 : ℝ))] with t ht hn hs
  refine ⟨hn, ?_⟩
  have h : (heightThreshold (8 * order t) : ℝ) ≤
      heightThreshold (ZetaVinogradovScheduledMargin.order t) := by
    exact_mod_cast VinogradovScaledSchedule.heightThreshold_mono
      (VinogradovCubicSchedule.eight_degree_le_index hs)
  linarith [ht.2.1]


/-- Absolute height preserves the entire schedule and proposed width. -/
theorem abs_invariance (C t : ℝ) :
    order |t| = order t ∧ level |t| = level t ∧ width C |t| = width C t := by
  simp [order, level, width, scale, ZetaNearOneLogProfile.height]

end
end RiemannGaussian.ZetaVinogradovCubicScale
