/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCubicBudget
import RiemannGaussian.VinogradovScaledSchedule

/-!
# The retained cubic growth on one natural degree schedule

The degree floor((L/log L)^(1/3)/64) has normalized radius 1/4 and
normalized full growth cost five. The expanded block window requires
T_(8n), not T_n. That larger threshold is proved on the same schedule.
-/

namespace RiemannGaussian.VinogradovCubicSchedule
noncomputable section
open Filter VinogradovCubicBudget VinogradovScaleSelection
open VinogradovSharperBudget (delta)
open VinogradovHeightSchedule (size size_atTop size_cube)
open VinogradovScaledSchedule (degree degree_atTop affine_ratio heightThreshold_mono)
open scoped Topology

/-- The full actual radius has normalized limit one quarter. -/
theorem radius_scaled :
    Tendsto (fun L : ℝ ↦ delta (degree L) * size L ^ 2) atTop (𝓝 (1 / 4)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div ((affine_ratio.pow 2).const_mul 4096)
    (by norm_num : (4096 : ℝ) * (1 / 32) ^ 2 ≠ 0)
  rw [show (1 : ℝ) / (4096 * (1 / 32) ^ 2) = 1 / 4 by norm_num] at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL
  simp only [Pi.div_apply]
  unfold delta
  field_simp

/-- The actual cubic exponent retains its complete affine denominator. -/
theorem growth_scaled :
    Tendsto (fun L : ℝ ↦ growth (degree L) * size L ^ 3) atTop (𝓝 5) := by
  have h := (tendsto_const_nhds (x := (5 : ℝ))).div ((affine_ratio.pow 3).const_mul 32768)
    (by norm_num : (32768 : ℝ) * (1 / 32) ^ 3 ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL
  simp only [Pi.div_apply, growth_eq]
  field_simp

/-- The complete growth cost tends to five second logarithms. -/
theorem growth_normalized :
    Tendsto (fun L : ℝ ↦ growth (degree L) * L / Real.log L) atTop (𝓝 5) := by
  apply growth_scaled.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [size_cube hL]
  ring

/-- The enlarged block-selection index remains below the already paid
balanced index, including natural rounding. -/
theorem eight_degree_le_index {L : ℝ} (hs : 0 ≤ size L) :
    8 * degree L ≤ VinogradovHeightSchedule.index L := by
  unfold VinogradovHeightSchedule.index
  apply (Nat.le_floor_iff hs).mpr
  have hf := Nat.floor_le (div_nonneg hs (by norm_num : (0 : ℝ) ≤ 64))
  change (degree L : ℝ) ≤ size L / 64 at hf
  push_cast
  linarith

/-- The complete expanded-window starting height is paid jointly with
the actual growing degree; no fixed-degree threshold is substituted. -/
theorem eventually_threshold : ∀ᶠ L : ℝ in atTop,
    48 ≤ degree L ∧ (heightThreshold (8 * degree L) : ℝ) ≤ Real.exp (L / 2) := by
  filter_upwards [VinogradovHeightSchedule.eventually_threshold,
    degree_atTop.eventually (eventually_ge_atTop 48)] with L ht hn
  refine ⟨hn, ?_⟩
  have h : (heightThreshold (8 * degree L) : ℝ) ≤
      heightThreshold (VinogradovHeightSchedule.index L) := by
    exact_mod_cast heightThreshold_mono (eight_degree_le_index (by linarith [ht.2.2.1]))
  exact h.trans ht.2.2.2

end
end RiemannGaussian.VinogradovCubicSchedule
