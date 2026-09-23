/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovScaledSchedule
import RiemannGaussian.VinogradovSharperBudget

/-!
# A balanced degree for the stronger actual VK growth

The single degree floor((L/log L)^(1/3)/32) pays the same original
height threshold. Its stronger radius has scaled limit 1/16 and its
complete growth cost has normalized limit four. Natural rounding and
the minimum degree forty-eight are retained.
-/

namespace RiemannGaussian.VinogradovSharperSchedule
noncomputable section
open Filter VinogradovSharperBudget VinogradovScaleSelection
open VinogradovHeightSchedule (size size_atTop size_cube)
open scoped Topology

/-- A natural degree that incorporates the actual cubic-growth coefficient. -/
def degree (L : ℝ) : ℕ := ⌊size L / 32⌋₊

/-- The scaled natural degree still grows without bound. -/
theorem degree_atTop : Tendsto degree atTop atTop :=
  tendsto_nat_floor_atTop.comp (size_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 32))

/-- Rounding preserves the exact scaled-degree ratio. -/
theorem degree_ratio : Tendsto (fun L : ℝ ↦ (degree L : ℝ) / size L) atTop (𝓝 (1 / 32)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (show (0 : ℝ) ≤ 1 / 32 by norm_num)).comp size_atTop
  simpa only [Function.comp_def, degree, one_div_mul_eq_div] using h

/-- The complete affine degree factor has its exact normalized limit. -/
theorem affine_ratio :
    Tendsto (fun L : ℝ ↦ (2 * (degree L : ℝ) + 1) / size L) atTop (𝓝 (1 / 16)) := by
  have h := (degree_ratio.const_mul 2).add (size_atTop.const_div_atTop (1 : ℝ))
  norm_num at h
  convert h using 1
  funext L
  ring

/-- The actual analytic radius, including natural rounding and the
affine offset in its denominator, has its exact balanced limit. -/
theorem radius_scaled :
    Tendsto (fun L : ℝ ↦ delta (degree L) * size L ^ 2) atTop (𝓝 (1 / 16)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div ((affine_ratio.pow 2).const_mul 4096)
    (by norm_num : (4096 : ℝ) * (1 / 16) ^ 2 ≠ 0)
  rw [show (1 : ℝ) / (4096 * (1 / 16) ^ 2) = 1 / 16 by norm_num] at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL
  simp only [Pi.div_apply]
  unfold delta
  field_simp

/-- The actual cubic height exponent retains its exact scaled value. -/
theorem growth_scaled :
    Tendsto (fun L : ℝ ↦ growth (degree L) * size L ^ 3) atTop (𝓝 4) := by
  have h := (radius_scaled.const_mul 2).div degree_ratio (by norm_num : (1 / 32 : ℝ) ≠ 0)
  norm_num at h
  apply h.congr'
  filter_upwards [size_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    degree_atTop.eventually (eventually_ge_atTop 1)] with L hL hn
  have hnpos : (0 : ℝ) < degree L := by exact_mod_cast (show 0 < degree L by omega)
  simp only [Pi.div_apply]
  unfold growth
  field_simp

/-- The entire actual zeta height cost is asymptotic to four second
logarithms on the scaled degree schedule. -/
theorem growth_normalized :
    Tendsto (fun L : ℝ ↦ growth (degree L) * L / Real.log L) atTop (𝓝 4) := by
  apply growth_scaled.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [size_cube hL]
  ring

/-- The coefficient-aware degree is no larger than the original
balanced degree wherever its continuous size is nonnegative. -/
theorem degree_le_index {L : ℝ} (hs : 0 ≤ size L) :
    degree L ≤ VinogradovHeightSchedule.index L := by
  apply Nat.floor_le_floor
  linarith

/-- Every original moment threshold remains available on the new
schedule; this is a joint-degree statement, not a fixed-index limit. -/
theorem eventually_threshold : ∀ᶠ L : ℝ in atTop,
    48 ≤ degree L ∧ (heightThreshold (degree L) : ℝ) ≤ Real.exp (L / 2) := by
  filter_upwards [VinogradovHeightSchedule.eventually_threshold,
    degree_atTop.eventually (eventually_ge_atTop 48)] with L ht hn
  refine ⟨hn, ?_⟩
  have h : (heightThreshold (degree L) : ℝ) ≤
      heightThreshold (VinogradovHeightSchedule.index L) := by
    exact_mod_cast VinogradovScaledSchedule.heightThreshold_mono (degree_le_index (by linarith [ht.2.2.1]))
  exact h.trans ht.2.2.2

end
end RiemannGaussian.VinogradovSharperSchedule
