/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovBalancedScale
import RiemannGaussian.ZetaVinogradovAngularBudget

/-!
# Exact cost of the signed angular Vinogradov endgame

The original height profile, doubled-height profile and Euler-center
logarithm have normalized limits 3, 3 and 2/3 on one moving natural
degree schedule. The full signed contradiction cost consequently tends
to 98560*C/(3*pi). The radial correction vanishes on that same schedule.
No component of the actual arithmetic or analytic budget is assumed.
-/

namespace RiemannGaussian.ZetaVinogradovBalancedBudget
noncomputable section
open Filter VinogradovNearOneBudget ZetaVinogradovBalancedScale
open ZetaNearOneBudgetLimit (scale scale_pos scale_double_div)
open ZetaVinogradovLocalDisc (profile)
open ZetaVinogradovCanonical (allowance)
open ZetaVinogradovAngularBudget (budget)
open scoped Topology

/-- The complete original contradiction cost at the proposed VK width. -/
def cost (C t : ℝ) : ℝ :=
  14 * width C t * budget (order t) (6 * width C t) t +
    392 * (width C t) ^ 2 / (delta (order t)) ^ 2

/-- The actual profile at the original height costs three second logarithms. -/
theorem profile_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) t / level t) atTop (𝓝 3) := by
  have h := ((level_atTop.const_div_atTop (Real.log 8192)).add growth_normalized).add
    (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num only [zero_add, show (2 : ℝ) + 1 = 3 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  change Real.log 8192 / level t + growth (order t) * scale t / level t + 1 =
    (Real.log 8192 + growth (order t) * scale t + level t) / level t
  field_simp

/-- The doubled evaluation uses the same natural order and has the
same leading cost, rather than paying a factor-two height majorant. -/
theorem profile_double_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) (2 * t) / level t) atTop (𝓝 3) := by
  have hg := growth_normalized.mul scale_double_div
  simp only [mul_one] at hg
  have h := ((level_atTop.const_div_atTop (Real.log 8192)).add hg).add level_double_ratio
  norm_num only [zero_add, show (2 : ℝ) + 1 = 3 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hL := scale_pos t
  change Real.log 8192 / level t +
    (growth (order t) * scale t / level t) * (scale (2 * t) / scale t) +
      level (2 * t) / level t =
    (Real.log 8192 + growth (order t) * scale (2 * t) + level (2 * t)) / level t
  field_simp

/-- The complete reciprocal-zeta center allowance has exact normalized
cost two thirds; it is not discarded as a lower-order term. -/
theorem center_log_normalized {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ Real.log (1 + 1 / (6 * width C t)) / level t)
      atTop (𝓝 (2 / 3 : ℝ)) := by
  have harg : Tendsto (fun t : ℝ ↦ 1 + 6 * width C t) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using ((width_tendsto_zero C).const_mul 6).const_add 1
  have hlog := (harg.log (by norm_num : (1 : ℝ) ≠ 0)).div_atTop level_atTop
  have h := (hlog.sub (level_atTop.const_div_atTop (Real.log 6))).sub (log_width_ratio hC)
  norm_num only [sub_zero, zero_sub, neg_neg] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hw := width_pos hC ht
  have he : 1 + 1 / (6 * width C t) = (1 + 6 * width C t) / (6 * width C t) := by
    field_simp
    ring
  rw [he, Real.log_div (by positivity : 1 + 6 * width C t ≠ 0)
    (by positivity : 6 * width C t ≠ 0),
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hw.ne']
  ring

/-- Both actual allowances retain the full profile and Euler-center
cost, with the identical moving degree at the two oscillatory heights. -/
theorem allowance_normalized {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) t / level t)
      atTop (𝓝 (11 / 3 : ℝ)) ∧
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) (2 * t) / level t)
      atTop (𝓝 (11 / 3 : ℝ)) := by
  have h₁ := profile_normalized.add (center_log_normalized hC)
  have h₂ := profile_double_normalized.add (center_log_normalized hC)
  norm_num only [show (3 : ℝ) + 2 / 3 = 11 / 3 by norm_num] at h₁ h₂
  constructor
  · convert h₁ using 1
    funext t
    unfold allowance
    ring
  · convert h₂ using 1
    funext t
    unfold allowance
    ring

/-- The full actual signed angular prime budget has its exact
source-normalized limit, including the real-axis term. -/
theorem width_mul_budget_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ width C t * budget (order t) (6 * width C t) t)
      atTop (𝓝 (7040 * C / (3 * Real.pi))) := by
  obtain ⟨h₁, h₂⟩ := allowance_normalized hC
  have h := ((width_tendsto_zero C).const_mul (1344 * localZetaLogHeight 0)).add
    (((width_mul_level_div_delta C).mul ((h₁.const_mul 8).add (h₂.const_mul 2))).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  rw [show (64 * C) * (8 * (11 / 3 : ℝ) + 2 * (11 / 3)) / Real.pi =
    7040 * C / (3 * Real.pi) by ring] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  unfold budget
  field_simp

/-- The entire signed cost has exact limit 98560*C/(3*pi); every
moving-radius correction vanishes on the same natural degree schedule. -/
theorem cost_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (cost C) atTop (𝓝 (98560 * C / (3 * Real.pi))) := by
  have h := ((width_mul_budget_tendsto hC).const_mul 14).add
    (((width_div_delta_tendsto C).pow 2).const_mul 392)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h
  rw [show (14 : ℝ) * (7040 * C / (3 * Real.pi)) = 98560 * C / (3 * Real.pi) by ring] at h
  convert h using 1
  funext t
  unfold cost
  ring

end
end RiemannGaussian.ZetaVinogradovBalancedBudget
