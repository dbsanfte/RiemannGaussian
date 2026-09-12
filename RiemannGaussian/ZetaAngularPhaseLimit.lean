/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAngularPhaseFamily

/-!
# The complete moving-order limit for general phase families

Every fixed positive center shift has the same leading allowance. The
entire countable frequency correction tends to zero on the actual joint
order-height schedule. The limiting cost depends only on the total
nonconstant mass, while the source retains the constant and selected
coefficients separately.
-/

namespace RiemannGaussian.ZetaAngularPhaseLimit
noncomputable section
open Filter ZetaNearOneBudgetLimit ZetaNearOneJensen DerivativeOrderComparison
open ZetaLogLogScale ZetaAngularPhaseAllowance ZetaAngularPhaseFamily
open scoped Topology

/-- Every fixed positive center-to-margin ratio has the same actual
leading allowance; the complete moving center cost still vanishes. -/
theorem normalized_allowance_tendsto {b C r : ℝ}
    (hb : Real.log 2 < b) (hC : 0 < C) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ width C t * allowance (order b t) (r * width C t) t /
      delta (order b t)) atTop (𝓝 (C * b)) := by
  have hC' : 0 < r * C / 6 := by positivity
  have hv : ∀ᶠ t : ℝ in atTop, 0 ≤ level t ∧ scale t ≤ 1 * scale t := by
    filter_upwards [level_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with t ht
    exact ⟨ht, by simp⟩
  have hratio : Tendsto (fun t : ℝ ↦ scale t / scale t) atTop (𝓝 1) := by
    simpa only [div_self (scale_pos _).ne'] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1))
  have h := (ZetaLogLogBudget.normalized_allowance_tendsto hb hC'
    (by norm_num : (0 : ℝ) < 1) (fun t ↦ t) hv hratio).const_mul (6 / r)
  have hc : 6 / r * (r * C / 6 * b * 1) = C * b := by field_simp
  rw [hc] at h
  convert h using 1
  funext t
  have he : 6 * width (r * C / 6) t = r * width C t := by unfold width; ring_nf
  rw [he]
  unfold width
  field_simp

/-- The full allowance of a countable family has its actual leading
limit. The complete logarithmic frequency moment is lower order. -/
theorem normalized_totalAllowance_tendsto {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    {b C r : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ width C t * totalAllowance (order b t) (r * width C t) t a ω /
      delta (order b t)) atTop (𝓝 (mass a * (C * b))) := by
  have hlo := (normalized_allowance_tendsto hb hC hr).const_mul (mass a)
  have herr := (width_div_delta_tendsto hb C).const_mul (2 * frequencyCost a ω)
  have hhi := hlo.add herr
  simp only [mul_zero, add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      scale_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht hscale
    have hu := width_pos hC ht
    have he := totalAllowance_bounds ha hs hω hlog (order b t) (mul_pos hr hu) hscale
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he.1 hu.le)
      (delta_pos (order b t)).le
    convert h using 1
    ring_nf
  · filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      scale_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht hscale
    have hu := width_pos hC ht
    have he := totalAllowance_bounds ha hs hω hlog (order b t) (mul_pos hr hu) hscale
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he.2 hu.le)
      (delta_pos (order b t)).le
    convert h using 1
    ring_nf

/-- The complete actual prime budget includes every frequency and
its full real-axis allowance before taking the limit. -/
theorem width_mul_budget_tendsto {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    {b C r : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ width C t * budget (order b t) (r * width C t) t a ω)
      atTop (𝓝 (2 * mass a * C * b / Real.pi)) := by
  have h := ((width_tendsto_zero C).const_mul (448 * a 0 * localZetaLogHeight 0)).add
    (((normalized_totalAllowance_tendsto ha hs hω hlog hb hC hr).const_mul 2).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  · funext t
    unfold budget
    ring_nf
  · ring_nf

/-- The entire selected radial correction vanishes on the same
schedule. Only the total nonconstant mass enters the leading cost. -/
theorem cost_tendsto {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n ↦ tail a n * Real.log (ω n)))
    {b C r : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ cost (order b t) r (width C t) t a ω)
      atTop (𝓝 (2 * mass a * C * b / Real.pi)) := by
  have h := (width_mul_budget_tendsto ha hs hω hlog hb hC hr).add
    (((width_div_delta_tendsto hb C).pow 2).const_mul (a 1 * (r + 1)))
  simpa only [cost, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using h

/-- Absolute ordinate preserves the full countable allowance and
the selected radial correction at a fixed proposed margin. -/
theorem cost_abs (k : ℕ) (r u t : ℝ) (a ω : ℕ → ℝ) :
    cost k r u |t| a ω = cost k r u t a ω := by
  simp only [cost, budget, totalAllowance, allowance, ZetaNearOneLogProfile.profile,
    ZetaNearOneLogProfile.height, abs_mul, abs_abs]

end
end RiemannGaussian.ZetaAngularPhaseLimit
