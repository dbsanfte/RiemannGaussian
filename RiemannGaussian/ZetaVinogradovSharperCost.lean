/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovSharperScale
import RiemannGaussian.ZetaVinogradovSharperDisc
import RiemannGaussian.ZetaAngularDiscBudget
import RiemannGaussian.ZetaVinogradovBalancedBudget

/-!
# The stronger actual VK growth pays a larger zero-free coefficient

The shorter-moment bounds discharge both actual analytic discs. Their
complete signed cost, including the unchanged leading Euler-center
logarithm, has exact limit 38080*C/(3*pi). No arithmetic or analytic
payment is assumed in the resulting actual-zero margin.
-/

namespace RiemannGaussian.ZetaVinogradovSharperCost
noncomputable section
open Filter VinogradovSharperBudget VinogradovScaleSelection ZetaVinogradovSharperScale
open ZetaVinogradovBalancedScale (width level level_atTop level_double_ratio width_tendsto_zero)
open ZetaNearOneBudgetLimit (scale scale_pos scale_double_div)
open ZetaVinogradovSharperDisc (profile)
open ZetaVinogradovBalancedBudget (center_log_normalized)
open scoped Topology

/-- The complete logarithmic cost at the original Euler-side center. -/
def allowance (n : ℕ) (x t : ℝ) : ℝ := profile n t + Real.log (1 + 1 / x)

/-- Both actual profiles enter the common signed numerical detector. -/
def budget (n : ℕ) (x t : ℝ) : ℝ :=
  ZetaAngularDiscBudget.budget (delta n) (profile n t) (profile n (2 * t)) x

/-- Both disc hypotheses of the generic signed detector are discharged
by the actual stronger zeta bound on the original height window. -/
theorem margin_of_budget (n : ℕ) (hn : 48 ≤ n) (ρ : NontrivialZetaZero)
    (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|) {d : ℝ} (hd : 0 < d)
    (hdsmall : d < delta n / 28)
    (hpay : 14 * d * budget n (6 * d) ρ.1.im + 392 * d ^ 2 / (delta n) ^ 2 < 1) :
    d < 1 - ρ.1.re := by
  have hx : 0 < 6 * d := by positivity
  have hx' : 6 * d ≤ delta n / 4 := by linarith
  have ht₂ : (heightThreshold n : ℝ) + 1 ≤ |2 * ρ.1.im| := by
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg ρ.1.im]
  exact ZetaAngularDiscBudget.margin_of_budget ρ (delta_pos n)
    ((delta_le n).trans (by norm_num)) hd hdsmall
    (ZetaVinogradovSharperDisc.analyticOnNhd_translated n hn ht hx hx')
    (fun _ hz ↦ ZetaVinogradovSharperDisc.norm_translated_le n hn ht hx hx' hz)
    (ZetaVinogradovSharperDisc.analyticOnNhd_translated n hn ht₂ hx hx')
    (fun _ hz ↦ ZetaVinogradovSharperDisc.norm_translated_le n hn ht₂ hx hx' hz) hpay

/-- The complete original contradiction cost at the proposed VK width. -/
def cost (C t : ℝ) : ℝ :=
  14 * width C t * budget (order t) (6 * width C t) t +
    392 * (width C t) ^ 2 / (delta (order t)) ^ 2

/-- The actual profile at the original height costs five second logarithms. -/
theorem profile_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) t / level t) atTop (𝓝 5) := by
  have h := ((level_atTop.const_div_atTop (Real.log 8192)).add growth_normalized).add
    (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num only [zero_add, show (4 : ℝ) + 1 = 5 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  change Real.log 8192 / level t + growth (order t) * scale t / level t + 1 =
    (Real.log 8192 + growth (order t) * scale t + level t) / level t
  field_simp

/-- The doubled evaluation uses the same natural order and has the
same leading cost, rather than paying a factor-two height majorant. -/
theorem profile_double_normalized :
    Tendsto (fun t : ℝ ↦ profile (order t) (2 * t) / level t) atTop (𝓝 5) := by
  have hg := growth_normalized.mul scale_double_div
  simp only [mul_one] at hg
  have h := ((level_atTop.const_div_atTop (Real.log 8192)).add hg).add level_double_ratio
  norm_num only [zero_add, show (4 : ℝ) + 1 = 5 by norm_num] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  have hL := scale_pos t
  change Real.log 8192 / level t +
    (growth (order t) * scale t / level t) * (scale (2 * t) / scale t) +
      level (2 * t) / level t =
    (Real.log 8192 + growth (order t) * scale (2 * t) + level (2 * t)) / level t
  field_simp

/-- Both actual allowances retain the full profile and Euler-center
cost, with the identical moving degree at the two oscillatory heights. -/
theorem allowance_normalized {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) t / level t)
      atTop (𝓝 (17 / 3 : ℝ)) ∧
    Tendsto (fun t : ℝ ↦ allowance (order t) (6 * width C t) (2 * t) / level t)
      atTop (𝓝 (17 / 3 : ℝ)) := by
  have h₁ := profile_normalized.add (center_log_normalized hC)
  have h₂ := profile_double_normalized.add (center_log_normalized hC)
  norm_num only [show (5 : ℝ) + 2 / 3 = 17 / 3 by norm_num] at h₁ h₂
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
      atTop (𝓝 (2720 * C / (3 * Real.pi))) := by
  obtain ⟨h₁, h₂⟩ := allowance_normalized hC
  have h := ((width_tendsto_zero C).const_mul (1344 * localZetaLogHeight 0)).add
    (((width_mul_level_div_delta C).mul ((h₁.const_mul 8).add (h₂.const_mul 2))).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  rw [show (16 * C) * (8 * (17 / 3 : ℝ) + 2 * (17 / 3)) / Real.pi =
    2720 * C / (3 * Real.pi) by ring] at h
  apply h.congr'
  filter_upwards [level_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  unfold budget ZetaAngularDiscBudget.budget allowance
  field_simp

/-- The entire signed cost has exact limit 38080*C/(3*pi); every
moving-radius correction vanishes on the same natural degree schedule. -/
theorem cost_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (cost C) atTop (𝓝 (38080 * C / (3 * Real.pi))) := by
  have h := ((width_mul_budget_tendsto hC).const_mul 14).add
    (((width_div_delta_tendsto C).pow 2).const_mul 392)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h
  rw [show (14 : ℝ) * (2720 * C / (3 * Real.pi)) = 38080 * C / (3 * Real.pi) by ring] at h
  convert h using 1
  funext t
  unfold cost
  ring

end
end RiemannGaussian.ZetaVinogradovSharperCost
