/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogCorrection
import RiemannGaussian.ZetaAngularPrimeBudget

/-!
# The complete prime budget at a growing derivative order

The exact leading/correction split is evaluated along one joint height,
order and center schedule. Both oscillatory heights and the real-axis
cost are included. The entire normalized contradiction allowance tends
to `140*C*b/pi`; no fixed-order asymptotic is used at a moving order.
-/

namespace RiemannGaussian.ZetaLogLogBudget
noncomputable section
open Filter ZetaLogLogScale ZetaLogLogCorrection ZetaNearOneBudgetLimit
open ZetaAngularPrimeBudget ZetaNearOneJensen ZetaNearOneLogProfile
open DerivativeOrderComparison DerivativePowerExponents
open scoped Topology

/-- Doubling the actual ordinate has a bounded additive logarithmic
cost and never decreases either logarithmic height. -/
theorem scale_double_bounds (t : ℝ) :
    scale t ≤ scale (2 * t) ∧ scale (2 * t) ≤ 2 * scale t := by
  have hl : Real.log 2 ≤ scale t := Real.log_le_log (by norm_num) (two_le_height t)
  have hlo : height t ≤ height (2 * t) := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hhi : height (2 * t) ≤ 2 * height t := by
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have h := Real.log_le_log (by linarith [two_le_height (2 * t)] : 0 < height (2 * t)) hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by linarith [two_le_height t] : height t ≠ 0)] at h
  refine ⟨Real.log_le_log (by linarith [two_le_height t]) hlo, ?_⟩
  change scale (2 * t) ≤ Real.log 2 + scale t at h
  linarith

/-- The original leading height term has an exact two-height identity
with its natural derivative order and center normalization retained. -/
theorem leading_identity (b C t v : ℝ) :
    width C t * (alpha (order b t) * scale v) / delta (order b t) =
      C * (level t / ((order b t : ℝ) + 2)) * (scale v / scale t) := by
  have ha := alpha_pos (order b t)
  unfold width delta
  field_simp

/-- The full allowance has its exact leading limit at any comparable
evaluation-height function with a proved logarithmic ratio. The complete
moving center and canonical correction have already been controlled. -/
theorem normalized_allowance_tendsto {b C D q : ℝ}
    (hb : Real.log 2 < b) (hC : 0 < C) (hD : 0 < D) (v : ℝ → ℝ)
    (hv : ∀ᶠ t : ℝ in atTop, 0 ≤ level (v t) ∧ scale (v t) ≤ D * scale t)
    (hratio : Tendsto (fun t : ℝ ↦ scale (v t) / scale t) atTop (𝓝 q)) :
    Tendsto (fun t : ℝ ↦ width C t * allowance (order b t) (6 * width C t) (v t) /
      delta (order b t)) atTop (𝓝 (C * b * q)) := by
  have hbpos : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hmain := ((level_div_order hbpos).const_mul C).mul hratio
  have herr := normalized_correction_tendsto hb hC hD v hv
  have h := hmain.add herr
  simp only [add_zero] at h
  convert h using 1
  funext t
  rw [allowance_eq, ← leading_identity]
  ring

/-- The full actual prime budget, including the real-axis pole
allowance and doubled oscillatory height, has its joint-order limit. -/
theorem width_mul_budget_tendsto {b C : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ width C t * budget (order b t) (6 * width C t) t)
      atTop (𝓝 (10 * C * b / Real.pi)) := by
  have hsame : ∀ᶠ t : ℝ in atTop, 0 ≤ level t ∧ scale t ≤ 1 * scale t := by
    filter_upwards [level_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with t ht
    exact ⟨ht, by simp⟩
  have hratio : Tendsto (fun t : ℝ ↦ scale t / scale t) atTop (𝓝 1) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)) using 1
    funext t
    exact div_self (scale_pos t).ne'
  have h1 := normalized_allowance_tendsto hb hC (by norm_num : (0 : ℝ) < 1)
    (fun t ↦ t) hsame hratio
  have hdouble : ∀ᶠ t : ℝ in atTop, 0 ≤ level (2 * t) ∧ scale (2 * t) ≤ 2 * scale t := by
    filter_upwards [level_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with t ht
    have hl := Real.log_le_log (scale_pos t) (scale_double_bounds t).1
    exact ⟨ht.trans hl, (scale_double_bounds t).2⟩
  have h2 := normalized_allowance_tendsto hb hC (by norm_num : (0 : ℝ) < 2)
    (fun t ↦ 2 * t) hdouble scale_double_div
  simp only [mul_one] at h1 h2
  have h := ((width_tendsto_zero C).const_mul (1344 * localZetaLogHeight 0)).add
    (((h1.const_mul 8).add (h2.const_mul 2)).div_const Real.pi)
  simp only [mul_zero, zero_add] at h
  have he : 8 * (C * b) + 2 * (C * b) = 10 * C * b := by ring
  rw [he] at h
  convert h using 1
  funext t
  unfold budget
  ring

/-- The signed-angular contradiction cost has an actual moving-order
limit. The canonical radial loss vanishes along the same schedule. -/
theorem cost_tendsto {b C : ℝ} (hb : Real.log 2 < b) (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ ZetaAngularPrimeBudget.cost (order b t) (C * level t) t)
      atTop (𝓝 (140 * C * b / Real.pi)) := by
  have h := ((width_mul_budget_tendsto hb hC).const_mul 14).add
    (((width_div_delta_tendsto hb C).pow 2).const_mul 392)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h
  have he : 14 * (10 * C * b / Real.pi) = 140 * C * b / Real.pi := by ring
  rw [he] at h
  convert h using 1
  funext t
  unfold ZetaAngularPrimeBudget.cost
  rw [← width_eq_margin, shift_eq_six_width]
  ring

end
end RiemannGaussian.ZetaLogLogBudget
