/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogScale
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Ordinary log-log widths and complete-band eligibility

The ordinary width `A*log(log(H))/log(H)` is positive and antitone once
`H >= exp(exp(1))`, and tends to zero. Its coefficient is retained when
passing from the smoothed height: any strictly larger smoothed coefficient
eventually dominates the ordinary one. No fixed fractional loss is imposed.
-/

namespace RiemannGaussian.ZetaLogLogWidth
noncomputable section
open Filter ZetaNearOneBudgetLimit ZetaNearOneLogProfile
open scoped Topology

/-- The ordinary log-log margin as a function of positive height. -/
def width (A H : ℝ) : ℝ := A * Real.log (Real.log H) / Real.log H

/-- A fixed elementary height above which the width is positive and
decreasing. This is not the zero-exclusion threshold. -/
def baseHeight : ℝ := Real.exp (Real.exp 1)

/-- The elementary width threshold lies above height two. -/
theorem two_le_baseHeight : 2 ≤ baseHeight := by
  have h := Real.add_one_le_exp (Real.exp 1)
  have he : 1 < Real.exp 1 := by norm_num
  unfold baseHeight
  linarith

/-- The first logarithm is already at least `exp(1)` above the
elementary width threshold. -/
theorem log_lower {H : ℝ} (hH : baseHeight ≤ H) : Real.exp 1 ≤ Real.log H := by
  have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hH
  simpa only [baseHeight, Real.log_exp] using h

/-- Every positive coefficient gives a positive ordinary width in
the entire eligible height range. -/
theorem width_pos {A H : ℝ} (hA : 0 < A) (hH : baseHeight ≤ H) : 0 < width A H := by
  have hlog := log_lower hH
  have hp : 0 < Real.log H := (Real.exp_pos 1).trans_le hlog
  have hloglog : 1 ≤ Real.log (Real.log H) := by
    have h := Real.log_le_log (Real.exp_pos 1) hlog
    simpa only [Real.log_exp] using h
  unfold width
  exact div_pos (mul_pos hA (by linarith)) hp

/-- The ordinary width decreases on the full eligible height interval,
which allows high-zero exclusion to cover the complete lower divisor. -/
theorem width_antitone {A : ℝ} (hA : 0 ≤ A) :
    AntitoneOn (width A) (Set.Ici baseHeight) := by
  intro x hx y hy hxy
  change baseHeight ≤ x at hx
  change baseHeight ≤ y at hy
  have hxp : 0 < x := by linarith [two_le_baseHeight]
  have h := Real.log_div_self_antitoneOn (log_lower hx) (log_lower hy)
    (Real.log_le_log hxp hxy)
  have hm := mul_le_mul_of_nonneg_left h hA
  simpa only [width, mul_div_assoc] using hm

/-- Every fixed ordinary log-log coefficient gives a width tending
to zero, with no order or zero-location assumption. -/
theorem width_tendsto_zero (A : ℝ) : Tendsto (width A) atTop (𝓝 0) := by
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    Real.tendsto_log_atTop).const_mul A
  simp only [Function.comp_def, id_eq, mul_zero] at h
  convert h using 1
  funext H
  unfold width
  ring

/-- The smoothed logarithmic height has asymptotic ratio one to the
ordinary logarithm, so no fixed coefficient loss is needed. -/
theorem scale_div_log_tendsto :
    Tendsto (fun t : ℝ ↦ scale t / Real.log t) atTop (𝓝 1) := by
  have hu : Tendsto (fun t : ℝ ↦ 1 + Real.log 3 / Real.log t) atTop (𝓝 1) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (Real.tendsto_log_atTop.const_div_atTop (Real.log 3))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have hp : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    apply (one_le_div hl).mpr
    unfold scale height
    rw [abs_of_pos hp]
    exact Real.log_le_log hp (by linarith)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have hp : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have h := Real.log_le_log (by linarith : 0 < t + 2) (show t + 2 ≤ 3 * t by linarith)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hp.ne'] at h
    apply (div_le_iff₀ hl).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hl.ne']
    simpa only [scale, height, abs_of_pos hp, add_comm] using h

/-- Any strict coefficient surplus absorbs the full smoothing change
eventually. This retains the entire open coefficient range in the final
ordinary-logarithm theorem. -/
theorem eventually_le_smoothed {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∀ᶠ t : ℝ in atTop, width A t ≤ ZetaLogLogScale.width C t := by
  have hC : 0 < C := hA.trans hAC
  have hratio := scale_div_log_tendsto.eventually (gt_mem_nhds ((one_lt_div hA).mpr hAC))
  filter_upwards [hratio, eventually_ge_atTop baseHeight] with t ht hbase
  have ht2 := two_le_baseHeight.trans hbase
  have hp : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hll : 0 ≤ Real.log (Real.log t) :=
    Real.log_nonneg (by linarith [log_lower hbase, Real.add_one_le_exp (1 : ℝ)])
  have hs : Real.log t ≤ scale t := by
    unfold scale height
    rw [abs_of_pos hp]
    exact Real.log_le_log hp (by linarith)
  have hq := Real.log_le_log hl hs
  have hcross : A * scale t ≤ C * Real.log t := by
    have h := (div_lt_div_iff₀ hl hA).mp ht
    nlinarith
  unfold width ZetaLogLogScale.width
  apply (div_le_div_iff₀ hl (scale_pos t)).mpr
  calc
    A * Real.log (Real.log t) * scale t = Real.log (Real.log t) * (A * scale t) := by ring
    _ ≤ Real.log (Real.log t) * (C * Real.log t) :=
      mul_le_mul_of_nonneg_left hcross hll
    _ ≤ ZetaLogLogScale.level t * (C * Real.log t) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    _ = C * ZetaLogLogScale.level t * Real.log t := by ring

/-- Every positive log-log coefficient eventually dominates every
fixed logarithmic coefficient. This compares the actual width functions,
without a uniform threshold over coefficients. -/
theorem eventually_dominates_logarithmic {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ∀ᶠ H : ℝ in atTop, B / Real.log H < width A H := by
  have h := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hA
  filter_upwards [h.eventually (eventually_gt_atTop B), eventually_ge_atTop (2 : ℝ)] with H hH ht
  apply div_lt_div_of_pos_right hH
  exact Real.log_pos (by linarith)

end
end RiemannGaussian.ZetaLogLogWidth
