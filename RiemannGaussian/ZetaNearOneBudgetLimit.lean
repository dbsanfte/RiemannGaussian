/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOnePhaseConstraint

/-!
# The complete fixed-order prime budget at logarithmic shifts

For each positive target coefficient, the Euler-side shift is exactly
six times that coefficient divided by the logarithmic height. The full
center allowance is included. At every fixed derivative order, the actual
three-height budget divided by logarithmic height tends to `40/(k+2)`.
This statement does not exchange the height and derivative-order limits.
-/

namespace RiemannGaussian.ZetaNearOneBudgetLimit
noncomputable section
open Filter ZetaNearOneLogProfile ZetaNearOneJensen ZetaNearOnePhaseConstraint
open DerivativeOrderComparison DirichletPowerParameters DerivativePowerExponents
open scoped Topology

/-- A strictly positive logarithmic height at every real ordinate. -/
def scale (t : ℝ) : ℝ := Real.log (height t)

/-- The center shift for an arbitrary positive target coefficient. -/
def shift (C t : ℝ) : ℝ := 6 * C / scale t

/-- The logarithmic height never vanishes. -/
theorem scale_pos (t : ℝ) : 0 < scale t :=
  Real.log_pos (by linarith [two_le_height t])

/-- The actual logarithmic height tends to infinity. -/
theorem scale_atTop : Tendsto scale atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_atTop_mono (fun t : ℝ ↦ show t ≤ |t| + 2 by linarith [le_abs_self t]) tendsto_id)

/-- The logarithmic shift is positive at every ordinate. -/
theorem shift_pos {C : ℝ} (hC : 0 < C) (t : ℝ) : 0 < shift C t := by
  unfold shift
  exact div_pos (by positivity) (scale_pos t)

/-- Every fixed-coefficient center shift tends to zero. -/
theorem shift_tendsto_zero (C : ℝ) : Tendsto (shift C) atTop (𝓝 0) :=
  scale_atTop.const_div_atTop (6 * C)

/-- Doubling the height has no leading logarithmic cost. -/
theorem scale_double_div :
    Tendsto (fun t : ℝ ↦ scale (2 * t) / scale t) atTop (𝓝 1) := by
  have hu : Tendsto (fun t : ℝ ↦ 1 + Real.log 2 / scale t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (scale_atTop.const_div_atTop (Real.log 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro t
    apply (one_le_div (scale_pos t)).mpr
    apply Real.log_le_log (by linarith [two_le_height t])
    simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  · intro t
    have hh : height (2 * t) ≤ 2 * height t := by
      simp only [height, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hb := Real.log_le_log (by linarith [two_le_height (2 * t)]) hh
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (ne_of_gt (by linarith [two_le_height t] : 0 < height t))] at hb
    apply (div_le_iff₀ (scale_pos t)).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ (scale_pos t).ne']
    simpa only [scale, add_comm] using hb

/-- The complete logarithmic profile retains its exact leading
fixed-order exponent. -/
theorem profile_div_scale (k : ℕ) :
    Tendsto (fun t : ℝ ↦ profile k t / scale t) atTop (𝓝 (alpha k)) := by
  have hlog : Tendsto (fun t : ℝ ↦ Real.log (scale t) / scale t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp scale_atTop
  have hc := scale_atTop.const_div_atTop (Real.log (32768 / delta k))
  have h := (hc.add (tendsto_const_nhds (x := alpha k))).add hlog
  simp only [zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [] with t
  have hs : Real.log (height t) ≠ 0 := (scale_pos t).ne'
  unfold profile scale
  field_simp [hs]

/-- The doubled-height profile has the same leading coefficient when
normalized at the original height. -/
theorem profile_double_div_scale (k : ℕ) :
    Tendsto (fun t : ℝ ↦ profile k (2 * t) / scale t) atTop (𝓝 (alpha k)) := by
  have hp := (profile_div_scale k).comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := hp.mul scale_double_div
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [] with t
  simp only [Function.comp_def, id_eq]
  field_simp [(scale_pos t).ne', (scale_pos (2 * t)).ne']

/-- The full Euler center cost is lower order at every fixed positive
logarithmic-shift coefficient. -/
theorem center_cost_div_scale {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ Real.log (1 + 1 / shift C t) / scale t) atTop (𝓝 0) := by
  let u : ℝ → ℝ := fun t ↦ 1 + scale t / (6 * C)
  have hu : Tendsto u atTop atTop := by
    have hb := scale_atTop.atTop_div_const (show 0 < 6 * C by positivity)
    simpa only [u, add_comm] using hb.atTop_add (tendsto_const_nhds (x := 1))
  have hl : Tendsto (fun t ↦ Real.log (u t) / u t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  have hr : Tendsto (fun t ↦ u t / scale t) atTop (𝓝 (1 / (6 * C))) := by
    have hh := (scale_atTop.const_div_atTop 1).add (tendsto_const_nhds (x := 1 / (6 * C)))
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [] with t
    dsimp [u]
    field_simp [(scale_pos t).ne']
  have h := hl.mul hr
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [] with t
  have hst := scale_pos t
  have hup : 0 < u t := by dsimp [u]; positivity
  have he : 1 + 1 / shift C t = u t := by
    unfold shift u
    field_simp
  rw [he]
  field_simp [hup.ne', (scale_pos t).ne']

/-- The complete local allowance, including the moving Euler center,
has the original fixed-order leading coefficient. -/
theorem allowance_div_scale (k : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ allowance k (shift C t) t / scale t)
      atTop (𝓝 (alpha k)) := by
  have h := ((profile_div_scale k).add (scale_atTop.const_div_atTop 14)).add
    (center_cost_div_scale hC)
  simp only [add_zero] at h
  convert h using 1
  funext t
  unfold allowance
  ring

/-- At the doubled ordinate the original moving center cost remains
lower order; the center shift is not silently changed. -/
theorem allowance_double_div_scale (k : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ allowance k (shift C t) (2 * t) / scale t)
      atTop (𝓝 (alpha k)) := by
  have h := ((profile_double_div_scale k).add (scale_atTop.const_div_atTop 14)).add
    (center_cost_div_scale hC)
  simp only [add_zero] at h
  convert h using 1
  funext t
  unfold allowance
  ring

/-- The full actual prime budget has leading coefficient `40/(k+2)`
for every fixed derivative order and positive target coefficient. -/
theorem budget_div_scale (k : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun t : ℝ ↦ budget k (shift C t) t / scale t)
      atTop (𝓝 (40 / ((k : ℝ) + 2))) := by
  have h := (scale_atTop.const_div_atTop (1344 * localZetaLogHeight 0)).add
    ((((allowance_div_scale k hC).const_mul 32).add
      ((allowance_double_div_scale k hC).const_mul 8)).div_const (delta k))
  have he : (0 : ℝ) + (32 * alpha k + 8 * alpha k) / delta k = 40 / ((k : ℝ) + 2) := by
    unfold delta
    field_simp [(alpha_pos k).ne']
    ring
  rw [he] at h
  convert h using 1
  funext t
  unfold budget
  ring

/-- Reflection of the ordinate leaves the actual scale and budget
unchanged, with the doubled height transformed at the same time. -/
theorem budget_abs (k : ℕ) (x t : ℝ) : budget k x |t| = budget k x t := by
  simp [budget, allowance, profile, height, abs_mul]

end
end RiemannGaussian.ZetaNearOneBudgetLimit
