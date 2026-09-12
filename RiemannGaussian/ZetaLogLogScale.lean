/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.LogLogDerivativeSchedule
import RiemannGaussian.ZetaNearOneExclusion

/-!
# A joint log-log schedule in the actual zeta parameters

The selected derivative order grows with the actual logarithmic height.
The proposed margin is `C*log(log(abs(t)+2))/log(abs(t)+2)`. The complete
reciprocal-disc-width losses vanish along this same schedule, while the
leading logarithmic ratio tends to its exact schedule parameter.
-/

namespace RiemannGaussian.ZetaLogLogScale
noncomputable section
open Filter ZetaNearOneBudgetLimit ZetaNearOneLogProfile DerivativeOrderComparison
open scoped Topology

/-- The second logarithm of the actual smoothed height. -/
def level (t : ℝ) : ℝ := Real.log (scale t)

/-- The derivative order selected at the actual ordinate. -/
def order (b t : ℝ) : ℕ := LogLogDerivativeSchedule.index b (scale t)

/-- The proposed log-log zero margin, with its exact coefficient. -/
def width (C t : ℝ) : ℝ := C * level t / scale t

/-- The second logarithm tends to infinity with height. -/
theorem level_atTop : Tendsto level atTop atTop :=
  Real.tendsto_log_atTop.comp scale_atTop

/-- The actual selected order tends to infinity. -/
theorem order_atTop {b : ℝ} (hb : 0 < b) : Tendsto (order b) atTop atTop :=
  (LogLogDerivativeSchedule.index_atTop hb).comp scale_atTop

/-- The actual leading ratio retains its exact value under the joint
height and natural-order schedule. -/
theorem level_div_order {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ ↦ level t / ((order b t : ℝ) + 2)) atTop (𝓝 b) :=
  (LogLogDerivativeSchedule.log_div_index hb).comp scale_atTop

/-- A positive coefficient gives a positive margin whenever the second
logarithm is positive. -/
theorem width_pos {C t : ℝ} (hC : 0 < C) (ht : 0 < level t) : 0 < width C t :=
  div_pos (mul_pos hC ht) (scale_pos t)

/-- Every fixed log-log coefficient still gives a margin tending to zero. -/
theorem width_tendsto_zero (C : ℝ) : Tendsto (width C) atTop (𝓝 0) := by
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp scale_atTop).const_mul C
  simp only [Function.comp_def, id_eq, mul_zero] at h
  convert h using 1
  funext t
  unfold width level
  ring

/-- Every fixed logarithmic power is absorbed with the actual moving
radius, rather than at a separately fixed derivative order. -/
theorem pow_level_div_width_tendsto {b : ℝ} (hb : Real.log 2 < b) (n : ℕ) :
    Tendsto (fun t : ℝ ↦ level t ^ n / (scale t * delta (order b t)))
      atTop (𝓝 0) :=
  (LogLogDerivativeSchedule.pow_log_div_width_tendsto hb n).comp scale_atTop

/-- The full margin divided by the shrinking analytic width tends to
zero along the same joint schedule. -/
theorem width_div_delta_tendsto {b : ℝ} (hb : Real.log 2 < b) (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t / delta (order b t)) atTop (𝓝 0) := by
  have h := (pow_level_div_width_tendsto hb 1).const_mul C
  simp only [pow_one, mul_zero] at h
  convert h using 1
  funext t
  unfold width
  ring

/-- The margin also absorbs one further logarithmic factor in the
complete shrinking-width allowance. -/
theorem width_mul_level_div_delta_tendsto {b : ℝ} (hb : Real.log 2 < b) (C : ℝ) :
    Tendsto (fun t : ℝ ↦ width C t * level t / delta (order b t)) atTop (𝓝 0) := by
  have h := (pow_level_div_width_tendsto hb 2).const_mul C
  simp only [mul_zero] at h
  convert h using 1
  funext t
  unfold width
  ring

/-- The log-log margin is exactly the original local margin at a
height-dependent coefficient; the pointwise contradiction is unchanged. -/
theorem width_eq_margin (C t : ℝ) :
    width C t = ZetaNearOneExclusion.margin (C * level t) t := rfl

/-- The original Euler-side center shift remains exactly six times the
new margin, even though its coefficient now varies with height. -/
theorem shift_eq_six_width (C t : ℝ) : shift (C * level t) t = 6 * width C t := by
  unfold shift width
  ring

/-- Reflection preserves the entire actual schedule and margin. -/
theorem abs_invariance (b C t : ℝ) :
    level |t| = level t ∧ order b |t| = order b t ∧ width C |t| = width C t := by
  simp [level, order, width, scale, height]

end
end RiemannGaussian.ZetaLogLogScale
