/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogScale

/-!
# The entire local correction on a moving-order schedule

The allowance is split exactly into its original height exponent and
the full remaining width, logarithmic height and Euler center costs.
At the joint log-log schedule, every correction vanishes after the
actual source normalization. A generic evaluation-height function is
allowed when its logarithmic height is within a fixed multiple of the
original one. No center cost or doubled-height term is omitted.
-/

namespace RiemannGaussian.ZetaLogLogCorrection
noncomputable section
open Filter ZetaLogLogScale ZetaNearOneBudgetLimit ZetaNearOneLogProfile
open ZetaNearOneJensen DerivativeOrderComparison DerivativePowerExponents
open scoped Topology

/-- All terms left after the original leading height exponent, with
the exact moving center cost retained. -/
def correction (k : ℕ) (x t : ℝ) : ℝ :=
  Real.log (32768 / delta k) + 14 + level t + Real.log (1 + 1 / x)

/-- The local allowance retains its exact leading/correction identity
before any bound or height limit is applied. -/
theorem allowance_eq (k : ℕ) (x t : ℝ) :
    allowance k x t = alpha k * scale t + correction k x t := by
  unfold allowance profile correction level scale
  ring

/-- The full logarithmic width cost is nonnegative at every order. -/
theorem log_width_nonneg (k : ℕ) : 0 ≤ Real.log (32768 / delta k) := by
  apply Real.log_nonneg
  apply (one_le_div (delta_pos k)).mpr
  linarith [LogLogDerivativeSchedule.delta_le_one k]

/-- The complete correction has nonnegative terms at positive second
logarithmic height and a positive Euler-side shift. -/
theorem correction_nonneg (k : ℕ) {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ level t) :
    0 ≤ correction k x t := by
  have hi : 0 ≤ 1 / x := by positivity
  have hc : 0 ≤ Real.log (1 + 1 / x) := Real.log_nonneg (by linarith)
  unfold correction
  linarith [log_width_nonneg k]

/-- The entire moving Euler center logarithm has an explicit bound
linear in the second logarithm. The positive coefficient is fixed. -/
theorem center_log_le {C t : ℝ} (hC : 0 < C) (hL : 1 ≤ scale t) (hq : 1 ≤ level t) :
    Real.log (1 + 1 / (6 * width C t)) ≤
      Real.log (1 + 1 / (6 * C)) + level t := by
  have hw := width_pos hC (by linarith : 0 < level t)
  have hCp : 0 < 6 * C := by positivity
  have hi : 1 / (6 * width C t) ≤ scale t / (6 * C) := by
    calc
      1 / (6 * width C t) = scale t / ((6 * C) * level t) := by
        unfold width
        field_simp
      _ ≤ scale t / (6 * C) :=
        div_le_div_of_nonneg_left (scale_pos t).le hCp
          (by nlinarith : 6 * C ≤ (6 * C) * level t)
  have harg : 1 + 1 / (6 * width C t) ≤ (1 + 1 / (6 * C)) * scale t := by
    calc
      1 + 1 / (6 * width C t) ≤ scale t + scale t / (6 * C) := by linarith
      _ = (1 + 1 / (6 * C)) * scale t := by ring
  have h := Real.log_le_log (by positivity : 0 < 1 + 1 / (6 * width C t)) harg
  rw [Real.log_mul (by positivity : 1 + 1 / (6 * C) ≠ 0) (scale_pos t).ne'] at h
  exact h

/-- Any evaluation with comparable logarithmic height receives the
full uniform correction bound, keeping its height multiplier explicit. -/
theorem correction_le {b C D t v : ℝ} (hb : 0 < b) (hC : 0 < C) (hD : 0 < D)
    (hL : 1 ≤ scale t) (hq : 1 ≤ level t) (hv : scale v ≤ D * scale t) :
    correction (order b t) (6 * width C t) v ≤
      (Real.log 131072 + 14 + Real.log D + Real.log (1 + 1 / (6 * C))) +
        (LogLogDerivativeSchedule.exponent b + 2) * level t := by
  have hw := LogLogDerivativeSchedule.log_width_le hb hL
  have hc := center_log_le hC hL hq
  have hvlog := Real.log_le_log (scale_pos v) hv
  rw [Real.log_mul hD.ne' (scale_pos t).ne'] at hvlog
  change level v ≤ Real.log D + level t at hvlog
  change Real.log (32768 / delta (order b t)) ≤
    Real.log 131072 + LogLogDerivativeSchedule.exponent b * level t at hw
  unfold correction
  linarith

/-- The complete actual correction vanishes on the joint schedule
for every evaluation-height function satisfying a fixed logarithmic
comparison. The moving center and width are part of the proved estimate. -/
theorem normalized_correction_tendsto {b C D : ℝ}
    (hb : Real.log 2 < b) (hC : 0 < C) (hD : 0 < D) (v : ℝ → ℝ)
    (hv : ∀ᶠ t : ℝ in atTop, 0 ≤ level (v t) ∧ scale (v t) ≤ D * scale t) :
    Tendsto (fun t : ℝ ↦ width C t * correction (order b t) (6 * width C t) (v t) /
      delta (order b t)) atTop (𝓝 0) := by
  let K := Real.log 131072 + 14 + Real.log D + Real.log (1 + 1 / (6 * C))
  have hbpos : 0 < b := lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hb
  have hlim : Tendsto (fun t : ℝ ↦ K * (width C t / delta (order b t)) +
      (LogLogDerivativeSchedule.exponent b + 2) *
        (width C t * level t / delta (order b t))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((width_div_delta_tendsto hb C).const_mul K).add
        ((width_mul_level_div_delta_tendsto hb C).const_mul
          (LogLogDerivativeSchedule.exponent b + 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hv, level_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht hq
    have hw := width_pos hC (by linarith : 0 < level t)
    have hc := correction_nonneg (order b t) (by positivity : 0 < 6 * width C t) ht.1
    exact div_nonneg (mul_nonneg hw.le hc) (delta_pos _).le
  · filter_upwards [hv, scale_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      level_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht hL hq
    have hw := width_pos hC (by linarith : 0 < level t)
    have h := mul_le_mul_of_nonneg_left
      (correction_le hbpos hC hD hL hq ht.2)
      (div_nonneg hw.le (delta_pos (order b t)).le)
    convert h using 1
    · ring
    · dsimp [K]
      ring

end
end RiemannGaussian.ZetaLogLogCorrection
