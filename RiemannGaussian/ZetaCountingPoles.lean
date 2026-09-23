/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaCountingPhase

/-!
# Exact pole contribution to the zero count

The two polynomial factors of completed xi contribute exactly pi to the
quarter-contour phase at every positive height. All arctangents and their
branch signs are evaluated before numerical rounding is considered.
-/

namespace RiemannGaussian.ZetaCountingPoles
noncomputable section
open Complex MeasureTheory
open GammaCountingPhase

/-- The literal logarithmic derivative of a linear factor with real root. -/
def pole (c : ℝ) (s : ℂ) : ℂ := (s - c)⁻¹

/-- The linear pole is integrable on the safe right vertical side. -/
theorem pole_vertical_integrable {c : ℝ} (hc : c < 3 / 2) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => pole c ((3 / 2 : ℂ) + t * I)) volume 0 T := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀ (by fun_prop)
  intro t
  apply Complex.ne_zero_of_re_pos
  simp
  linarith

/-- The linear pole is integrable on every horizontal side at nonzero height. -/
theorem pole_horizontal_integrable (c : ℝ) {T : ℝ} (hT : T ≠ 0) :
    IntervalIntegrable (fun x : ℝ => pole c ((x : ℂ) + T * I)) volume (1 / 2 : ℝ) (3 / 2) := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀ (by fun_prop)
  intro x he
  apply hT
  simpa using congrArg Complex.im he

/-- The vertical argument increment of the linear factor is an exact arctangent. -/
theorem pole_vertical (c T : ℝ) :
    (∫ t : ℝ in 0..T, (pole c ((3 / 2 : ℂ) + t * I)).re) =
      Real.arctan (T / (3 / 2 - c)) := by
  have he (t : ℝ) : (pole c ((3 / 2 : ℂ) + t * I)).re =
      (3 / 2 - c) / ((3 / 2 - c) ^ 2 + t ^ 2) := by
    simp [pole, Complex.inv_re, Complex.normSq_apply, pow_two]
  simp_rw [he]
  rw [integral_div_sq_add_sq]
  simp

/-- The horizontal argument increment keeps the exact signed endpoint difference. -/
theorem pole_horizontal (c T : ℝ) :
    (∫ x : ℝ in (1 / 2 : ℝ)..(3 / 2), (pole c ((x : ℂ) + T * I)).im) =
      -(Real.arctan ((3 / 2 - c) / T) - Real.arctan ((1 / 2 - c) / T)) := by
  have he (x : ℝ) : (pole c ((x : ℂ) + T * I)).im =
      -(T / (T ^ 2 + (x - c) ^ 2)) := by
    simp [pole, Complex.inv_im, Complex.normSq_apply, pow_two, add_comm, neg_div]
  simp_rw [he, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_sub_right
    (fun x : ℝ => T / (T ^ 2 + x ^ 2)), integral_div_sq_add_sq]

/-- Exact quarter-contour increment of one linear factor, with its right
endpoint positive and its horizontal side above the real axis. -/
theorem pole_path {c T : ℝ} (hc : c < 3 / 2) (hT : 0 < T) :
    pathPhase (pole c) T = Real.pi / 2 - Real.arctan ((1 / 2 - c) / T) := by
  rw [pathPhase, pole_vertical, pole_horizontal]
  have hh := Real.arctan_inv_of_pos (div_pos hT (sub_pos.mpr hc))
  rw [inv_div] at hh
  rw [hh]
  ring

/-- Both elementary factors in the actual completed-xi logarithmic derivative. -/
def poles (s : ℂ) : ℂ := pole 0 s + pole 1 s

/-- The whole pole contribution is integrable on the vertical segment. -/
theorem poles_vertical_integrable (T : ℝ) :
    IntervalIntegrable (fun t : ℝ => poles ((3 / 2 : ℂ) + t * I)) volume 0 T :=
  (pole_vertical_integrable (by norm_num : (0 : ℝ) < 3 / 2) T).add
    (pole_vertical_integrable (by norm_num : (1 : ℝ) < 3 / 2) T)

/-- The whole pole contribution is integrable on the horizontal segment. -/
theorem poles_horizontal_integrable {T : ℝ} (hT : T ≠ 0) :
    IntervalIntegrable (fun x : ℝ => poles ((x : ℂ) + T * I)) volume (1 / 2 : ℝ) (3 / 2) :=
  (pole_horizontal_integrable 0 hT).add (pole_horizontal_integrable 1 hT)

/-- The pole contribution to the complete zero-count phase is exactly pi. -/
theorem poles_path {T : ℝ} (hT : 0 < T) : pathPhase poles T = Real.pi := by
  unfold poles
  rw [pathPhase_add T (pole_vertical_integrable (by norm_num : (0 : ℝ) < 3 / 2) T)
    (pole_horizontal_integrable 0 hT.ne')
    (pole_vertical_integrable (by norm_num : (1 : ℝ) < 3 / 2) T)
    (pole_horizontal_integrable 1 hT.ne'),
    pole_path (by norm_num : (0 : ℝ) < 3 / 2) hT,
    pole_path (by norm_num : (1 : ℝ) < 3 / 2) hT]
  norm_num
  rw [neg_div, Real.arctan_neg]
  ring

end
end RiemannGaussian.ZetaCountingPoles
