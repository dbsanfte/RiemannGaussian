/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Tactic

/-!
# Exact full-circle averaging of a complex resolvent

The whole parameter circle can be evaluated without choosing finitely
many coefficients. For `c / (1 - u b)`, its mean is `c` when the pole is
outside the circle, and zero when it is inside. The boundary-pole case
is excluded explicitly; a totalized integral there is not used as a
mathematical average. The complex identities precede any norm estimate.
-/

open Complex Metric Real Set
namespace RiemannGaussian
noncomputable section

private lemma one_sub_mul_ne_zero {b u : ℂ} (hb : ‖b‖ < 1) (hu : ‖u‖ ≤ 1) :
    1 - u * b ≠ 0 := by
  intro h
  have he : u * b = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖u * b‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hu (norm_nonneg b)).trans_lt (by simpa using hb)
  simp [he] at hn

/-- A parameter resolvent has a genuine integrable circle trace when
its pole does not lie on the circle. -/
theorem circleIntegrable_parameterResolvent (c : ℂ) {b : ℂ} (hb : ‖b‖ ≠ 1) :
    CircleIntegrable (fun u : ℂ => c / (1 - u * b)) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  apply continuousOn_const.div (continuousOn_const.sub (continuousOn_id.mul continuousOn_const))
  intro u hu he
  have hn : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
  have heq := congrArg norm ((sub_eq_zero.mp he).symm)
  exact hb (by simpa [norm_mul, hn] using heq)

/-- An exterior parameter pole leaves the entire complex center value
unchanged under averaging. -/
theorem circleAverage_parameterResolvent_of_norm_lt (c : ℂ) {b : ℂ} (hb : ‖b‖ < 1) :
    circleAverage (fun u : ℂ => c / (1 - u * b)) 0 1 = c := by
  have hd : DifferentiableOn ℂ (fun u : ℂ => c / (1 - u * b)) (closedBall 0 1) := by
    intro u hu
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_const c).div
      ((differentiableAt_const 1).sub (differentiableAt_id.mul_const b))
      (one_sub_mul_ne_zero hb (by simpa [mem_closedBall, dist_zero_right] using hu))
  have hm : circleAverage (fun u : ℂ => c / (1 - u * b)) 0 1 = c / (1 - 0 * b) := by
    apply DiffContOnCl.circleAverage
    simpa using hd.diffContOnCl_ball (Subset.rfl : closedBall (0 : ℂ) 1 ⊆ closedBall 0 1)
  simpa using hm

/-- An interior parameter pole cancels the center value exactly. The
proof inverts the circle and applies the analytic mean-value theorem. -/
theorem circleAverage_parameterResolvent_of_one_lt_norm (c : ℂ) {b : ℂ} (hb : 1 < ‖b‖) :
    circleAverage (fun u : ℂ => c / (1 - u * b)) 0 1 = 0 := by
  have hne : ∀ u ∈ closedBall (0 : ℂ) 1, u - b ≠ 0 := by
    intro u hu he
    have hu' : ‖u‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hu
    rw [sub_eq_zero.mp he] at hu'
    linarith
  have hd : DifferentiableOn ℂ (fun u : ℂ => c * u / (u - b)) (closedBall 0 1) := by
    intro u hu
    exact (((differentiableAt_const c).mul differentiableAt_id).div
      (differentiableAt_id.sub_const b) (hne u hu)).differentiableWithinAt
  calc
    circleAverage (fun u : ℂ => c / (1 - u * b)) 0 1 =
        circleAverage (fun u : ℂ => c / (1 - u⁻¹ * b)) 0 1 :=
      circleAverage_zero_one_congr_inv.symm
    _ = circleAverage (fun u : ℂ => c * u / (u - b)) 0 1 := by
      apply circleAverage_congr_sphere
      intro u hu
      have hu' : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
      have hu0 : u ≠ 0 := by intro he; simp [he] at hu'
      field_simp
    _ = 0 := by
      have hm : circleAverage (fun u : ℂ => c * u / (u - b)) 0 1 = c * 0 / (0 - b) := by
        apply DiffContOnCl.circleAverage
        simpa using hd.diffContOnCl_ball (Subset.rfl : closedBall (0 : ℂ) 1 ⊆ closedBall 0 1)
      simpa using hm

/-- The exact complex result for every regular parameter circle. -/
theorem circleAverage_parameterResolvent (c : ℂ) {b : ℂ} (hb : ‖b‖ ≠ 1) :
    circleAverage (fun u : ℂ => c / (1 - u * b)) 0 1 =
      if ‖b‖ < 1 then c else 0 := by
  by_cases h : ‖b‖ < 1
  · rw [if_pos h, circleAverage_parameterResolvent_of_norm_lt c h]
  · rw [if_neg h, circleAverage_parameterResolvent_of_one_lt_norm c
      (lt_of_le_of_ne (le_of_not_gt h) hb.symm)]

end
end RiemannGaussian
