/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Opposite bounds on the two signed angular channels

The positive and negative real-coordinate projections of a radius-R
circle each have average R/pi. Consequently a signed first moment uses
an upper bound on the left semicircle and a lower bound on the right.
No absolute bound on the full boundary function is required.
-/

namespace RiemannGaussian.SignedCircleProjection
noncomputable section
open Complex Metric Real Set MeasureTheory

/-- The positive sine channel has exact mass two over a full period. -/
theorem integral_positive_sine :
    (∫ θ : ℝ in 0..2 * Real.pi, max (Real.sin θ) 0) = 2 := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun θ ↦ max (Real.sin θ) 0) volume a b :=
    fun a b ↦ (Real.continuous_sin.max continuous_const).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi (2 * Real.pi))]
  have hfirst : (∫ θ : ℝ in 0..Real.pi, max (Real.sin θ) 0) = 2 := by
    calc
      _ = ∫ θ : ℝ in 0..Real.pi, Real.sin θ := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le Real.pi_pos.le] at hθ
        exact max_eq_left (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)
      _ = 2 := by rw [integral_sin]; norm_num
  have hsecond : (∫ θ : ℝ in Real.pi..2 * Real.pi, max (Real.sin θ) 0) = 0 := by
    calc
      _ = ∫ _θ : ℝ in Real.pi..2 * Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi)] at hθ
        rcases hθ with ⟨hθlo, hθhi⟩
        have hs := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith : 0 ≤ θ - Real.pi) (by linarith : θ - Real.pi ≤ Real.pi)
        have he : Real.sin θ = -Real.sin (θ - Real.pi) := by
          rw [← Real.sin_add_pi (θ - Real.pi), sub_add_cancel]
        exact max_eq_right (by rw [he]; linarith)
      _ = 0 := by simp
  rw [hfirst, hsecond, add_zero]

/-- The positive real projection of every nonnegative-radius circle
has exact average R/pi. -/
theorem average_positive_re {R : ℝ} (hR : 0 ≤ R) :
    Real.circleAverage (fun z : ℂ ↦ max z.re 0) 0 R = R / Real.pi := by
  rw [Real.circleAverage_eq_integral_add (-(Real.pi / 2))]
  have he (θ : ℝ) : max (circleMap 0 R (θ + -(Real.pi / 2))).re 0 =
      R * max (Real.sin θ) 0 := by
    simp [circleMap, Complex.exp_re, ← sub_eq_add_neg, Real.cos_sub_pi_div_two,
      mul_max_of_nonneg _ _ hR]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_positive_sine]
  simp only [smul_eq_mul]
  field_simp

/-- The full signed real projection has zero circle average. -/
theorem average_re (R : ℝ) : Real.circleAverage (fun z : ℂ ↦ z.re) 0 R = 0 := by
  simp [Real.circleAverage_def, circleMap, intervalIntegral.integral_const_mul, integral_cos]

/-- The negative real projection has the same exact mass as the
positive channel, without taking the modulus of their original sum. -/
theorem average_negative_re {R : ℝ} (hR : 0 ≤ R) :
    Real.circleAverage (fun z : ℂ ↦ max (-z.re) 0) 0 R = R / Real.pi := by
  have he (z : ℂ) : max (-z.re) 0 = max z.re 0 - z.re := by
    by_cases hz : 0 ≤ z.re
    · rw [max_eq_right (neg_nonpos.mpr hz), max_eq_left hz, sub_self]
    · rw [max_eq_left (by linarith : 0 ≤ -z.re), max_eq_right (by linarith : z.re ≤ 0), zero_sub]
  simp_rw [he]
  rw [Real.circleAverage_fun_sub
    (ContinuousOn.circleIntegrable hR (Complex.continuous_re.max continuous_const).continuousOn)
    (ContinuousOn.circleIntegrable hR Complex.continuous_re.continuousOn),
    average_positive_re hR, average_re, sub_zero]

/-- Opposite one-sided bounds suffice for a signed boundary moment:
the left semicircle uses an upper bound and the right a lower bound. -/
theorem signed_average_le {F : ℂ → ℝ} {R B C : ℝ} (hR : 0 ≤ R)
    (hF : CircleIntegrable F 0 R)
    (hleft : ∀ z ∈ sphere 0 R, z.re ≤ 0 → F z ≤ B)
    (hright : ∀ z ∈ sphere 0 R, 0 ≤ z.re → -F z ≤ C) :
    Real.circleAverage (fun z : ℂ ↦ -z.re * F z) 0 R ≤ (B + C) * R / Real.pi := by
  have hmain : CircleIntegrable (fun z : ℂ ↦ -z.re * F z) 0 R :=
    hF.continuousOn_mul (by fun_prop)
  have hl : CircleIntegrable (fun z : ℂ ↦ B * max (-z.re) 0) 0 R :=
    ContinuousOn.circleIntegrable hR (by fun_prop)
  have hr : CircleIntegrable (fun z : ℂ ↦ C * max z.re 0) 0 R :=
    ContinuousOn.circleIntegrable hR (by fun_prop)
  have hb := Real.circleAverage_mono hmain (hl.add hr) (fun z hz ↦ by
    rw [abs_of_nonneg hR] at hz
    dsimp only [Pi.add_apply]
    by_cases h : 0 ≤ z.re
    · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h, mul_zero, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left (hright z hz h) h]
    · rw [max_eq_left (by linarith : 0 ≤ -z.re), max_eq_right (by linarith : z.re ≤ 0),
        mul_zero, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left (hleft z hz (by linarith)) (by linarith : 0 ≤ -z.re)])
  apply hb.trans_eq
  rw [Real.circleAverage_add hl hr]
  simp_rw [← smul_eq_mul, Real.circleAverage_fun_smul, smul_eq_mul]
  rw [average_negative_re hR, average_positive_re hR]
  ring

end
end RiemannGaussian.SignedCircleProjection
