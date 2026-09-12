/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Continuous lower clipping of the logarithmic norm

Clipping at an arbitrary finite negative depth makes the logarithm continuous
through zero points. It majorizes the original logarithm away from zeros,
retains every sign above the chosen floor, and is monotone as that floor is
lowered. Nonnegative upper envelopes are preserved.
-/

namespace RiemannGaussian.ClippedLogNorm
noncomputable section

/-- The logarithmic norm with its negative depth clipped at `-M`. -/
def value (M : ℝ) (z : ℂ) : ℝ := Real.log (max ‖z‖ (Real.exp (-M)))

/-- The clipped logarithm is continuous even at zeros. -/
theorem continuous (M : ℝ) : Continuous (value M) := by
  apply (continuous_norm.max continuous_const).log
  intro z
  exact (lt_of_lt_of_le (Real.exp_pos _) (le_max_right ‖z‖ _)).ne'

/-- The clipping depth is a genuine lower bound at every point. -/
theorem lower (M : ℝ) (z : ℂ) : -M ≤ value M z := by
  simpa only [Real.log_exp, value] using
    Real.log_le_log (Real.exp_pos (-M)) (le_max_right ‖z‖ (Real.exp (-M)))

/-- Away from zero, clipping only raises the original logarithm. -/
theorem log_norm_le {z : ℂ} (hz : z ≠ 0) (M : ℝ) : Real.log ‖z‖ ≤ value M z :=
  Real.log_le_log (norm_pos_iff.mpr hz) (le_max_left _ _)

/-- Above the chosen floor, the original signed logarithm is unchanged. -/
theorem eq_log_norm {M : ℝ} {z : ℂ} (hz : Real.exp (-M) ≤ ‖z‖) :
    value M z = Real.log ‖z‖ := by rw [value, max_eq_left hz]

/-- Below the chosen floor, the clipped logarithm equals the explicit depth. -/
theorem eq_floor {M : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Real.exp (-M)) : value M z = -M := by
  rw [value, max_eq_right hz, Real.log_exp]

/-- Increasing the retained negative depth decreases the clipped logarithm. -/
theorem antitone_depth (z : ℂ) : Antitone (fun M => value M z) := by
  intro a b hab
  apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _))
  exact max_le_max le_rfl (Real.exp_le_exp.mpr (by linarith))

/-- A nonnegative upper envelope for the original logarithm also bounds every
nonnegative-depth clipping, including at zero points. -/
theorem upper {M L : ℝ} {z : ℂ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hz : Real.log ‖z‖ ≤ L) : value M z ≤ L := by
  rcases le_total (Real.exp (-M)) ‖z‖ with h | h
  · rwa [eq_log_norm h]
  · rw [eq_floor h]
    linarith

/-- A nonnegative weighted upper envelope is preserved without dividing by
the weight, so a vanishing projection causes no singularity. -/
theorem weighted_upper {M a C : ℝ} {z : ℂ} (hM : 0 ≤ M) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hz : a * Real.log ‖z‖ ≤ C) : a * value M z ≤ C := by
  rcases le_total (Real.exp (-M)) ‖z‖ with h | h
  · rwa [eq_log_norm h]
  · rw [eq_floor h]
    exact (mul_nonpos_of_nonneg_of_nonpos ha (by linarith)).trans hC

/-- The same retained weight gives an absolute dominator after finite clipping. -/
theorem abs_weighted_le {M a C : ℝ} {z : ℂ} (hM : 0 ≤ M) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (hC : 0 ≤ C) (hz : a * Real.log ‖z‖ ≤ C) :
    |a * value M z| ≤ C + M := by
  have hu := weighted_upper hM ha hC hz
  have hl := mul_le_mul_of_nonneg_left (lower M z) ha
  have hm := mul_le_of_le_one_left hM ha1
  rw [abs_le]
  constructor <;> nlinarith

end
end RiemannGaussian.ClippedLogNorm
