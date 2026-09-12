/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# The nonresonant phase-increment inverse

The inverse of `exp(i*delta)-1` has real part `-1/2` and imaginary part
`-cot(delta/2)/2`. Its imaginary part is increasing on `(0,2*pi)`, while
its norm is controlled by the distance to either endpoint. These facts
allow signed discrete summation by parts to retain cancellation until the
variation telescopes. All reciprocal identities require genuine zero
avoidance.

This is classical Kuzmin--Landau machinery; see Arias de Reyna,
*On Kuzmin-Landau Lemma*, https://arxiv.org/abs/2002.05982.
-/

namespace RiemannGaussian.PhaseIncrementInverse
noncomputable section

/-- The unit complex rotation with its angle measured in radians. -/
def rotation (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

/-- The literal reciprocal of a nonzero phase increment. Identities and
estimates below explicitly exclude resonant angles. -/
def inverseStep (x : ℝ) : ℂ := (rotation x - 1)⁻¹

/-- Every rotation has unit norm. -/
theorem norm_rotation (x : ℝ) : ‖rotation x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

/-- Rotation preserves addition of the original real angles. -/
theorem rotation_add (x y : ℝ) : rotation (x + y) = rotation x * rotation y := by
  simp only [rotation, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- The exact distance from a rotation to resonance. -/
theorem norm_rotation_sub_one (x : ℝ) :
    ‖rotation x - 1‖ = 2 * |Real.sin (x / 2)| := by
  rw [rotation, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The increment is genuinely nonzero strictly between adjacent
resonances. -/
theorem rotation_sub_one_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    rotation x - 1 ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotation_sub_one]
  have hs : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  positivity

private theorem inverseStep_two_mul (x : ℝ) (hx : Real.sin x ≠ 0) :
    inverseStep (2 * x) = ⟨-(1 / 2 : ℝ), -Real.cot x / 2⟩ := by
  unfold inverseStep
  apply inv_eq_of_mul_eq_one_right
  simp only [rotation, Complex.exp_ofReal_mul_I,
    Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.cot_eq_cos_div_sin]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, add_zero, sub_zero] <;>
    field_simp <;> nlinarith [Real.sin_sq_add_cos_sq x]

/-- The inverse retains a constant real part and the complete signed
cotangent channel on the nonresonant arc. -/
theorem inverseStep_eq {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    inverseStep x = ⟨-(1 / 2 : ℝ), -Real.cot (x / 2) / 2⟩ := by
  have hs : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    inverseStep_two_mul (x / 2) hs

/-- The real part is constant throughout one nonresonant arc. -/
theorem inverseStep_re {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).re = -(1 / 2 : ℝ) := by
  rw [inverseStep_eq hx]

/-- The imaginary part carries the signed cotangent variation. -/
theorem inverseStep_im {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    (inverseStep x).im = -Real.cot (x / 2) / 2 := by
  rw [inverseStep_eq hx]

/-- Cotangent decreases on its genuine interval of continuity. -/
theorem cot_antitoneOn : AntitoneOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
    (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)).mpr
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hxy)
    (show y - x ≤ Real.pi by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hs
  nlinarith

/-- The inverse increment moves monotonically along one vertical line
as the angle increases between successive resonances. -/
theorem inverseStep_im_monotoneOn :
    MonotoneOn (fun x ↦ (inverseStep x).im) (Set.Ioo 0 (2 * Real.pi)) := by
  intro x hx y hy hxy
  change (inverseStep x).im ≤ (inverseStep y).im
  rw [inverseStep_im hx, inverseStep_im hy]
  have hc := cot_antitoneOn
    (show x / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hx.1, hx.2])
    (show y / 2 ∈ Set.Ioo 0 Real.pi by constructor <;> linarith [hy.1, hy.2])
    (show x / 2 ≤ y / 2 by linarith)
  linarith

/-- A symmetric distance from resonance gives a uniform sine floor. -/
theorem sin_half_lower {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) : η / Real.pi ≤ Real.sin (x / 2) := by
  by_cases hc : x ≤ Real.pi
  · have hs := Real.mul_le_sin (show 0 ≤ x / 2 by linarith [hx.1])
      (show x / 2 ≤ Real.pi / 2 by linarith)
    have he : 2 / Real.pi * (x / 2) = x / Real.pi := by ring
    rw [he] at hs
    exact (div_le_div_of_nonneg_right hx.1 Real.pi_pos.le).trans hs
  · have hs := Real.mul_le_sin (show 0 ≤ Real.pi - x / 2 by linarith [hx.2])
      (show Real.pi - x / 2 ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hs
    have hh : η / Real.pi ≤ 2 / Real.pi * (Real.pi - x / 2) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      field_simp
      linarith [hx.2]
    exact hh.trans hs

/-- The reciprocal has an explicit bound depending only on its distance
from resonance, not on a sum length. -/
theorem norm_inverseStep_le {η x : ℝ} (hη : 0 < η)
    (hx : x ∈ Set.Icc η (2 * Real.pi - η)) :
    ‖inverseStep x‖ ≤ Real.pi / (2 * η) := by
  have hs := sin_half_lower hη hx
  have hsp : 0 < Real.sin (x / 2) := lt_of_lt_of_le (div_pos hη Real.pi_pos) hs
  rw [inverseStep, norm_inv, norm_rotation_sub_one, abs_of_pos hsp]
  have hb := one_div_le_one_div_of_le (mul_pos (by norm_num : (0 : ℝ) < 2)
    (div_pos hη Real.pi_pos)) (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  calc
    (2 * Real.sin (x / 2))⁻¹ ≤ 1 / (2 * (η / Real.pi)) := by
      simpa only [one_div] using hb
    _ = Real.pi / (2 * η) := by field_simp

end
end RiemannGaussian.PhaseIncrementInverse
