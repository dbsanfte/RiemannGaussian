/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Phase-preserving inversion of a complex error disk

A closed disk with center `a` and radius `e < ‖a‖` inverts into the disk
with center `conj a / (normSq a - e²)` and radius
`e / (normSq a - e²)`. The exact squared-gap identity precedes the
estimate. Multiplication by an arbitrary complex numerator retains its
phase and therefore gives a signed real-part error, not just a norm bound.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- The exact gap identity behind inversion of a complex disk. No sign
or nonvanishing assumptions are needed for this polynomial identity. -/
theorem normSq_inverse_disk_gap (a z : ℂ) (e : ℝ) :
    normSq (((normSq a - e ^ 2 : ℝ) : ℂ) - starRingEnd ℂ a * z) - e ^ 2 * normSq z =
      (normSq a - e ^ 2) * (normSq (z - a) - e ^ 2) := by
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im,
    conj_re, conj_im]
  ring

/-- Inversion preserves the full error disk, with the shifted center
and exact image radius. The input disk must avoid zero. -/
theorem norm_inv_sub_inverse_disk_center_le {a z : ℂ} {e : ℝ}
    (he : 0 ≤ e) (ha : e < ‖a‖) (hz : ‖z - a‖ ≤ e) :
    ‖z⁻¹ - starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ)‖ ≤
      e / (normSq a - e ^ 2) := by
  have hD : 0 < normSq a - e ^ 2 := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hz
    exact (ha.trans_le hz).false
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hDc : ((normSq a - e ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD.ne'
  have hsq : normSq (z - a) ≤ e ^ 2 := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z - a)]
  have hgap := normSq_inverse_disk_gap a z e
  have hprod := mul_nonpos_of_nonneg_of_nonpos hD.le (sub_nonpos.mpr hsq)
  have hnum : ‖((normSq a - e ^ 2 : ℝ) : ℂ) - starRingEnd ℂ a * z‖ ≤ e * ‖z‖ := by
    rw [normSq_eq_norm_sq (((normSq a - e ^ 2 : ℝ) : ℂ) - starRingEnd ℂ a * z),
      normSq_eq_norm_sq z] at hgap
    nlinarith [norm_nonneg (((normSq a - e ^ 2 : ℝ) : ℂ) - starRingEnd ℂ a * z),
      mul_nonneg he hnz.le]
  have hid : z⁻¹ - starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ) =
      (((normSq a - e ^ 2 : ℝ) : ℂ) - starRingEnd ℂ a * z) /
        (z * ((normSq a - e ^ 2 : ℝ) : ℂ)) := by
    field_simp
  rw [hid, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hD]
  calc
    _ ≤ (e * ‖z‖) / (‖z‖ * (normSq a - e ^ 2)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hnz hD).le
    _ = _ := by field_simp

/-- An arbitrary complex numerator transports the entire inverse disk.
Its phase remains in the center; only the error radius uses its norm. -/
theorem norm_div_sub_inverse_disk_center_le (b : ℂ) {a z : ℂ} {e : ℝ}
    (he : 0 ≤ e) (ha : e < ‖a‖) (hz : ‖z - a‖ ≤ e) :
    ‖b / z - b * starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ)‖ ≤
      ‖b‖ * e / (normSq a - e ^ 2) := by
  have h := mul_le_mul_of_nonneg_left
    (norm_inv_sub_inverse_disk_center_le he ha hz) (norm_nonneg b)
  have hid : b / z - b * starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ) =
      b * (z⁻¹ - starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ)) := by ring
  rw [hid, norm_mul]
  exact h.trans_eq (by ring)

/-- The real part of a complex quotient has a signed enclosure centered
at the retained numerator--slope phase. This allows cancellation between
different quotients before estimating the combined signed contribution. -/
theorem abs_re_div_sub_inverse_disk_center_le (b : ℂ) {a z : ℂ} {e : ℝ}
    (he : 0 ≤ e) (ha : e < ‖a‖) (hz : ‖z - a‖ ≤ e) :
    |(b / z).re - (b * starRingEnd ℂ a).re / (normSq a - e ^ 2)| ≤
      ‖b‖ * e / (normSq a - e ^ 2) := by
  have h := (Complex.abs_re_le_norm
    (b / z - b * starRingEnd ℂ a / ((normSq a - e ^ 2 : ℝ) : ℂ))).trans
      (norm_div_sub_inverse_disk_center_le b he ha hz)
  simpa only [sub_re, div_ofReal_re] using h

end
end RiemannGaussian
