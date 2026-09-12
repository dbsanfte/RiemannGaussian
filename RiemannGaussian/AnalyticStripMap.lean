/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
# The analytic coordinate from the unit disc to a vertical strip

The Cayley coordinate has strictly positive real part on the unit disc,
so its principal logarithm is analytic. The resulting arctangent map
retains the real-coordinate sign and has a nonzero derivative everywhere.
Composing with it therefore preserves the exact analytic order of every
function, including every zero multiplicity.
-/

namespace RiemannGaussian.AnalyticStripMap
noncomputable section
open Complex Metric Set
open scoped Topology

/-- The full complex Cayley coordinate used by the strip map. -/
def cayley (w : ℂ) : ℂ := (1 + w * I) / (1 - w * I)

/-- The logarithm's denominator avoids zero throughout the open unit disc. -/
theorem denominator_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w * I ≠ 0 := by
  intro h
  have h := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_one, norm_mul, norm_I, mul_one] at h
  linarith

/-- The logarithm's numerator also avoids zero throughout the unit disc. -/
theorem numerator_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 + w * I ≠ 0 := by
  have h := denominator_ne_zero (w := -w) (by simpa using hw)
  simpa only [neg_mul, sub_neg_eq_add] using h

/-- The Cayley real part retains the precise distance from the unit circle. -/
theorem cayley_re (w : ℂ) :
    (cayley w).re = (1 - normSq w) / normSq (1 - w * I) := by
  simp only [cayley, Complex.div_re, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, add_zero, sub_neg_eq_add, zero_add,
    normSq_apply]
  ring

/-- The Cayley imaginary part keeps the sign of the original real coordinate. -/
theorem cayley_im (w : ℂ) :
    (cayley w).im = 2 * w.re / normSq (1 - w * I) := by
  simp only [cayley, Complex.div_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, add_zero, sub_neg_eq_add, zero_add]
  ring

/-- The entire unit disc maps into the open right half-plane. -/
theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  rw [cayley_re]
  apply div_pos
  · rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  · exact normSq_pos.mpr (denominator_ne_zero hw)

/-- The logarithm never meets its branch cut on the unit disc. -/
theorem cayley_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) : cayley w ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (cayley_re_pos hw))

/-- The full Cayley derivative, before composing with the logarithm. -/
theorem hasDerivAt_cayley {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt cayley (2 * I / (1 - w * I) ^ 2) w := by
  have h := (((hasDerivAt_id w).mul_const I).const_add 1).div
    (((hasDerivAt_id w).mul_const I).const_sub 1) (denominator_ne_zero hw)
  convert! h using 1
  dsimp [cayley]
  congr 1
  ring

/-- The normalized arctangent real coordinate is exactly half the
argument of the Cayley coordinate, retaining its sign. -/
theorem arctan_re (w : ℂ) : (Complex.arctan w).re = (cayley w).arg / 2 := by
  simp [Complex.arctan, cayley, Complex.mul_re, Complex.log_im]
  ring

/-- The unit disc lies in the correct narrow arctangent branch strip. -/
theorem abs_arctan_re_lt {w : ℂ} (hw : ‖w‖ < 1) :
    |(Complex.arctan w).re| < Real.pi / 4 := by
  have h := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayley_re_pos hw))
  rw [arctan_re, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Nonnegative real coordinates are preserved in both directions. -/
theorem arctan_re_nonneg_iff {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).re ↔ 0 ≤ w.re := by
  rw [arctan_re, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), zero_mul,
    arg_nonneg_iff, cayley_im,
    le_div_iff₀ (normSq_pos.mpr (denominator_ne_zero hw)), zero_mul]
  constructor <;> intro h <;> linarith

/-- The arctangent derivative is the original rational derivative,
with no singularity or branch premise left inside the unit disc. -/
theorem hasDerivAt_arctan {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt Complex.arctan (1 / (1 + w ^ 2)) w := by
  have h := ((hasDerivAt_cayley hw).clog (cayley_mem_slitPlane hw)).const_mul (-I / 2)
  have hn := numerator_ne_zero hw
  have hd := denominator_ne_zero hw
  have he : (1 - w * I) * (1 + w * I) = 1 + w ^ 2 := by
    calc
      _ = 1 - w ^ 2 * I ^ 2 := by ring
      _ = _ := by simp
  have hw2 : 1 + w ^ 2 ≠ 0 := he ▸ mul_ne_zero hd hn
  convert! h using 1
  dsimp [cayley]
  field_simp
  ring_nf
  simp [add_comm]

/-- The arctangent is analytic on a neighborhood of each point of
the unit disc; the branch domain is proved pointwise. -/
theorem analyticAt_arctan {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ Complex.arctan w := by
  have h : DifferentiableOn ℂ Complex.arctan (ball 0 1) := by
    intro z hz
    exact (hasDerivAt_arctan (by simpa only [mem_ball, dist_zero_right] using hz)).differentiableAt.differentiableWithinAt
  exact h.analyticOnNhd isOpen_ball w (by simpa only [mem_ball, dist_zero_right] using hw)

/-- The physical strip coordinate with its center and half-width explicit. -/
def map (c : ℂ) (η : ℝ) (w : ℂ) : ℂ := c + (4 * (η : ℂ) / Real.pi) * Complex.arctan w

/-- The disc center is the exact physical strip center. -/
theorem map_zero (c : ℂ) (η : ℝ) : map c η 0 = c := by
  simp [map, Complex.arctan]

/-- The exact real displacement under the strip map. -/
theorem map_re_sub (c : ℂ) (η : ℝ) (w : ℂ) :
    (map c η w).re - c.re = (4 * η / Real.pi) * (Complex.arctan w).re := by
  have he : 4 * (η : ℂ) / Real.pi = ((4 * η / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  rw [map, he]
  simp

/-- Every point of the open unit disc lies strictly inside the physical strip. -/
theorem map_mem_strip (c : ℂ) {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : ‖w‖ < 1) :
    |(map c η w).re - c.re| < η := by
  rw [map_re_sub, abs_mul, abs_of_pos (by positivity : 0 < 4 * η / Real.pi)]
  have h := mul_lt_mul_of_pos_left (abs_arctan_re_lt hw)
    (by positivity : 0 < 4 * η / Real.pi)
  convert! h using 1
  field_simp

/-- The strip coordinate preserves which side of the center contains
a point. This is the sign needed by the full canonical zero source. -/
theorem map_re_lt_center_iff (c : ℂ) {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : ‖w‖ < 1) :
    (map c η w).re < c.re ↔ w.re < 0 := by
  have hn : (Complex.arctan w).re < 0 ↔ w.re < 0 :=
    lt_iff_lt_of_le_iff_le (arctan_re_nonneg_iff hw)
  have hp : 0 < 4 * η / Real.pi := by positivity
  rw [← sub_neg, map_re_sub]
  constructor
  · intro h
    apply hn.mp
    nlinarith
  · intro h
    have h' := hn.mpr h
    nlinarith

/-- The strip coordinate has an explicit tangent inverse on its whole
disc domain, not merely a local inverse at the center. -/
theorem tan_map (c : ℂ) {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.tan (Real.pi * (map c η w - c) / (4 * η)) = w := by
  have hη0 : (η : ℂ) ≠ 0 := ofReal_ne_zero.mpr hη.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : Real.pi * (map c η w - c) / (4 * η) = Complex.arctan w := by
    unfold map
    field_simp
    ring
  rw [he]
  apply Complex.tan_arctan
  · intro h
    subst w
    simp only [norm_I, lt_self_iff_false] at hw
  · intro h
    subst w
    simp only [norm_neg, norm_I, lt_self_iff_false] at hw

/-- No two points of the unit disc represent the same physical point. -/
theorem map_injOn (c : ℂ) {η : ℝ} (hη : 0 < η) : InjOn (map c η) (ball 0 1) := by
  intro w hw z hz he
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  rw [← tan_map c hη hw', he, tan_map c hη hz']

/-- The difference of the two complex trigonometric norm squares
retains exactly the real-coordinate double angle; the imaginary growth cancels. -/
theorem normSq_cos_sub_sin (z : ℂ) :
    normSq (Complex.cos z) - normSq (Complex.sin z) = Real.cos (2 * z.re) := by
  calc
    _ = (Real.cos z.re ^ 2 - Real.sin z.re ^ 2) *
        (Real.cosh z.im ^ 2 - Real.sinh z.im ^ 2) := by
      rw [Complex.cos_eq z, Complex.sin_eq z]
      simp only [normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, sin_ofReal_re, cos_ofReal_re,
        sinh_ofReal_re, cosh_ofReal_re, sin_ofReal_im, cos_ofReal_im,
        sinh_ofReal_im, cosh_ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero, mul_one]
      ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq, mul_one, Real.cos_two_mul']

/-- Every point of the normalized open strip has its tangent in the
open unit disc, including arbitrarily large imaginary ordinates. -/
theorem norm_tan_lt_one {z : ℂ} (hz : |z.re| < Real.pi / 4) : ‖Complex.tan z‖ < 1 := by
  have hc : 0 < Real.cos (2 * z.re) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_lt.mp hz).1], by linarith [(abs_lt.mp hz).2]⟩
  have hn : normSq (Complex.sin z) < normSq (Complex.cos z) := by
    linarith [normSq_cos_sub_sin z]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hn
  have hnorm : ‖Complex.sin z‖ < ‖Complex.cos z‖ := by
    nlinarith [norm_nonneg (Complex.sin z), norm_nonneg (Complex.cos z)]
  rw [Complex.tan, norm_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hnorm)).mpr hnorm

/-- Every physical strip point gives an inverse tangent argument in
the correct narrow branch strip. -/
theorem abs_inverse_argument_re_lt (c : ℂ) {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : |z.re - c.re| < η) :
    |(Real.pi * (z - c) / (4 * (η : ℂ))).re| < Real.pi / 4 := by
  let q : ℂ := Real.pi * (z - c) / (4 * η)
  change |q.re| < Real.pi / 4
  have he : q.re = Real.pi * (z.re - c.re) / (4 * η) := by
    dsimp [q]
    rw [show (4 : ℂ) * η = ((4 * η : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    simp
  rw [he, abs_div, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by positivity : 0 < 4 * η)]
  exact (div_lt_iff₀ (by positivity : 0 < 4 * η)).mpr (by nlinarith [Real.pi_pos])

/-- The explicit inverse coordinate of any strip point lies inside the
unit disc, uniformly over its unbounded imaginary coordinate. -/
theorem norm_inverse_lt_one (c : ℂ) {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : |z.re - c.re| < η) :
    ‖Complex.tan (Real.pi * (z - c) / (4 * (η : ℂ)))‖ < 1 :=
  norm_tan_lt_one (abs_inverse_argument_re_lt c hη hz)

/-- The explicit tangent coordinate maps every physical strip point
back to that same point, with the arctangent branch bounds discharged. -/
theorem map_tan (c : ℂ) {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : |z.re - c.re| < η) :
    map c η (Complex.tan (Real.pi * (z - c) / (4 * η))) = z := by
  let q : ℂ := Real.pi * (z - c) / (4 * η)
  have hq : |q.re| < Real.pi / 4 := abs_inverse_argument_re_lt c hη hz
  have he : Complex.arctan (Complex.tan q) = q := Complex.arctan_tan
    (by intro h; have hh := congrArg Complex.re h; norm_num at hh; rw [hh] at hq;
        have hp := Real.pi_pos; rw [abs_of_pos (by positivity)] at hq; linarith)
    (by linarith [(abs_lt.mp hq).1, Real.pi_pos])
    (by linarith [(abs_lt.mp hq).2, Real.pi_pos])
  change c + (4 * (η : ℂ) / Real.pi) * Complex.arctan (Complex.tan q) = z
  rw [he]
  dsimp [q]
  have hη0 : (η : ℂ) ≠ 0 := ofReal_ne_zero.mpr hη.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- The image of the entire open disc is exactly the entire vertical
strip. No finite-height portion or exceptional interior point is omitted. -/
theorem map_image (c : ℂ) {η : ℝ} (hη : 0 < η) :
    map c η '' ball 0 1 = {z : ℂ | |z.re - c.re| < η} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact map_mem_strip c hη (by simpa only [mem_ball, dist_zero_right] using hw)
  · intro hz
    refine ⟨Complex.tan (Real.pi * (z - c) / (4 * η)), ?_, map_tan c hη hz⟩
    simpa only [mem_ball, dist_zero_right] using norm_inverse_lt_one c hη hz

/-- The strip map's derivative preserves its full complex rational form. -/
theorem hasDerivAt_map (c : ℂ) (η : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (map c η) ((4 * (η : ℂ) / Real.pi) / (1 + w ^ 2)) w := by
  simpa only [map, mul_one_div] using!
    ((hasDerivAt_arctan hw).const_mul (4 * (η : ℂ) / Real.pi)).const_add c

/-- The map is analytic at every point of the original unit disc. -/
theorem analyticAt_map (c : ℂ) (η : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (map c η) w := by
  exact analyticAt_const.add (analyticAt_const.mul (analyticAt_arctan hw))

/-- A positive-width strip map has nonzero derivative throughout the disc. -/
theorem deriv_map_ne_zero (c : ℂ) {η : ℝ} (hη : 0 < η) {w : ℂ} (hw : ‖w‖ < 1) :
    deriv (map c η) w ≠ 0 := by
  rw [(hasDerivAt_map c η hw).deriv]
  apply div_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hη.ne'))
      (ofReal_ne_zero.mpr Real.pi_ne_zero)
  · have h : (1 - w * I) * (1 + w * I) = 1 + w ^ 2 := by
      calc
        _ = 1 - w ^ 2 * I ^ 2 := by ring
        _ = _ := by simp
    exact h ▸ mul_ne_zero (denominator_ne_zero hw) (numerator_ne_zero hw)

/-- Composition with the strip map preserves the exact analytic order,
including multiplicities, without assuming a function has only simple zeros. -/
theorem analyticOrderAt_comp_map (f : ℂ → ℂ) (c : ℂ) {η : ℝ} (hη : 0 < η)
    {w : ℂ} (hw : ‖w‖ < 1) :
    analyticOrderAt (f ∘ map c η) w = analyticOrderAt f (map c η w) :=
  analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_map c η hw) (deriv_map_ne_zero c hη hw)

end
end RiemannGaussian.AnalyticStripMap
