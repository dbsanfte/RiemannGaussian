/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The analytic cotangent-minus-pole correction

The entire divided sine gives a genuine analytic representative of the
cotangent after its center pole is removed. Its normalization and zero
value are proved from the original sine, not assigned to a singular
quotient. Exact complex and real identities retain the physical strip
scale and give the boundary signs needed for a half-disc comparison.
-/

namespace RiemannGaussian.CotangentRegularization
noncomputable section
open Complex Filter Metric Set
open scoped Topology

/-- The genuine entire divided sine, with its derivative-defined value at zero. -/
def sinc : ℂ → ℂ := dslope Complex.sin 0

/-- The original sine derivative fixes the complete center normalization. -/
theorem sinc_zero : sinc 0 = 1 := by
  simp [sinc, dslope_same, Complex.deriv_sin]

/-- Away from zero the analytic representative is the original sine quotient. -/
theorem sinc_eq {z : ℂ} (hz : z ≠ 0) : sinc z = Complex.sin z / z := by
  simp only [sinc, dslope_of_ne Complex.sin hz, slope_def_field, Complex.sin_zero, sub_zero]

/-- Removable-singularity theory proves the divided sine entire. -/
theorem analyticAt_sinc (z : ℂ) : AnalyticAt ℂ sinc z := by
  have hd : Differentiable ℂ sinc := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr
      Complex.differentiable_sin.differentiableOn
  exact hd.analyticAt z

/-- The original odd sine becomes an exactly even entire divided sine. -/
theorem sinc_neg (z : ℂ) : sinc (-z) = sinc z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [sinc_eq (neg_ne_zero.mpr hz), sinc_eq hz, Complex.sin_neg, neg_div_neg_eq]

/-- Evenness fixes the derivative at the removed pole to zero. -/
theorem deriv_sinc_zero : deriv sinc 0 = 0 := by
  have he : (fun z : ℂ => sinc (-z)) = sinc := funext sinc_neg
  have hd := deriv_comp_neg sinc 0
  rw [he, neg_zero] at hd
  linear_combination (1 / 2 : ℂ) * hd

private theorem sin_ne_zero {z : ℂ} (hz : z ≠ 0) (hzn : ‖z‖ < Real.pi) :
    Complex.sin z ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have him : z.im = 0 := by rw [hk]; simp
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hr : Real.sin z.re = 0 := by rw [he] at h; exact_mod_cast h
  have habs : |z.re| < Real.pi := (Complex.abs_re_le_norm z).trans_lt hzn
  have hz0 := (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp habs).1 (abs_lt.mp habs).2).mp hr
  exact hz (by rw [he, hz0, Complex.ofReal_zero])

/-- The divided sine has no zero in the complete disc of radius pi. -/
theorem sinc_ne_zero {z : ℂ} (hz : ‖z‖ < Real.pi) : sinc z ≠ 0 := by
  by_cases hz0 : z = 0
  · simp [hz0, sinc_zero]
  · rw [sinc_eq hz0]
    exact div_ne_zero (sin_ne_zero hz0 hz) hz0

/-- Its full logarithmic derivative is analytic throughout the zero-free disc. -/
theorem analyticAt_logDeriv_sinc {z : ℂ} (hz : ‖z‖ < Real.pi) :
    AnalyticAt ℂ (logDeriv sinc) z := by
  exact (analyticAt_sinc z).deriv.div (analyticAt_sinc z) (sinc_ne_zero hz)

/-- The analytic logarithmic derivative is exactly cotangent minus its
original pole wherever the unregularized quotient is defined. -/
theorem logDeriv_sinc_eq {z : ℂ} (hz : z ≠ 0) (hzn : ‖z‖ < Real.pi) :
    logDeriv sinc z = Complex.cot z - 1 / z := by
  have he : (fun w : ℂ => Complex.sin w / w) =ᶠ[𝓝 z] sinc := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact (sinc_eq hw).symm
  have hd := ((Complex.hasDerivAt_sin z).div (hasDerivAt_id z) hz).congr_of_eventuallyEq he.symm
  rw [logDeriv, Pi.div_apply, hd.deriv, sinc_eq hz, Complex.cot_eq_cos_div_sin]
  simp only [id_eq, mul_one]
  have hs := sin_ne_zero hz hzn
  field_simp

/-- The physical strip frequency, kept explicit in every correction. -/
def frequency (η : ℝ) : ℝ := Real.pi / (2 * η)

/-- The genuine analytic correction after subtracting the strip source's pole. -/
def correction (η : ℝ) (z : ℂ) : ℂ :=
  (frequency η : ℂ) * logDeriv sinc ((frequency η : ℂ) * z)

private theorem frequency_pos {η : ℝ} (hη : 0 < η) : 0 < frequency η := by
  unfold frequency
  positivity

private theorem scaled_norm_lt {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : ‖z‖ < 2 * η) :
    ‖(frequency η : ℂ) * z‖ < Real.pi := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (frequency_pos hη)]
  unfold frequency
  apply (mul_lt_mul_of_pos_left hz (div_pos Real.pi_pos (by positivity))).trans_eq
  field_simp

/-- The removed center singularity has its true zero correction value. -/
theorem correction_zero (η : ℝ) : correction η 0 = 0 := by
  simp [correction, logDeriv, deriv_sinc_zero]

/-- The physical correction is genuinely analytic beyond the entire
closed half-disc used in the strip comparison. -/
theorem analyticAt_correction {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : ‖z‖ < 2 * η) :
    AnalyticAt ℂ (correction η) z := by
  exact analyticAt_const.mul ((analyticAt_logDeriv_sinc (scaled_norm_lt hη hz)).comp
    (analyticAt_const.mul analyticAt_id))

/-- The exact complex source correction retains both the cotangent and
the original pole, with every denominator hypothesis discharged. -/
theorem correction_eq {η : ℝ} (hη : 0 < η) {z : ℂ} (hz : z ≠ 0) (hzn : ‖z‖ < 2 * η) :
    correction η z = (frequency η : ℂ) * Complex.cot ((frequency η : ℂ) * z) - 1 / z := by
  have hp : (frequency η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (frequency_pos hη).ne'
  rw [correction, logDeriv_sinc_eq (mul_ne_zero hp hz) (scaled_norm_lt hη hzn)]
  field_simp

/-- The full real cotangent is a signed sine-cosine numerator over its
actual squared complex sine norm; no imaginary ordinate is discarded. -/
theorem cot_re (z : ℂ) :
    (Complex.cot z).re = Real.sin z.re * Real.cos z.re / Complex.normSq (Complex.sin z) := by
  have hsr : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [Complex.sin_eq z]
    simp [Real.sin]
  have hsi : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    rw [Complex.sin_eq z]
    simp [Real.cos, Real.sinh]
  have hcr : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq z]
    simp [Real.cos]
  have hci : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
    rw [Complex.cos_eq z]
    simp [Real.sin, Real.sinh]
  rw [Complex.cot_eq_cos_div_sin, Complex.div_re]
  rw [hsr, hsi, hcr, hci, ← add_div]
  congr 1
  linear_combination (Real.sin z.re * Real.cos z.re) * (Real.cosh_sq_sub_sinh_sq z.im)

/-- The cotangent has the favorable real sign on the whole half strip,
uniformly in its imaginary coordinate. -/
theorem cot_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (hz' : z.re ≤ Real.pi / 2) :
    0 ≤ (Complex.cot z).re := by
  rw [cot_re]
  apply div_nonneg (mul_nonneg ?_ ?_) (Complex.normSq_nonneg _)
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hz (by linarith [Real.pi_pos])
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hz'⟩

/-- On the imaginary axis the original cotangent's real part is exactly zero. -/
theorem cot_re_zero {z : ℂ} (hz : z.re = 0) : (Complex.cot z).re = 0 := by
  simp [cot_re, hz]

/-- The physical cotangent keeps its nonnegative sign on the complete
closed right half-disc, including the outer real endpoint. -/
theorem scaled_cot_re_nonneg {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : 0 ≤ z.re) (hz' : z.re ≤ η) :
    0 ≤ ((frequency η : ℂ) * Complex.cot ((frequency η : ℂ) * z)).re := by
  have hp := frequency_pos hη
  have hq : ((frequency η : ℂ) * z).re = frequency η * z.re := by simp
  have hq0 : 0 ≤ ((frequency η : ℂ) * z).re := by rw [hq]; positivity
  have hq1 : ((frequency η : ℂ) * z).re ≤ Real.pi / 2 := by
    rw [hq]
    apply (mul_le_mul_of_nonneg_left hz' hp.le).trans_eq
    unfold frequency
    field_simp
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    mul_nonneg hp.le (cot_re_nonneg hq0 hq1)

/-- The analytic correction has zero real part on the entire imaginary
diameter, including the genuinely removed singularity at its center. -/
theorem correction_re_zero {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : z.re = 0) (hzn : ‖z‖ < 2 * η) : (correction η z).re = 0 := by
  by_cases hz0 : z = 0
  · simp [hz0, correction_zero]
  · rw [correction_eq hη hz0 hzn, Complex.sub_re]
    have hq : ((frequency η : ℂ) * z).re = 0 := by simp [hz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      cot_re_zero hq, mul_zero, one_div, Complex.inv_re, hz, zero_div, sub_self]

/-- On the first positive quarter-period, the original cotangent loses at
most a linear term from its pole; no small-angle approximation is assumed. -/
theorem cot_real_lower {x : ℝ} (hx : 0 < x) (hx' : x ≤ Real.pi / 2) :
    1 / x - x / 2 ≤ Real.cot x := by
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hcos : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hx'⟩
  calc
    _ = (1 - x ^ 2 / 2) / x := by field_simp
    _ ≤ Real.cos x / x := div_le_div_of_nonneg_right Real.one_sub_sq_div_two_le_cos hx.le
    _ ≤ Real.cos x / Real.sin x := div_le_div_of_nonneg_left hcos hsin (Real.sin_le hx.le)
    _ = _ := by rw [Real.cot_eq_cos_div_sin]

/-- The selected real cotangent-minus-pole loss is at most
`pi^2*u/(8*eta^2)`, so it vanishes linearly at the removed center. -/
theorem scaled_cot_real_lower {η u : ℝ} (hη : 0 < η) (hu : 0 < u) (hu' : u ≤ η) :
    -(Real.pi ^ 2 * u / (8 * η ^ 2)) ≤ frequency η * Real.cot (frequency η * u) - 1 / u := by
  have hp := frequency_pos hη
  have hx : frequency η * u ≤ Real.pi / 2 := by
    apply (mul_le_mul_of_nonneg_left hu' hp.le).trans_eq
    unfold frequency
    field_simp
  have h := mul_le_mul_of_nonneg_left (cot_real_lower (mul_pos hp hu) hx) hp.le
  have he : frequency η * (1 / (frequency η * u) - frequency η * u / 2) =
      1 / u - Real.pi ^ 2 * u / (8 * η ^ 2) := by
    unfold frequency
    field_simp
    ring
  rw [he] at h
  linarith

end
end RiemannGaussian.CotangentRegularization
