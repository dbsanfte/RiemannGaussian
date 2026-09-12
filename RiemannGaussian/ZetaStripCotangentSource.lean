/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStripDisc

/-!
# The exact limiting cotangent source of an actual strip zero

The full signed finite canonical source is retained while the disc radius
approaches one. Its real projection is exactly the classical cotangent
source in physical strip coordinates, with the Jacobian and actual zero
multiplicity. No limit of the boundary moment is assumed by these source
identities.
-/

namespace RiemannGaussian.ZetaStripCotangentSource
noncomputable section
open Complex Filter Metric Set
open ZetaStripDisc AnalyticStripDisc AnalyticDiscSignedDerivative AnalyticDiscBoundaryMoment
open scoped Topology

/-- The double-angle identity keeps the two canonical pieces coupled.
Only the actual zero denominator is required to be nonzero. -/
theorem cot_sub_tan {q : ℂ} (hq : Complex.tan q ≠ 0) :
    Complex.cot q - Complex.tan q = 2 * Complex.cot (2 * q) := by
  simp only [← Complex.tan_inv_eq_cot]
  rw [Complex.tan_two_mul, inv_div]
  field_simp

/-- The real part of the full limiting canonical kernel is exactly
the signed double-angle cotangent. Its complex precursor is not discarded. -/
theorem kernel_one_tan_re {q : ℂ} (hq : Complex.tan q ≠ 0) :
    (kernel 1 (Complex.tan q)).re = (-2 * Complex.cot (2 * q)).re := by
  have h := congrArg Complex.re (cot_sub_tan hq)
  simp only [Complex.sub_re] at h
  simp only [kernel, one_pow, Complex.ofReal_one, div_one, Complex.add_re,
    neg_div, one_div, Complex.neg_re, Complex.conj_re, Complex.tan_inv_eq_cot]
  rw [show (-2 : ℂ) * Complex.cot (2 * q) = -(2 * Complex.cot (2 * q)) by ring,
    Complex.neg_re]
  linarith

/-- The complete complex canonical kernel has its ordinary full-radius
limit at every fixed coordinate. This does not exchange a limit with a sum. -/
theorem kernel_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (w : ℂ) :
    Tendsto (fun n => kernel (r n) w) atTop (𝓝 (kernel 1 w)) := by
  have h : ContinuousAt (fun R : ℝ => kernel R w) 1 := by
    unfold kernel
    fun_prop (disch := norm_num)
  exact h.tendsto.comp hr

/-- A genuine strip zero cannot map to the safe nonzero center. -/
theorem coordinate_ne_zero (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) : coordinate c η ρ.1 ≠ 0 := by
  intro h
  have hm := AnalyticStripMap.map_tan c hη hρ
  change AnalyticStripMap.map c η (coordinate c η ρ.1) = ρ.1 at hm
  rw [h, AnalyticStripMap.map_zero] at hm
  have he := congrArg Complex.re hm
  linarith [NontrivialZetaZero.re_lt_one ρ]

/-- The full unit-radius source has its exact physical complex
cotangent argument, before imposing any relation between ordinates. -/
theorem kernel_one_coordinate_re (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) :
    (kernel 1 (coordinate c η ρ.1)).re =
      (-2 * Complex.cot (Real.pi * (ρ.1 - c) / (2 * η))).re := by
  have h := kernel_one_tan_re (coordinate_ne_zero ρ hc hη hρ)
  change (kernel 1 (coordinate c η ρ.1)).re =
    (-2 * Complex.cot (2 * (Real.pi * (ρ.1 - c) / (4 * η)))).re at h
  have he : 2 * (Real.pi * (ρ.1 - c) / (4 * (η : ℂ))) =
      Real.pi * (ρ.1 - c) / (2 * η) := by ring
  rwa [he] at h

/-- At the selected zero's ordinate, the exact limiting source is a
real cotangent of its horizontal distance from the safe center. -/
theorem kernel_one_coordinate_same_height (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) (ht : c.im = ρ.1.im) :
    (kernel 1 (coordinate c η ρ.1)).re =
      2 * Real.cot (Real.pi * (c.re - ρ.1.re) / (2 * η)) := by
  rw [kernel_one_coordinate_re ρ hc hη hρ]
  have hz : ρ.1 - c = -((c.re - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ht]
  have he : Real.pi * (ρ.1 - c) / (2 * (η : ℂ)) =
      -((Real.pi * (c.re - ρ.1.re) / (2 * η) : ℝ) : ℂ) := by
    rw [hz]
    push_cast
    ring
  rw [he]
  have hr (x : ℝ) : Complex.cot (-(x : ℂ)) = -(Real.cot x : ℂ) := by
    rw [Complex.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      Complex.ofReal_div, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.cos_neg, Complex.sin_neg, div_neg]
  rw [hr]
  norm_num [Complex.mul_re, Real.cot]

/-- The physically normalized selected source converges to the exact
cotangent source with its full actual multiplicity. Only the single selected
term is passed to the limit here. -/
theorem selected_source_tendsto (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) (ht : c.im = ρ.1.im)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (kernel (r n) (coordinate c η ρ.1)).re) atTop
      (𝓝 ((analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * η)) *
        Real.cot (Real.pi * (c.re - ρ.1.re) / (2 * η)))) := by
  have h := (Complex.continuous_re.tendsto _).comp (kernel_tendsto hr (coordinate c η ρ.1))
  have h := h.const_mul ((Real.pi / (4 * η)) * (analyticZetaZeroMultiplicity ρ : ℝ))
  rw [kernel_one_coordinate_same_height ρ hc hη hρ ht] at h
  convert! h using 1
  congr 1
  ring

/-- The exact limiting cotangent contribution is strictly positive
for every actual zero in the open strip at the center's ordinate. -/
theorem selected_source_pos (ρ : NontrivialZetaZero) {c : ℂ} {η : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hρ : ρ.1 ∈ strip c η) :
    0 < (analyticZetaZeroMultiplicity ρ : ℝ) * (Real.pi / (2 * η)) *
      Real.cot (Real.pi * (c.re - ρ.1.re) / (2 * η)) := by
  have hd : 0 < c.re - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have hdη : c.re - ρ.1.re < η := by
    have hh := (abs_lt.mp (show |ρ.1.re - c.re| < η from hρ)).1
    linarith
  have hx : 0 < Real.pi * (c.re - ρ.1.re) / (2 * η) := by positivity
  have hxπ : Real.pi * (c.re - ρ.1.re) / (2 * η) < Real.pi / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * η)]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxπ⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  rw [Real.cot_eq_cos_div_sin]
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
    · positivity
  · exact div_pos hcos hsin

/-- The actual finite inequality has the physical logarithmic derivative
with coefficient one, an exact signed boundary moment, and the full pole
correction. It is ready for a proved boundary limit. -/
theorem normalized_selected_constraint (ρ : NontrivialZetaZero) {c : ℂ} {η r : ℝ}
    (hc : 1 < c.re) (hη : 0 < η) (hleft : η < c.re) (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ w : ℂ, ‖w‖ = r → carrier c η w ≠ 0)
    (hρ : ρ.1 ∈ strip c η) (hmem : coordinate c η ρ.1 ∈ ball 0 r) :
    (-logDeriv riemannZeta c).re + (Real.pi / (4 * η)) *
        (analyticZetaZeroMultiplicity ρ : ℝ) * (kernel r (coordinate c η ρ.1)).re ≤
      (Real.pi / (4 * η)) * (-moment (carrier c η) r).re +
        (1 / (c - 1) - 1 / (c + 1)).re := by
  have h := mul_le_mul_of_nonneg_left
    (selected_source_constraint ρ hc hη hleft hr hr1 hs hρ hmem)
    (by positivity : 0 ≤ Real.pi / (4 * η))
  have he : (Real.pi / (4 * η)) * (4 * η / Real.pi) = 1 := by
    field_simp
  simpa only [mul_add, ← mul_assoc, he, one_mul] using h

end
end RiemannGaussian.ZetaStripCotangentSource
