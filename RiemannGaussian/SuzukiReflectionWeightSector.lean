/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectionContrast

/-!
# The complex sector of the actual reflection weight on remote strip sides

The canonical reflection contrast has weight minus the square of its
Cauchy difference. On a remote vertical segment of height at most one
half, this exact weight has nonnegative real part and imaginary part at
most one thirty-second of it in magnitude. Its original complex phase
and its quartic denominator remain available.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- The original canonical reflection weight, before multiplying by
either the actual or finite arithmetic carrier. -/
def suzukiXiReflectionWeight (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  -suzukiXiReflectionCauchyDifference rho z ^ 2

/-- The original mixed reflection channel retains the full complex
weight before any signed projection. -/
theorem suzukiXiReflectionCarrierChannel_eq_weight_mul (rho : NontrivialZetaZero) (z : ℂ) :
    suzukiXiReflectionCarrierChannel rho z = suzukiXiReflectionWeight rho z * suzukiXiZeroCarrier z := by
  rw [suzukiXiReflectionCarrierChannel_eq_neg_square]
  unfold suzukiXiReflectionWeight
  ring

/-- The weight itself has the exact fourth-order node denominator,
without dividing by the carrier or assuming its numerator nonzero. -/
theorem suzukiXiReflectionWeight_eq_quartic (rho : NontrivialZetaZero) {z : ℂ}
    (ha : z ≠ zetaSpectralCoordinate rho.1)
    (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    suzukiXiReflectionWeight rho z =
      (4 * ((zetaSpectralCoordinate rho.1).im : ℂ) ^ 2) /
        ((z - zetaSpectralCoordinate rho.1) * (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))) ^ 2 := by
  let a := zetaSpectralCoordinate rho.1
  have hd : a - starRingEnd ℂ a = 2 * I * (a.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  have he : suzukiXiReflectionCauchyDifference rho z =
      (a - starRingEnd ℂ a) / ((z - a) * (z - starRingEnd ℂ a)) := by
    unfold suzukiXiReflectionCauchyDifference
    change (z - a)⁻¹ - (z - starRingEnd ℂ a)⁻¹ = _
    have hza : z - a ≠ 0 := sub_ne_zero.mpr ha
    have hzb : z - starRingEnd ℂ a ≠ 0 := sub_ne_zero.mpr hb
    field_simp
    ring
  rw [suzukiXiReflectionWeight, he, hd]
  simp only [div_pow, mul_pow, I_sq]
  ring

private lemma inverse_square_sector {q : ℂ} (hpos : 0 < q.re)
    (hsmall : 80 * |q.im| ≤ q.re) :
    0 ≤ (1 / q ^ 2).re ∧ |(1 / q ^ 2).im| ≤ (1 / q ^ 2).re / 32 := by
  have hn : q ≠ 0 := by intro he; simp [he] at hpos
  have hd : 0 < normSq (q ^ 2) := normSq_pos.mpr (pow_ne_zero _ hn)
  have hre : (1 / q ^ 2).re = (q.re ^ 2 - q.im ^ 2) / normSq (q ^ 2) := by
    rw [one_div, Complex.inv_re]
    congr 1
    simp [pow_two, mul_re]
  have him : (1 / q ^ 2).im = -(2 * q.re * q.im) / normSq (q ^ 2) := by
    rw [one_div, Complex.inv_im]
    congr 1
    simp only [pow_two, mul_im]
    ring
  have hsquare := mul_self_le_mul_self (show 0 ≤ 80 * |q.im| by positivity) hsmall
  have hprod := mul_le_mul_of_nonneg_left hsmall hpos.le
  have habs := sq_abs q.im
  have hnum : 0 ≤ q.re ^ 2 - q.im ^ 2 := by nlinarith
  have hratio : 32 * (2 * q.re * |q.im|) ≤ q.re ^ 2 - q.im ^ 2 := by nlinarith
  refine ⟨by rw [hre]; exact div_nonneg hnum hd.le, ?_⟩
  rw [him, hre, abs_div, abs_neg, abs_mul, abs_mul,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos hpos, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have he : ((q.re ^ 2 - q.im ^ 2) / normSq (q ^ 2) / 32) * normSq (q ^ 2) =
      (q.re ^ 2 - q.im ^ 2) / 32 := by field_simp
  rw [he]
  linarith

/-- The literal reflection weight lies in a narrow right-facing
sector on every sufficiently remote complete strip segment. -/
theorem suzukiXiReflectionWeight_vertical_sector (rho : NontrivialZetaZero) {v y : ℝ}
    (hv : 100 ≤ |v - (zetaSpectralCoordinate rho.1).re|) (hy : y ∈ Set.Icc 0 (1 / 2)) :
    0 ≤ (suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)).re ∧
      |(suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)).im| ≤
        (suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)).re / 32 ∧
      ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ ≤
        2 * (suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)).re := by
  let a := zetaSpectralCoordinate rho.1
  let z : ℂ := (v : ℂ) + (y : ℂ) * I
  let x := v - a.re
  let q : ℂ := (z - a) * (z - starRingEnd ℂ a)
  have hx : 100 ≤ |x| := hv
  have hza : z ≠ a := by
    intro he
    have hr := congrArg Complex.re he
    simp only [z, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero] at hr
    simp only [x, hr, sub_self, abs_zero] at hx
    linarith
  have hzb : z ≠ starRingEnd ℂ a := by
    intro he
    have hr := congrArg Complex.re he
    simp only [z, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, conj_re] at hr
    simp only [x, hr, sub_self, abs_zero] at hx
    linarith
  have hqre : q.re = x ^ 2 - y ^ 2 + a.im ^ 2 := by
    simp [q, z, x, mul_re, mul_im]
    ring
  have hqim : q.im = 2 * x * y := by
    simp [q, z, x, mul_re, mul_im]
    ring
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 ≤ 1 / 4 := by nlinarith [hy.1, hy.2]
  have hpos : 0 < q.re := by rw [hqre, hx2]; nlinarith [sq_nonneg a.im]
  have hsmall : 80 * |q.im| ≤ q.re := by
    rw [hqim, hqre, abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
      abs_of_nonneg hy.1, hx2]
    nlinarith [sq_nonneg a.im, mul_le_mul_of_nonneg_left hy.2 (abs_nonneg x)]
  obtain ⟨hq0, hqs⟩ := inverse_square_sector hpos hsmall
  have he : suzukiXiReflectionWeight rho z = ((4 * a.im ^ 2 : ℝ) : ℂ) * (1 / q ^ 2) := by
    rw [suzukiXiReflectionWeight_eq_quartic rho hza hzb]
    dsimp [q, a]
    push_cast
    ring
  have hc : 0 ≤ 4 * a.im ^ 2 := by positivity
  have hw0 : 0 ≤ (suzukiXiReflectionWeight rho z).re := by
    rw [he, re_ofReal_mul]
    exact mul_nonneg hc hq0
  have hws : |(suzukiXiReflectionWeight rho z).im| ≤ (suzukiXiReflectionWeight rho z).re / 32 := by
    rw [he, im_ofReal_mul, re_ofReal_mul, abs_mul, abs_of_nonneg hc]
    nlinarith [mul_le_mul_of_nonneg_left hqs hc]
  refine ⟨hw0, hws, ?_⟩
  have hnorm := Complex.norm_le_abs_re_add_abs_im (suzukiXiReflectionWeight rho z)
  rw [abs_of_nonneg hw0] at hnorm
  linarith

/-- The complete reflection weight has a quartic remote-side bound
independent of either the actual or finite arithmetic carrier. -/
theorem norm_suzukiXiReflectionWeight_vertical_le
    (rho : NontrivialZetaZero) {R v y : ℝ} (hR : 0 < R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4 := by
  let a := zetaSpectralCoordinate rho.1
  let z : ℂ := (v : ℂ) + (y : ℂ) * I
  have hgap : R / 2 ≤ |v - a.re| := by
    have h := abs_sub_abs_le_abs_sub v a.re
    linarith
  have hd : R / 2 ≤ ‖z - a‖ := by
    refine hgap.trans ?_
    simpa [z] using Complex.abs_re_le_norm (z - a)
  have hdstar : R / 2 ≤ ‖z - starRingEnd ℂ a‖ := by
    refine hgap.trans ?_
    simpa [z] using Complex.abs_re_le_norm (z - starRingEnd ℂ a)
  have hza : z ≠ a := by intro he; simp [he] at hd; linarith
  have hzb : z ≠ starRingEnd ℂ a := by intro he; simp [he] at hdstar; linarith
  rw [suzukiXiReflectionWeight_eq_quartic rho hza hzb, norm_div, norm_mul, norm_pow, norm_pow,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 4 * a.im ^ 2 / ((R / 2) * (R / 2)) ^ 2 := by gcongr
    _ = _ := by dsimp [a]; field_simp; ring

end
end RiemannGaussian
