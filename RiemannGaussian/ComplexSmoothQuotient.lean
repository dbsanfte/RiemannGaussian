/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexCauchyGreenAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A smooth bounded quotient with its full signed area source

The homogeneous expression `a conj(b) / (|b|^2+r^2 |a|^2)` stays
bounded even when the original denominator b vanishes. Its two local
charts retain both zero and pole data. The exact Cauchy--Green source
keeps the complex Wronskian before taking any absolute value.
-/

open Complex
namespace RiemannGaussian
noncomputable section

/-- Homogeneous smoothing of a complex quotient. Its value at a common
zero is zero; smoothness there must be proved from local cancellation. -/
def complexSmoothQuotient (r : ℝ) (a b : ℂ) : ℂ :=
  a * starRingEnd ℂ b /
    (b * starRingEnd ℂ b + (r : ℂ) ^ 2 * (a * starRingEnd ℂ a))

/-- The full complex denominator is exactly a nonnegative real sum. -/
theorem complexSmoothQuotient_denominator (r : ℝ) (a b : ℂ) :
    b * starRingEnd ℂ b + (r : ℂ) ^ 2 * (a * starRingEnd ℂ a) =
      ((normSq b + r ^ 2 * normSq a : ℝ) : ℂ) := by
  simp only [mul_conj, ofReal_add, ofReal_mul, ofReal_pow]

/-- Away from a common zero the smoothed denominator is genuinely
positive, including when the original denominator vanishes. -/
theorem complexSmoothQuotient_denominator_pos {r : ℝ} (hr : 0 < r) {a b : ℂ}
    (hab : a ≠ 0 ∨ b ≠ 0) : 0 < normSq b + r ^ 2 * normSq a := by
  rcases hab with ha | hb
  · exact add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos (sq_pos_of_pos hr) (normSq_pos.mpr ha))
  · exact add_pos_of_pos_of_nonneg (normSq_pos.mpr hb) (mul_nonneg (sq_nonneg _) (normSq_nonneg _))

/-- Every original denominator zero is assigned the finite value zero. -/
@[simp] theorem complexSmoothQuotient_zero_right (r : ℝ) (a : ℂ) :
    complexSmoothQuotient r a 0 = 0 := by simp [complexSmoothQuotient]

/-- The smoothed value vanishes at every numerator zero as well. -/
@[simp] theorem complexSmoothQuotient_zero_left (r : ℝ) (b : ℂ) :
    complexSmoothQuotient r 0 b = 0 := by simp [complexSmoothQuotient]

/-- A uniform bound requiring no separation of either original factor
from zero. It applies even at their common zeros. -/
theorem norm_complexSmoothQuotient_le {r : ℝ} (hr : 0 < r) (a b : ℂ) :
    ‖complexSmoothQuotient r a b‖ ≤ 1 / (2 * r) := by
  by_cases hb : b = 0
  · simp only [hb, complexSmoothQuotient_zero_right, norm_zero]
    positivity
  have hd := complexSmoothQuotient_denominator_pos hr (Or.inr hb : a ≠ 0 ∨ b ≠ 0)
  rw [complexSmoothQuotient, norm_div, norm_mul, norm_conj,
    complexSmoothQuotient_denominator, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  apply (div_le_div_iff₀ hd (mul_pos (by norm_num) hr)).mpr
  rw [← Complex.sq_norm, ← Complex.sq_norm]
  nlinarith [sq_nonneg (‖b‖ - r * ‖a‖)]

/-- The full common complex factor cancels exactly; its phase is not
estimated separately. -/
theorem complexSmoothQuotient_mul (r : ℝ) (a b : ℂ) {c : ℂ} (hc : c ≠ 0) :
    complexSmoothQuotient r (c * a) (c * b) = complexSmoothQuotient r a b := by
  have hcc : c * starRingEnd ℂ c ≠ 0 := mul_ne_zero hc (by simpa using hc)
  unfold complexSmoothQuotient
  simp only [map_mul]
  calc
    _ = ((c * starRingEnd ℂ c) * (a * starRingEnd ℂ b)) /
        ((c * starRingEnd ℂ c) * (b * starRingEnd ℂ b + (r : ℂ) ^ 2 * (a * starRingEnd ℂ a))) := by
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ hcc

/-- The ordinary quotient chart is valid wherever its original
denominator is nonzero. -/
theorem complexSmoothQuotient_eq_div_chart (r : ℝ) (a : ℂ) {b : ℂ} (hb : b ≠ 0) :
    complexSmoothQuotient r a b = complexSmoothQuotient r (a / b) 1 := by
  have h := complexSmoothQuotient_mul r (a / b) 1 hb
  simpa [mul_div_cancel₀ _ hb] using h

/-- The reciprocal chart stays regular through original denominator
zeros when the numerator is nonzero. -/
theorem complexSmoothQuotient_eq_inv_chart (r : ℝ) {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    complexSmoothQuotient r a b = complexSmoothQuotient r 1 (b / a) := by
  have h := complexSmoothQuotient_mul r 1 (b / a) ha
  simpa [mul_div_cancel₀ _ ha] using h

/-- The ordinary chart has an explicit positive radial denominator. -/
theorem complexSmoothQuotient_one_right (r : ℝ) (a : ℂ) :
    complexSmoothQuotient r a 1 = a / ((1 + r ^ 2 * normSq a : ℝ) : ℂ) := by
  rw [complexSmoothQuotient, complexSmoothQuotient_denominator]
  simp

/-- The exact complex complement of radial smoothing. This identity
retains the coupled phase rather than replacing the complement by a norm. -/
theorem complexSmoothQuotient_radial_identity (r : ℝ) (a : ℂ) :
    complexSmoothQuotient r a 1 + (r : ℂ) ^ 2 * a ^ 2 *
      starRingEnd ℂ (complexSmoothQuotient r a 1) = a := by
  have hd : (1 + r ^ 2 * normSq a : ℝ) ≠ 0 := by
    have hn := mul_nonneg (sq_nonneg r) (normSq_nonneg a)
    linarith
  rw [complexSmoothQuotient_one_right, map_div₀, conj_ofReal]
  have hdc : ((1 + r ^ 2 * normSq a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp
  push_cast
  rw [← mul_conj a]
  ring

/-- Smooth inputs give a smooth quotient at every noncommon zero. -/
theorem contDiffAt_complexSmoothQuotient {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    {z : ℂ} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f z) (hg : ContDiffAt ℝ n g z)
    (hfg : f z ≠ 0 ∨ g z ≠ 0) :
    ContDiffAt ℝ n (fun w => complexSmoothQuotient r (f w) (g w)) z := by
  have hfc := Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have hgc := Complex.conjCLE.contDiff.contDiffAt.comp z hg
  have hd : g z * starRingEnd ℂ (g z) + (r : ℂ) ^ 2 * (f z * starRingEnd ℂ (f z)) ≠ 0 := by
    rw [complexSmoothQuotient_denominator, ofReal_ne_zero]
    exact (complexSmoothQuotient_denominator_pos hr hfg).ne'
  simpa [complexSmoothQuotient, div_eq_mul_inv] using
    (hf.mul hgc).mul (((hg.mul hgc).add (contDiffAt_const.mul (hf.mul hfc))).inv hd)

/-- Exact signed area source for two holomorphic inputs. The full
Wronskian and all complex phases survive the regularization. -/
theorem complexCauchyGreenSource_complexSmoothQuotient
    {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hfg : f z ≠ 0 ∨ g z ≠ 0) :
    complexCauchyGreenSource (fun w => complexSmoothQuotient r (f w) (g w)) z =
      2 * I * (r : ℂ) ^ 2 * f z ^ 2 *
        starRingEnd ℂ (f z * deriv g z - g z * deriv f z) /
          ((normSq (g z) + r ^ 2 * normSq (f z) : ℝ) : ℂ) ^ 2 := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hfc : DifferentiableAt ℝ (fun w => starRingEnd ℂ (f w)) z :=
    Complex.conjCLE.differentiableAt.comp z hfR
  have hgc : DifferentiableAt ℝ (fun w => starRingEnd ℂ (g w)) z :=
    Complex.conjCLE.differentiableAt.comp z hgR
  have hd : g z * starRingEnd ℂ (g z) + (r : ℂ) ^ 2 * (f z * starRingEnd ℂ (f z)) ≠ 0 := by
    rw [complexSmoothQuotient_denominator, ofReal_ne_zero]
    exact (complexSmoothQuotient_denominator_pos hr hfg).ne'
  unfold complexSmoothQuotient
  rw [complexCauchyGreenSource_div
    (f := fun w => f w * starRingEnd ℂ (g w))
    (g := fun w => g w * starRingEnd ℂ (g w) + (r : ℂ) ^ 2 * (f w * starRingEnd ℂ (f w)))
    (hfR.mul hgc)
    ((hgR.mul hgc).add ((differentiableAt_const _).mul (hfR.mul hfc))) hd,
    complexCauchyGreenSource_add
      (f := fun w => g w * starRingEnd ℂ (g w))
      (g := fun w => (r : ℂ) ^ 2 * (f w * starRingEnd ℂ (f w)))
      (hgR.mul hgc) ((differentiableAt_const _).mul (hfR.mul hfc)),
    complexCauchyGreenSource_mul hfR hgc,
    complexCauchyGreenSource_mul hgR hgc,
    complexCauchyGreenSource_mul (g := fun w => f w * starRingEnd ℂ (f w))
      (differentiableAt_const _) (hfR.mul hfc),
    complexCauchyGreenSource_mul hfR hfc,
    complexCauchyGreenSource_eq_zero hf, complexCauchyGreenSource_eq_zero hg,
    complexCauchyGreenSource_eq_zero (differentiableAt_const _),
    complexCauchyGreenSource_conj hf, complexCauchyGreenSource_conj hg]
  rw [← complexSmoothQuotient_denominator]
  simp only [map_sub, map_mul]
  congr 1
  ring

end
end RiemannGaussian
