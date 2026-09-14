/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianDigammaGauss
import RiemannGaussian.FiniteOnePair
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact integrable cosine representation of the positive-part hinge

A nonnegative Laplace-cosine kernel is integrable on the positive quadrant.
Its two integration orders give the exact inverse-square cosine integral
and positive-part formula. Both endpoints and the signed linear term are
paid; no improper exchange or generic zero-bound premise is assumed.
-/

namespace RiemannGaussian.CosineHinge
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

/-- The half-line scaled Cauchy integral, including the zero scale. -/
theorem integral_cauchy_numerator (b : ℝ) :
    (∫ t : ℝ in Ioi 0, b ^ 2 / (t ^ 2 + b ^ 2)) = Real.pi * |b| / 2 := by
  by_cases hb : b = 0
  · simp [hb]
  have ha : 0 < |b| := abs_pos.mpr hb
  have hid (t : ℝ) : b ^ 2 / (t ^ 2 + b ^ 2) = (1 + (|b|⁻¹ * t) ^ 2)⁻¹ := by
    rw [← sq_abs b]
    field_simp [ha.ne']
    ring
  simp_rw [hid]
  rw [integral_comp_mul_left_Ioi (fun t : ℝ => (1 + t ^ 2)⁻¹) 0 (inv_pos.mpr ha)]
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
    inv_inv, smul_eq_mul]
  ring

/-- The rational half-line majorant is genuinely integrable at every scale. -/
theorem integrable_cauchy_numerator (b : ℝ) :
    IntegrableOn (fun t : ℝ => b ^ 2 / (t ^ 2 + b ^ 2)) (Ioi 0) := by
  by_cases hb : b = 0
  · simp [hb]
  have h := (integrable_inv_sq_add_sq (abs_pos.mpr hb)).const_mul (b ^ 2)
  simpa only [sq_abs, div_eq_mul_inv] using h.integrableOn (s := Ioi 0)

/-- A Laplace evaluation of the inverse-square kernel at positive frequency. -/
theorem integral_laplace_inverse_square {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioi 0, t * Real.exp (-t * x)) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have hg : Real.Gamma 2 = 1 := by norm_num
  rw [hg] at h
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    Real.Gamma_nat_eq_factorial, Nat.factorial_one, Nat.cast_one, mul_one] at h
  convert h using 1
  · congr 1
    funext t
    congr 2
    ring
  · ring

/-- Integrating the nonnegative Laplace-cosine kernel first in frequency
produces the same rational majorant, with all endpoint conditions paid. -/
theorem integral_laplace_cosine {t : ℝ} (ht : 0 < t) (b : ℝ) :
    (∫ x : ℝ in Ioi 0, t * Real.exp (-t * x) * (1 - Real.cos (b * x))) =
      b ^ 2 / (t ^ 2 + b ^ 2) := by
  simp_rw [mul_assoc]
  rw [integral_const_mul, Complex.integral_exp_neg_mul_one_sub_cos ht b]
  have hd : t ^ 2 + b ^ 2 ≠ 0 := by positivity
  field_simp [ht.ne', hd]
  ring

/-- The full Laplace-cosine kernel is integrable on the positive quadrant.
This justifies the subsequent change of integration order. -/
theorem integrable_laplace_cosine (b : ℝ) :
    Integrable (fun v : ℝ × ℝ => v.1 * Real.exp (-v.1 * v.2) *
      (1 - Real.cos (b * v.2))) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [mul_assoc] using
      (Complex.integrableOn_exp_neg_mul_one_sub_cos ht b).const_mul t
  · apply (integrable_cauchy_numerator b).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnorm : (∫ x : ℝ in Ioi 0, ‖t * Real.exp (-t * x) * (1 - Real.cos (b * x))‖) =
        ∫ x : ℝ in Ioi 0, t * Real.exp (-t * x) * (1 - Real.cos (b * x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)
        (sub_nonneg.mpr (Real.cos_le_one _)))]
    rw [hnorm, integral_laplace_cosine ht]

/-- Exact two-sided Fourier hinge kernel, expressed using its paired cosine.
The cancellation at zero makes the positive-half-line integral finite. -/
theorem integral_one_sub_cos_div_sq (b : ℝ) :
    (∫ x : ℝ in Ioi 0, (1 - Real.cos (b * x)) / x ^ 2) = Real.pi * |b| / 2 := by
  have hswap := integral_integral_swap
    (f := fun t x : ℝ => t * Real.exp (-t * x) * (1 - Real.cos (b * x)))
    (integrable_laplace_cosine b)
  have hleft : (∫ t : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0,
      t * Real.exp (-t * x) * (1 - Real.cos (b * x))) = Real.pi * |b| / 2 := by
    rw [← integral_cauchy_numerator b]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integral_laplace_cosine ht b
  have hright : (∫ x : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
      t * Real.exp (-t * x) * (1 - Real.cos (b * x))) =
      ∫ x : ℝ in Ioi 0, (1 - Real.cos (b * x)) / x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [integral_mul_const, integral_laplace_inverse_square hx]
    ring
  exact hright.symm.trans (hswap.symm.trans hleft)

/-- The cancellation kernel is genuinely integrable at both endpoints. -/
theorem integrable_one_sub_cos_div_sq (b : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - Real.cos (b * x)) / x ^ 2) (Ioi 0) := by
  apply (integrable_laplace_cosine b).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [integral_mul_const, integral_laplace_inverse_square hx]
  ring

/-- The exact positive-part hinge uses one signed endpoint and the paired
cosine integral. No estimate or dropped endpoint term occurs. -/
theorem positive_part_eq_cosine_integral (x : ℝ) :
    max 0 x = x / 2 + (1 / Real.pi) *
      (∫ t : ℝ in Ioi 0, (1 - Real.cos (x * t)) / t ^ 2) := by
  rw [integral_one_sub_cos_div_sq]
  have hmax : max 0 x = (x + |x|) / 2 := by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_right hx, abs_of_nonneg hx]; ring
    · rw [max_eq_left hx, abs_of_nonpos hx]; ring
  rw [hmax]
  field_simp [Real.pi_ne_zero]

end
end RiemannGaussian.CosineHinge
