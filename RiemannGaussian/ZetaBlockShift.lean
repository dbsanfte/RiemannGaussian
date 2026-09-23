/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockTaylor

/-!
# Reusing a block polynomial at nearby heights

The slowly varying factor `(1+x/300)^(-d)` has a short polynomial
approximation when `d` is purely imaginary and `|d| ≤ 64`. Its finite
differential residual gives a quantitative error without an assumed
Taylor remainder. This is a batch-evaluation estimate, not a zero count.
-/

namespace RiemannGaussian.ZetaBlockShift
noncomputable section
open Complex Real Set
open scoped BigOperators

/-- Binomial coefficients for the imaginary height correction. -/
def coefficient (d : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => -(d + j) / (300 * (j + 1)) * coefficient d j

@[simp] theorem coefficient_zero (d : ℂ) : coefficient d 0 = 1 := rfl

theorem coefficient_recurrence (d : ℂ) (j : ℕ) :
    ((j + 1 : ℕ) : ℂ) * coefficient d (j + 1) =
      -(d + j) / 300 * coefficient d j := by
  have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : j + 1 ≠ 0)
  simp only [coefficient]
  push_cast
  field_simp

/-- Complete finite shift polynomial. -/
def polynomial (d : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), coefficient d j * z ^ j

/-- Literal derivative of the shift polynomial. -/
def slope (d : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * coefficient d (j + 1) * z ^ j

@[simp] theorem polynomial_zero (d z : ℂ) : polynomial d 0 z = 1 := by
  simp [polynomial]

@[simp] theorem slope_zero (d z : ℂ) : slope d 0 z = 0 := by simp [slope]

theorem polynomial_succ (d z : ℂ) (m : ℕ) :
    polynomial d (m + 1) z = polynomial d m z + coefficient d (m + 1) * z ^ (m + 1) :=
  Finset.sum_range_succ _ _

theorem slope_succ (d z : ℂ) (m : ℕ) :
    slope d (m + 1) z = slope d m z + ((m + 1 : ℕ) : ℂ) * coefficient d (m + 1) * z ^ m :=
  Finset.sum_range_succ _ _

@[simp] theorem polynomial_at_zero (d : ℂ) (m : ℕ) : polynomial d m 0 = 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [polynomial_succ, ih]; simp

/-- All lower coefficients cancel in the differential residual. -/
theorem polynomial_residual (d z : ℂ) (m : ℕ) :
    (1 + z / 300) * slope d m z + (d / 300) * polynomial d m z =
      -((m + 1 : ℕ) : ℂ) * coefficient d (m + 1) * z ^ m := by
  induction m with
  | zero => simp [coefficient]; ring
  | succ m ih =>
    rw [slope_succ, polynomial_succ]
    have hc := coefficient_recurrence d (m + 1)
    push_cast at hc ih ⊢
    rw [show m + 1 + 1 = m + 2 by omega]
    linear_combination ih + z ^ (m + 1) * hc

theorem hasDerivAt_polynomial (d : ℂ) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => polynomial d m y) (slope d m x) x := by
  induction m with
  | zero => simpa using (hasDerivAt_const x (1 : ℂ))
  | succ m ih =>
    simp only [polynomial_succ, slope_succ]
    convert! ih.add (((hasDerivAt_id x).ofReal_comp.pow (m + 1)).const_mul
      (coefficient d (m + 1))) using 1
    norm_num
    ring

/-- Positive rational majorant at shift radius 64. -/
def majorant : ℕ → ℚ
  | 0 => 1
  | j + 1 => (64 + j) / (300 * (j + 1)) * majorant j

theorem majorant_nonneg (j : ℕ) : 0 ≤ majorant j := by
  induction j with
  | zero => norm_num [majorant]
  | succ j ih => dsimp [majorant]; positivity

theorem norm_coefficient_le {d : ℂ} (hd : ‖d‖ ≤ 64) (j : ℕ) :
    ‖coefficient d j‖ ≤ (majorant j : ℝ) := by
  induction j with
  | zero => norm_num [coefficient, majorant]
  | succ j ih =>
    simp only [coefficient, majorant, norm_mul, norm_div, norm_neg]
    push_cast
    have hn : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [Complex.norm_ofNat, hn]
    apply mul_le_mul _ ih (norm_nonneg _) (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (norm_add_le _ _).trans (by simpa using add_le_add_right hd (j : ℝ))

/-- Exact slowly varying factor after the block's main phase is removed. -/
def model (d : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-d * (Real.log (1 + x / 300) : ℂ))

@[simp] theorem model_zero (d : ℂ) : model d 0 = 1 := by simp [model]

/-- An imaginary height shift and its inverse both have norm one. -/
theorem norm_model {d : ℂ} (hd : d.re = 0) (x : ℝ) : ‖model d x‖ = 1 := by
  simp [model, Complex.norm_exp, mul_re, hd]

theorem model_neg_mul (d : ℂ) (x : ℝ) : model (-d) x * model d x = 1 := by
  rw [model, model, ← Complex.exp_add]
  simp

theorem hasDerivAt_model (d : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (model d)
      ((-d / 300) / (1 + (x : ℂ) / 300) * model d x) x := by
  have hd := ((((hasDerivAt_id x).div_const 300).const_add 1).log
    (by positivity : 1 + x / 300 ≠ 0)).ofReal_comp
  convert! (hd.const_mul (-d)).cexp using 1
  push_cast
  dsimp only [model, id]
  ring

private theorem denominator_norm {x : ℝ} (hx : 0 ≤ x) :
    ‖1 + (x : ℂ) / 300‖ = 1 + x / 300 := by
  rw [show (1 : ℂ) + (x : ℂ) / 300 = ((1 + x / 300 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Multiplying by the inverse exact factor exposes only the finite residual. -/
theorem hasDerivAt_normalizedPolynomial (d : ℂ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => polynomial d m y * model (-d) y)
      (((1 + (x : ℂ) / 300) * slope d m x + (d / 300) * polynomial d m x) /
        (1 + (x : ℂ) / 300) * model (-d) x) x := by
  have hd := (hasDerivAt_polynomial d m x).mul (hasDerivAt_model (-d) hx)
  have hn : (1 : ℂ) + (x : ℂ) / 300 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [denominator_norm hx]
    positivity
  convert! hd using 1
  generalize (1 : ℂ) + (x : ℂ) / 300 = t at *
  field_simp

/-- The remaining coefficient gives a rational uniform error bound. -/
def errorBudget (m : ℕ) : ℚ := (m + 1) * majorant (m + 1)

theorem norm_model_sub_polynomial_le {d : ℂ} (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64)
    (m : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖model d x - polynomial d m x‖ ≤ (errorBudget m : ℝ) := by
  let B : ℝ := (m + 1 : ℝ) * (majorant (m + 1) : ℝ)
  have hB : 0 ≤ B := by
    have h0 : (0 : ℝ) ≤ (majorant (m + 1) : ℝ) := by exact_mod_cast majorant_nonneg (m + 1)
    dsimp [B]; positivity
  have hb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖((1 + (t : ℂ) / 300) * slope d m t + (d / 300) * polynomial d m t) /
        (1 + (t : ℂ) / 300) * model (-d) t‖ ≤ B := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    rw [polynomial_residual, norm_mul, norm_model (by simpa using hd0), mul_one,
      norm_div, denominator_norm ht.1]
    apply (div_le_div_of_nonneg_right (b := B) _
      (show 0 ≤ 1 + t / 300 by positivity)).trans (div_le_self hB (by linarith))
    simp only [norm_mul, norm_neg, Complex.norm_natCast, norm_pow]
    have ht' : ‖(t : ℂ)‖ ^ m ≤ 1 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact pow_le_one₀ ht.1 ht.2.le
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ) * ‖coefficient d (m + 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left ht' (by positivity)
      _ ≤ B := by
        rw [mul_one]
        simpa only [B, Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left (norm_coefficient_le hd (m + 1))
            (show 0 ≤ (m : ℝ) + 1 by positivity)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hasDerivAt_normalizedPolynomial d m ht.1).hasDerivWithinAt) hb x hx
  rw [Complex.ofReal_zero, polynomial_at_zero, model_zero, one_mul, sub_zero] at hm
  have hsmall : ‖polynomial d m x * model (-d) x - 1‖ ≤ B :=
    hm.trans (mul_le_of_le_one_right hB hx.2)
  calc
    ‖model d x - polynomial d m x‖ = ‖polynomial d m x - model d x‖ := norm_sub_rev _ _
    _ = ‖(polynomial d m x * model (-d) x - 1) * model d x‖ := by
      rw [sub_mul, mul_assoc, model_neg_mul, mul_one, one_mul]
    _ = ‖polynomial d m x * model (-d) x - 1‖ := by rw [norm_mul, norm_model hd0, mul_one]
    _ ≤ B := hsmall
    _ = _ := by simp [B, errorBudget]

/-- Exact arithmetic pays the degree-twelve remainder throughout radius 64. -/
theorem errorBudget_twelve : errorBudget 12 ≤ (1 / 80000000000000000 : ℚ) := by
  decide +kernel

/-- Uniform error of the reusable height correction is at most `1.25e-17`. -/
theorem norm_model_sub_twelve_le {d : ℂ} (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖model d x - polynomial d 12 x‖ ≤ 1 / 80000000000000000 := by
  exact (norm_model_sub_polynomial_le hd0 hd 12 hx).trans
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr errorBudget_twelve)

/-- Reusing the center polynomial retains its error, plus the tiny shift error. -/
theorem norm_product_error_le {s d : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (hd0 : d.re = 0) (hd : ‖d‖ ≤ 64) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖ZetaBlockTaylor.model s x * model d x -
      ZetaBlockTaylor.polynomial s 18 x * polynomial d 12 x‖ ≤
        801 / 20000000000000000 := by
  have he := ZetaBlockTaylor.norm_model_sub_eighteen_le hs0 hs hx
  have hp : ‖ZetaBlockTaylor.polynomial s 18 x‖ ≤ 4 := by
    have hn := norm_add_le (ZetaBlockTaylor.model s x)
      (ZetaBlockTaylor.polynomial s 18 x - ZetaBlockTaylor.model s x)
    rw [add_sub_cancel, norm_sub_rev] at hn
    linarith [ZetaBlockTaylor.norm_model_le hs hx]
  have hid : ZetaBlockTaylor.model s x * model d x -
      ZetaBlockTaylor.polynomial s 18 x * polynomial d 12 x =
      (ZetaBlockTaylor.model s x - ZetaBlockTaylor.polynomial s 18 x) * model d x +
      ZetaBlockTaylor.polynomial s 18 x * (model d x - polynomial d 12 x) := by ring
  rw [hid]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_model hd0, mul_one]
  have hshift := mul_le_mul hp (norm_model_sub_twelve_le hd0 hd hx) (norm_nonneg _) (by norm_num)
  linarith

end
end RiemannGaussian.ZetaBlockShift
