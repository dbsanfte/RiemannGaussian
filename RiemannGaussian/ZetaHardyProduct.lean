/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHardyPhase

/-!
# Finite-product evaluation of the certified Hardy rotation

The finite Gamma shift can be evaluated as a product of rational complex
linear factors. Only the leading midpoint primitive needs a transcendental
phase evaluation. The product retains all phase shifts exactly, and its
positive norm scales the existing certified Hardy approximation without
changing any sign. No new asymptotic or numerical premise is introduced.
-/

namespace RiemannGaussian.ZetaHardyProduct
noncomputable section
open Complex GammaPhaseApproximation ZetaHardyPhase

/-- One conjugated linear factor of the finite Gamma shift. -/
def factor (n : ℕ) (T : ℝ) : ℂ := ((1 / 4 + n : ℝ) : ℂ) - (T / 2 : ℝ) * I

/-- The complete algebraic product replacing the separate phase shifts. -/
def shiftProduct (M : ℕ) (T : ℝ) : ℂ := ∏ n ∈ Finset.range M, factor n T

private theorem factor_re_pos (n : ℕ) (T : ℝ) : 0 < (factor n T).re := by
  simp only [factor, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero]
  positivity

private theorem factor_arg (n : ℕ) (T : ℝ) :
    (factor n T).arg = -Real.arctan ((T / 2) / (1 / 4 + n)) := by
  have hh := Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (factor_re_pos n T)))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (factor_re_pos n T)))
  rw [Complex.tan_arg] at hh
  simp only [factor, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_sub,
    neg_div, Real.arctan_neg] at hh
  exact hh.symm

private theorem factor_polar (n : ℕ) (T : ℝ) :
    factor n T = (‖factor n T‖ : ℂ) *
      Complex.exp (-I * (Real.arctan ((T / 2) / (1 / 4 + n)) : ℂ)) := by
  have hh := (Complex.norm_mul_exp_arg_mul_I (factor n T)).symm
  rw [factor_arg] at hh
  simpa only [Complex.ofReal_neg, neg_mul, mul_neg, mul_comm] using hh

/-- No algebraic Gamma-shift factor vanishes at any real height. -/
theorem shiftProduct_ne_zero (M : ℕ) (T : ℝ) : shiftProduct M T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro n _
  exact Complex.ne_zero_of_re_pos (factor_re_pos n T)

/-- The finite product keeps the complete phase sum. Its norm is strictly
positive; no principal argument of the product is substituted for the sum. -/
theorem shiftProduct_polar (M : ℕ) (T : ℝ) :
    shiftProduct M T = (‖shiftProduct M T‖ : ℂ) * Complex.exp (-I *
      ((∑ n ∈ Finset.range M, Real.arctan ((T / 2) / (1 / 4 + n)) : ℝ) : ℂ)) := by
  calc
    shiftProduct M T = ∏ n ∈ Finset.range M, (‖factor n T‖ : ℂ) *
        Complex.exp (-I * (Real.arctan ((T / 2) / (1 / 4 + n)) : ℂ)) := by
      exact Finset.prod_congr rfl fun n _ => factor_polar n T
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Complex.exp_sum,
        ← Finset.mul_sum, ← Complex.ofReal_sum]
      simp only [shiftProduct, norm_prod]

/-- The single remaining phase: the shifted midpoint primitive and the
real logarithmic pi term. The finite angle sum has become an exact product. -/
def leadingPhase (M : ℕ) (T : ℝ) : ℝ :=
  primitive (1 / 4 + M) (T / 2) - T / 2 * Real.log Real.pi

/-- An algebraic product times one phase rotation, suitable for certified
complex interval evaluation at exact rational heights. -/
def weight (M : ℕ) (T : ℝ) : ℂ :=
  shiftProduct M T * Complex.exp (I * leadingPhase M T)

/-- The product weight is exactly a positive multiple of the previously
proved finite Gamma rotation. All height and phase information is retained. -/
theorem weight_eq (M : ℕ) (T : ℝ) :
    weight M T = (‖shiftProduct M T‖ : ℂ) *
      Complex.exp (I * thetaApproximation M T) := by
  conv_lhs => rw [weight, shiftProduct_polar, mul_assoc, ← Complex.exp_add]
  congr 2
  unfold leadingPhase thetaApproximation shiftedApproximation
  push_cast
  ring

/-- The elementary rotation has unit norm; only the exact finite product
scales numerical zeta-evaluation errors. -/
theorem norm_weight (M : ℕ) (T : ℝ) : ‖weight M T‖ = ‖shiftProduct M T‖ := by
  rw [weight_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    Complex.norm_exp]
  simp only [Complex.I_mul_re, Complex.ofReal_im, neg_zero, Real.exp_zero, mul_one]

/-- An algebraic positive scale, computable by rational arithmetic at
rational heights. It avoids both square roots and exponential growth. -/
def scale (M : ℕ) (T : ℝ) : ℝ := |(shiftProduct M T).re| + |(shiftProduct M T).im|

/-- The coordinate sum used for normalization is strictly positive. -/
theorem scale_pos (M : ℕ) (T : ℝ) : 0 < scale M T :=
  (norm_pos_iff.mpr (shiftProduct_ne_zero M T)).trans_le (Complex.norm_le_abs_re_add_abs_im _)

/-- A bounded rotation with the same certified Hardy sign, using only a
positive algebraic rescaling of the complete product. -/
def normalizedWeight (M : ℕ) (T : ℝ) : ℂ := ((1 / scale M T : ℝ) : ℂ) * weight M T

/-- Normalization prevents the finite Gamma product from amplifying
the numerical zeta error. This bound holds at every real height. -/
theorem norm_normalizedWeight_le (M : ℕ) (T : ℝ) : ‖normalizedWeight M T‖ ≤ 1 := by
  rw [normalizedWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (scale_pos M T)), norm_weight, one_div, inv_mul_eq_div]
  exact (div_le_one (scale_pos M T)).mpr (Complex.norm_le_abs_re_add_abs_im _)

/-- The numerically stable signed product value. -/
def normalizedValue (T : ℝ) : ℝ := (normalizedWeight 200 T * riemannZeta (point T)).re

/-- The real signed value used for numerical zero-list verification. -/
def signedValue (T : ℝ) : ℝ := (weight 200 T * riemannZeta (point T)).re

/-- The algebraic finite-product evaluator differs from the existing
finite Hardy evaluator by a strictly positive real factor only. -/
theorem signedValue_eq (T : ℝ) :
    signedValue T = ‖shiftProduct 200 T‖ * approximateHardy T := by
  rw [signedValue, weight_eq, mul_assoc, Complex.re_ofReal_mul]
  rfl

/-- The bounded product value retains the full signed value up to a
strictly positive real factor. -/
theorem normalizedValue_eq (T : ℝ) : normalizedValue T = (1 / scale 200 T) * signedValue T := by
  unfold normalizedValue normalizedWeight signedValue
  rw [mul_assoc, Complex.re_ofReal_mul]

/-- Positive product-evaluator signs certify positive actual Hardy signs
through the entire height range required by the literature verification. -/
theorem signedValue_pos_iff {T : ℝ} (hT : |T| ≤ 22000) :
    0 < signedValue T ↔ 0 < hardy T := by
  rw [signedValue_eq, mul_pos_iff_of_pos_left (norm_pos_iff.mpr (shiftProduct_ne_zero 200 T))]
  exact approximateHardy_pos_iff hT

/-- Negative product-evaluator signs certify negative actual Hardy signs
with the same fully proved analytic phase-error allowance. -/
theorem signedValue_neg_iff {T : ℝ} (hT : |T| ≤ 22000) :
    signedValue T < 0 ↔ hardy T < 0 := by
  rw [signedValue_eq]
  have hp := norm_pos_iff.mpr (shiftProduct_ne_zero 200 T)
  have he := mul_lt_mul_iff_right₀ (b := approximateHardy T) (c := 0) hp
  simp only [mul_zero] at he
  rw [he]
  exact approximateHardy_neg_iff hT

/-- The bounded product rotation certifies the sign of actual Hardy Z
through the entire stated verification range. -/
theorem normalizedValue_pos_iff {T : ℝ} (hT : |T| ≤ 22000) :
    0 < normalizedValue T ↔ 0 < hardy T := by
  rw [normalizedValue_eq, mul_pos_iff_of_pos_left (one_div_pos.mpr (scale_pos 200 T))]
  exact signedValue_pos_iff hT

/-- Negative bounded-product signs retain the same actual Hardy sign. -/
theorem normalizedValue_neg_iff {T : ℝ} (hT : |T| ≤ 22000) :
    normalizedValue T < 0 ↔ hardy T < 0 := by
  rw [normalizedValue_eq]
  have he := mul_lt_mul_iff_right₀ (b := signedValue T) (c := 0)
    (one_div_pos.mpr (scale_pos 200 T))
  simp only [mul_zero] at he
  rw [he]
  exact signedValue_neg_iff hT

/-- The exact bounded rotation does not increase any certified complex
zeta-evaluation error. No large Gamma-product allowance needs to be paid. -/
theorem normalized_error_lt {T ε : ℝ} {z : ℂ}
    (he : ‖riemannZeta (point T) - z‖ < ε) :
    |normalizedValue T - (normalizedWeight 200 T * z).re| < ε := by
  have hh := Complex.abs_re_le_norm
    (normalizedWeight 200 T * (riemannZeta (point T) - z))
  have hb : ‖normalizedWeight 200 T * (riemannZeta (point T) - z)‖ ≤
      ‖riemannZeta (point T) - z‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_normalizedWeight_le 200 T)
      (norm_nonneg (riemannZeta (point T) - z))
  simpa only [normalizedValue, mul_sub, Complex.sub_re] using (hh.trans hb).trans_lt he

/-- Opposite certified product-evaluator signs imply a genuine critical-line
zero in the open interval. The numerical signs remain explicit obligations. -/
theorem exists_zero_of_mul_neg {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 22000) (hb : |b| ≤ 22000)
    (hs : signedValue a * signedValue b < 0) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (point t) = 0 := by
  apply exists_zero_of_approximate_mul_neg hab ha hb
  rw [signedValue_eq, signedValue_eq] at hs
  have hp : 0 < ‖shiftProduct 200 a‖ * ‖shiftProduct 200 b‖ :=
    mul_pos (norm_pos_iff.mpr (shiftProduct_ne_zero 200 a))
      (norm_pos_iff.mpr (shiftProduct_ne_zero 200 b))
  have he : ‖shiftProduct 200 a‖ * approximateHardy a *
      (‖shiftProduct 200 b‖ * approximateHardy b) =
      (‖shiftProduct 200 a‖ * ‖shiftProduct 200 b‖) *
        (approximateHardy a * approximateHardy b) := by ring
  rw [he] at hs
  have hh := mul_lt_mul_iff_right₀ (b := approximateHardy a * approximateHardy b) (c := 0) hp
  simp only [mul_zero] at hh
  exact hh.mp hs

end
end RiemannGaussian.ZetaHardyProduct
