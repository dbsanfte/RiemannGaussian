/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovKorobovLogPhase
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A shared block polynomial with an explicit error

The elementary block accelerator of Hiary, arXiv:1403.0317, uses
`exp(s * (t - log(1+t)))`. Here all blocks share the fixed scale `t=x/300`.
The finite polynomial's differential residual gives an explicit error;
neither an infinite Taylor expansion nor an assumed numerical remainder
is used. This is an evaluation bound, not a zero-count certificate.
-/

namespace RiemannGaussian.ZetaBlockTaylor
noncomputable section
open Complex Real Set
open scoped BigOperators

/-- Consecutive coefficients, computed together. -/
def coefficientPair (s : ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, 0)
  | j + 1 =>
      let c := coefficientPair s j
      (c.2, ((s / 90000) * c.1 - ((j + 1 : ℕ) : ℂ) / 300 * c.2) / (j + 2))

/-- Coefficients of the shared scaled polynomial. -/
def coefficient (s : ℂ) (j : ℕ) : ℂ := (coefficientPair s j).1

@[simp] theorem coefficient_zero (s : ℂ) : coefficient s 0 = 1 := rfl
@[simp] theorem coefficient_one (s : ℂ) : coefficient s 1 = 0 := rfl

theorem coefficient_recurrence (s : ℂ) (j : ℕ) :
    ((j + 2 : ℕ) : ℂ) * coefficient s (j + 2) =
      (s / 90000) * coefficient s j - ((j + 1 : ℕ) : ℂ) / 300 * coefficient s (j + 1) := by
  have hj : ((j + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
  simp only [coefficient, coefficientPair]
  push_cast at hj ⊢
  field_simp

/-- The complete degree-`m` block polynomial. -/
def polynomial (s : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), coefficient s j * z ^ j

/-- Its literal derivative polynomial. -/
def slope (s : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, ((j + 1 : ℕ) : ℂ) * coefficient s (j + 1) * z ^ j

@[simp] theorem polynomial_zero (s z : ℂ) : polynomial s 0 z = 1 := by
  simp [polynomial]

@[simp] theorem slope_zero (s z : ℂ) : slope s 0 z = 0 := by simp [slope]

theorem polynomial_succ (s z : ℂ) (m : ℕ) :
    polynomial s (m + 1) z = polynomial s m z + coefficient s (m + 1) * z ^ (m + 1) :=
  Finset.sum_range_succ _ _

theorem slope_succ (s z : ℂ) (m : ℕ) :
    slope s (m + 1) z = slope s m z + ((m + 1 : ℕ) : ℂ) * coefficient s (m + 1) * z ^ m :=
  Finset.sum_range_succ _ _

@[simp] theorem polynomial_at_zero (s : ℂ) (m : ℕ) : polynomial s m 0 = 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [polynomial_succ, ih]; simp

/-- All but two terms cancel in the finite differential residual. -/
theorem polynomial_residual (s z : ℂ) (m : ℕ) :
    (1 + z / 300) * slope s m z - (s / 90000) * z * polynomial s m z =
      -((m + 1 : ℕ) : ℂ) * coefficient s (m + 1) * z ^ m -
        (s / 90000) * coefficient s m * z ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [slope_succ, polynomial_succ]
    have hc := coefficient_recurrence s m
    push_cast at hc ih ⊢
    rw [show m + 1 + 1 = m + 2 by omega]
    linear_combination ih + z ^ (m + 1) * hc

/-- The derivative is taken along the actual real block coordinate. -/
theorem hasDerivAt_polynomial (s : ℂ) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => polynomial s m y) (slope s m x) x := by
  induction m with
  | zero => simpa using (hasDerivAt_const x (1 : ℂ))
  | succ m ih =>
    simp only [polynomial_succ, slope_succ]
    convert! ih.add (((hasDerivAt_id x).ofReal_comp.pow (m + 1)).const_mul
      (coefficient s (m + 1))) using 1
    norm_num
    ring

/-- Positive rational majorants for the shared coefficients. -/
def majorantPair : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | j + 1 =>
      let c := majorantPair j
      (c.2, (c.1 / 4 + ((j + 1 : ℕ) : ℚ) / 300 * c.2) / (j + 2))

/-- The corresponding coefficient majorant. -/
def majorant (j : ℕ) : ℚ := (majorantPair j).1

theorem majorantPair_nonneg (j : ℕ) :
    0 ≤ (majorantPair j).1 ∧ 0 ≤ (majorantPair j).2 := by
  induction j with
  | zero => norm_num [majorantPair]
  | succ j ih =>
    constructor
    · exact ih.2
    · change 0 ≤ ((majorantPair j).1 / 4 + ((j + 1 : ℕ) : ℚ) / 300 *
        (majorantPair j).2) / (j + 2)
      rcases ih with ⟨h0, h1⟩
      positivity

theorem norm_coefficientPair_le {s : ℂ} (hs : ‖s‖ ≤ 22500) (j : ℕ) :
    ‖(coefficientPair s j).1‖ ≤ ((majorantPair j).1 : ℝ) ∧
      ‖(coefficientPair s j).2‖ ≤ ((majorantPair j).2 : ℝ) := by
  induction j with
  | zero => norm_num [coefficientPair, majorantPair]
  | succ j ih =>
    constructor
    · exact ih.2
    · dsimp only [coefficientPair, majorantPair]
      push_cast
      rw [norm_div]
      have hnorm : ‖(j : ℂ) + 2‖ = (j : ℝ) + 2 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_add,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hnorm]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ‖s / 90000 * (coefficientPair s j).1‖ +
            ‖((j : ℂ) + 1) / 300 * (coefficientPair s j).2‖ := norm_sub_le _ _
        _ ≤ (22500 / 90000 : ℝ) * ((majorantPair j).1 : ℝ) +
            ((j : ℝ) + 1) / 300 * ((majorantPair j).2 : ℝ) := by
          simp only [norm_mul, norm_div, Complex.norm_ofNat]
          have hn : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          rw [hn]
          exact add_le_add
            (mul_le_mul (by linarith : ‖s‖ / 90000 ≤ 22500 / 90000) ih.1
              (norm_nonneg _) (by norm_num))
            (mul_le_mul_of_nonneg_left ih.2 (by positivity))
        _ = _ := by ring

theorem norm_coefficient_le {s : ℂ} (hs : ‖s‖ ≤ 22500) (j : ℕ) :
    ‖coefficient s j‖ ≤ (majorant j : ℝ) := (norm_coefficientPair_le hs j).1

/-- The exact logarithmic correction on the normalized block. -/
def correction (x : ℝ) : ℝ := x / 300 - Real.log (1 + x / 300)

theorem correction_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ correction x ∧ correction x ≤ 1 / 180000 := by
  have ht : 0 ≤ x / 300 := div_nonneg hx.1 (by norm_num)
  have he := VinogradovKorobovLogPhase.logarithm_eq_polynomial_add_remainder 1 ht
  simp [VinogradovKorobovLogPhase.logarithmPolynomial] at he
  have h0 := VinogradovKorobovLogPhase.remainder_nonneg 1 ht
  have h1 := VinogradovKorobovLogPhase.remainder_le 1 ht
  norm_num at h1
  dsimp [correction]
  constructor
  · linarith
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

theorem hasDerivAt_correction {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt correction (x / (90000 * (1 + x / 300))) x := by
  have hd := (hasDerivAt_id x).div_const 300
  have he := hd.sub ((hd.const_add 1).log (by positivity : 1 + x / 300 ≠ 0))
  convert! he using 1
  dsimp [correction, id]
  field_simp [show 1 + x / 300 ≠ 0 by positivity]
  ring

/-- The exact block correction to the geometric sequence. -/
def model (s : ℂ) (x : ℝ) : ℂ := Complex.exp (s * (correction x : ℂ))

theorem norm_model_le {s : ℂ} (hs : ‖s‖ ≤ 22500) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖model s x‖ ≤ 3 := by
  rw [model, Complex.norm_exp]
  have hc := correction_bounds hx
  have hb : (s * (correction x : ℂ)).re ≤ 1 := by
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc
      s.re * correction x ≤ 22500 * (1 / 180000) :=
        mul_le_mul ((Complex.re_le_norm s).trans hs) hc.2 hc.1 (by norm_num)
      _ ≤ 1 := by norm_num
  exact (Real.exp_le_exp.mpr hb).trans (Real.exp_one_lt_three.le)

theorem norm_inverse_model_le {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ‖model (-s) x‖ ≤ 1 := by
  rw [model, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (correction_bounds hx).1

theorem hasDerivAt_model (s : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (model s)
      ((s / 90000) * (x : ℂ) / (1 + (x : ℂ) / 300) * model s x) x := by
  have hd := ((hasDerivAt_correction hx).ofReal_comp.const_mul s).cexp
  convert! hd using 1
  push_cast
  dsimp only [model]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

private theorem denominator_norm {x : ℝ} (hx : 0 ≤ x) :
    ‖1 + (x : ℂ) / 300‖ = 1 + x / 300 := by
  rw [show (1 : ℂ) + (x : ℂ) / 300 = ((1 + x / 300 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Dividing by the exact integrating factor leaves only the finite residual. -/
theorem hasDerivAt_normalizedPolynomial (s : ℂ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => polynomial s m y * model (-s) y)
      (((1 + (x : ℂ) / 300) * slope s m x -
        (s / 90000) * x * polynomial s m x) / (1 + (x : ℂ) / 300) * model (-s) x) x := by
  have hd := (hasDerivAt_polynomial s m x).mul (hasDerivAt_model (-s) hx)
  have hn : (1 : ℂ) + (x : ℂ) / 300 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [denominator_norm hx]
    positivity
  convert! hd using 1
  generalize (1 : ℂ) + (x : ℂ) / 300 = d at *
  field_simp
  ring

/-- The two uncancelled coefficients give the full finite error budget. -/
def errorBudget (m : ℕ) : ℚ :=
  3 * (((m + 1 : ℕ) : ℚ) * majorant (m + 1) + majorant m / 4)

private theorem norm_residual_le {s : ℂ} (hs : ‖s‖ ≤ 22500) (m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖(1 + (x : ℂ) / 300) * slope s m x - (s / 90000) * x * polynomial s m x‖ ≤
      (m + 1 : ℝ) * (majorant (m + 1) : ℝ) + (majorant m : ℝ) / 4 := by
  rw [polynomial_residual]
  have hxnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_nonneg hx.1]
  have hpow (j : ℕ) : ‖(x : ℂ)‖ ^ j ≤ 1 := by
    rw [hxnorm]; exact pow_le_one₀ hx.1 hx.2
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, norm_neg, Complex.norm_natCast, norm_pow, norm_div, Complex.norm_ofNat]
  push_cast
  apply add_le_add
  · calc
      _ ≤ (m + 1 : ℝ) * ‖coefficient s (m + 1)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hpow m) (by positivity)
      _ ≤ (m + 1 : ℝ) * (majorant (m + 1) : ℝ) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (norm_coefficient_le hs _) (by positivity)
  · calc
      _ ≤ (‖s‖ / 90000) * ‖coefficient s m‖ * 1 :=
        mul_le_mul_of_nonneg_left (hpow (m + 1)) (by positivity)
      _ ≤ (22500 / 90000 : ℝ) * (majorant m : ℝ) := by
        rw [mul_one]
        exact mul_le_mul (by linarith) (norm_coefficient_le hs _) (norm_nonneg _) (by norm_num)
      _ = _ := by ring

/-- Uniform approximation error for the actual exponential/logarithmic model. -/
theorem norm_model_sub_polynomial_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    (m : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖model s x - polynomial s m x‖ ≤ (errorBudget m : ℝ) := by
  let B : ℝ := (m + 1 : ℝ) * (majorant (m + 1) : ℝ) + (majorant m : ℝ) / 4
  have hB : 0 ≤ B := by
    have h0 : (0 : ℝ) ≤ (majorant m : ℝ) := by
      exact_mod_cast (majorantPair_nonneg m).1
    have h1 : (0 : ℝ) ≤ (majorant (m + 1) : ℝ) := by
      exact_mod_cast (majorantPair_nonneg (m + 1)).1
    dsimp [B]; positivity
  have hb : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖((1 + (t : ℂ) / 300) * slope s m t - (s / 90000) * t * polynomial s m t) /
        (1 + (t : ℂ) / 300) * model (-s) t‖ ≤ B := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    rw [norm_mul, norm_div, denominator_norm ht.1]
    calc
      _ ≤ B / (1 + t / 300) * 1 :=
        mul_le_mul (div_le_div_of_nonneg_right (norm_residual_le hs m ht') (by positivity))
          (norm_inverse_model_le hs0 ht') (norm_nonneg _) (by positivity)
      _ ≤ B := by
        rw [mul_one]
        apply div_le_self hB
        linarith [ht.1]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hasDerivAt_normalizedPolynomial s m ht.1).hasDerivWithinAt) hb x hx
  have h0 : model (-s) 0 = 1 := by simp [model, correction]
  rw [Complex.ofReal_zero, polynomial_at_zero, h0, one_mul, sub_zero] at hm
  have hsmall : ‖polynomial s m x * model (-s) x - 1‖ ≤ B :=
    hm.trans (mul_le_of_le_one_right hB hx.2)
  have hinv : model (-s) x * model s x = 1 := by
    rw [model, model, ← Complex.exp_add]
    simp
  calc
    ‖model s x - polynomial s m x‖ = ‖polynomial s m x - model s x‖ := norm_sub_rev _ _
    _ = ‖(polynomial s m x * model (-s) x - 1) * model s x‖ := by
      rw [sub_mul, mul_assoc, hinv, mul_one, one_mul]
    _ ≤ B * 3 := by
      rw [norm_mul]
      exact mul_le_mul hsmall (norm_model_le hs hx) (norm_nonneg _) hB
    _ = _ := by simp only [errorBudget, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_one]; dsimp [B]; ring

/-- A kernel-checked rational budget for degree eighteen. -/
theorem errorBudget_eighteen : errorBudget 18 ≤ (1 / 25000000000000 : ℚ) := by
  decide +kernel

/-- An absolute error at most `4e-14` throughout every normalized block. -/
theorem norm_model_sub_eighteen_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs : ‖s‖ ≤ 22500)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖model s x - polynomial s 18 x‖ ≤ 1 / 25000000000000 := by
  exact (norm_model_sub_polynomial_le hs0 hs 18 hx).trans
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr errorBudget_eighteen)

end
end RiemannGaussian.ZetaBlockTaylor
