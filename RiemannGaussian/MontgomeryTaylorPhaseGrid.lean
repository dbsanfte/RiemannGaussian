/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexApproximateOrbit
import RiemannGaussian.MontgomeryTaylorNumericalKernel

/-!
# Base rotation for a certified trigonometric grid

Only the base angle needs transcendental interval evaluation. Integer
recurrence checks then control the entire phase grid by the unitary-orbit
error theorem. Every numerical tactic explicitly uses Lean kernel checking.
-/

namespace RiemannGaussian.MontgomeryTaylorPhaseGrid
noncomputable section
set_option leancert.trust "kernel"

/-- Integer fixed-point scale used by the phase table. -/
def scale : ℕ := 1000000000000000000

/-- Approximate cosine numerator for the base rotation. -/
def baseCos : ℤ := 999999922893716607

/-- Approximate sine numerator for the base rotation. -/
def baseSin : ℤ := 392699071605535

/-- Complex value encoded by two fixed-point integer coordinates. -/
def encode (c s : ℤ) : ℂ := ⟨(c : ℝ) / scale, (s : ℝ) / scale⟩

/-- Rational approximation to one rotation through `pi / 8000`. -/
def base : ℂ := encode baseCos baseSin

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
set_option leancert.trust.kernelHeartbeats 10000000 in
private theorem cos_lower : ∀ r ∈ Set.Icc ((31415926535897932 : ℝ) / 10000000000000000)
    (31415926535897933 / 10000000000000000), (999999922893716607 : ℝ) / 1000000000000000000 ≤ Real.cos (r / 8000) := by
  certify_bound 8 (trust := kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
set_option leancert.trust.kernelHeartbeats 10000000 in
private theorem cos_upper : ∀ r ∈ Set.Icc ((31415926535897932 : ℝ) / 10000000000000000)
    (31415926535897933 / 10000000000000000), Real.cos (r / 8000) ≤ (999999922893716608 : ℝ) / 1000000000000000000 := by
  certify_bound 8 (trust := kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
set_option leancert.trust.kernelHeartbeats 10000000 in
private theorem sin_lower : ∀ r ∈ Set.Icc ((31415926535897932 : ℝ) / 10000000000000000)
    (31415926535897933 / 10000000000000000), (392699071605535 : ℝ) / 1000000000000000000 ≤ Real.sin (r / 8000) := by
  certify_bound 8 (trust := kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
set_option leancert.trust.kernelHeartbeats 10000000 in
private theorem sin_upper : ∀ r ∈ Set.Icc ((31415926535897932 : ℝ) / 10000000000000000)
    (31415926535897933 / 10000000000000000), Real.sin (r / 8000) ≤ (392699071605536 : ℝ) / 1000000000000000000 := by
  certify_bound 8 (trust := kernel)

/-- The only transcendental base error required by the integer grid. -/
theorem base_error :
    ‖base - Complex.exp (((Real.pi / 8000 : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / (scale : ℝ) := by
  have hp : Real.pi ∈ Set.Icc ((31415926535897932 : ℝ) / 10000000000000000)
      (31415926535897933 / 10000000000000000) := by
    constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]
  have hc0 := cos_lower Real.pi hp
  have hc1 := cos_upper Real.pi hp
  have hs0 := sin_lower Real.pi hp
  have hs1 := sin_upper Real.pi hp
  have hc : |(base - Complex.exp (((Real.pi / 8000 : ℝ) : ℂ) * Complex.I)).re| ≤
      1 / (scale : ℝ) := by
    simp only [base, encode, baseCos, Complex.sub_re, Complex.exp_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, Real.exp_zero, one_mul]
    norm_num only [Int.cast_ofNat, scale, Nat.cast_ofNat]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : |(base - Complex.exp (((Real.pi / 8000 : ℝ) : ℂ) * Complex.I)).im| ≤
      1 / (scale : ℝ) := by
    simp only [base, encode, baseSin, Complex.sub_im, Complex.exp_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, Real.exp_zero, one_mul]
    norm_num only [Int.cast_ofNat, scale, Nat.cast_ofNat]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := ComplexApproximateOrbit.norm_le_of_components hc hs
  exact h.trans_eq (by ring)

/-- An integer coordinate bound controls the encoded complex norm. -/
theorem encode_norm_le_two {c s : ℤ}
    (h : |c| + |s| ≤ 2 * (scale : ℤ)) : ‖encode c s‖ ≤ 2 := by
  have hR : |(c : ℝ)| + |(s : ℝ)| ≤ 2 * (scale : ℝ) := by exact_mod_cast h
  have hnorm := Complex.norm_le_abs_re_add_abs_im (encode c s)
  simp only [encode, abs_div,
    abs_of_nonneg (Nat.cast_nonneg scale : (0 : ℝ) ≤ (scale : ℝ))] at hnorm
  have hS : (0 : ℝ) < scale := by norm_num [scale]
  have hsum : |(c : ℝ)| / scale + |(s : ℝ)| / scale ≤ 2 := by
    rw [← add_div, div_le_iff₀ hS]
    exact hR
  exact hnorm.trans hsum

/-- Integer residuals certify one approximate rotation without evaluating
any trigonometric function at the new grid point. -/
theorem encode_step_error {c s c' s' : ℤ}
    (hc : |(scale : ℤ) * c' - (baseCos * c - baseSin * s)| ≤ scale)
    (hs : |(scale : ℤ) * s' - (baseSin * c + baseCos * s)| ≤ scale) :
    ‖encode c' s' - base * encode c s‖ ≤ 2 / (scale : ℝ) := by
  have hS : (0 : ℝ) < scale := by norm_num [scale]
  have hcR : |(scale : ℝ) * (c' : ℝ) -
      ((baseCos : ℝ) * (c : ℝ) - (baseSin : ℝ) * (s : ℝ))| ≤ scale := by
    exact_mod_cast hc
  have hsR : |(scale : ℝ) * (s' : ℝ) -
      ((baseSin : ℝ) * (c : ℝ) + (baseCos : ℝ) * (s : ℝ))| ≤ scale := by
    exact_mod_cast hs
  have hreal : (encode c' s' - base * encode c s).re =
      ((scale : ℝ) * c' - ((baseCos : ℝ) * c - (baseSin : ℝ) * s)) / scale ^ 2 := by
    simp only [encode, base, Complex.sub_re, Complex.mul_re]
    field_simp
  have himag : (encode c' s' - base * encode c s).im =
      ((scale : ℝ) * s' - ((baseSin : ℝ) * c + (baseCos : ℝ) * s)) / scale ^ 2 := by
    simp only [encode, base, Complex.sub_im, Complex.mul_im]
    field_simp
    ring
  have hc' : |(encode c' s' - base * encode c s).re| ≤ 1 / (scale : ℝ) := by
    rw [hreal, abs_div, abs_of_nonneg (sq_nonneg (scale : ℝ))]
    calc
      _ ≤ (scale : ℝ) / scale ^ 2 := div_le_div_of_nonneg_right hcR (sq_nonneg _)
      _ = _ := by field_simp
  have hs' : |(encode c' s' - base * encode c s).im| ≤ 1 / (scale : ℝ) := by
    rw [himag, abs_div, abs_of_nonneg (sq_nonneg (scale : ℝ))]
    calc
      _ ≤ (scale : ℝ) / scale ^ 2 := div_le_div_of_nonneg_right hsR (sq_nonneg _)
      _ = _ := by field_simp
  have h := ComplexApproximateOrbit.norm_le_of_components hc' hs'
  exact h.trans_eq (by ring)

/-- A table is certified by integer coordinate and recurrence checks.
The conclusion encloses both trigonometric coordinates at every grid point. -/
theorem grid_error_of_integer_checks (c s : ℕ → ℤ) {N : ℕ}
    (hc0 : c 0 = scale) (hs0 : s 0 = 0)
    (hsize : ∀ i < N, |c i| + |s i| ≤ 2 * (scale : ℤ))
    (hstepC : ∀ i < N,
      |(scale : ℤ) * c (i + 1) - (baseCos * c i - baseSin * s i)| ≤ scale)
    (hstepS : ∀ i < N,
      |(scale : ℤ) * s (i + 1) - (baseSin * c i + baseCos * s i)| ≤ scale)
    {n : ℕ} (hn : n ≤ N) :
    |(c n : ℝ) / scale - Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤
        6 * n / (scale : ℝ) ∧
      |(s n : ℝ) / scale - Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤
        6 * n / (scale : ℝ) := by
  have hstart : encode (c 0) (s 0) = 1 := by
    rw [hc0, hs0]
    apply Complex.ext <;> norm_num [encode, scale]
  have h := ComplexApproximateOrbit.trigonometric_grid_error
    (Real.pi / 8000) base (fun i => encode (c i) (s i))
    (by norm_num [scale] : (0 : ℝ) ≤ 2 / (scale : ℝ)) base_error hstart
    (fun i hi => encode_norm_le_two (hsize i hi))
    (fun i hi => encode_step_error (hstepC i hi) (hstepS i hi)) hn
  simp only [encode] at h
  have hbudget : (n : ℝ) * (2 / (scale : ℝ) * 2 + 2 / (scale : ℝ)) =
      6 * n / (scale : ℝ) := by ring
  rw [hbudget] at h
  exact h

end
end RiemannGaussian.MontgomeryTaylorPhaseGrid
