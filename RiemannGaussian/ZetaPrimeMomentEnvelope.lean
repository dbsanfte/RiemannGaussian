/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeLogMoments

/-!
# Arithmetic envelopes for logarithmic prime moments

An elementary exponential-series inequality controls the actual factorial
log kernels before summation. These bounds apply to omitted arithmetic
pieces while the full complex prime carrier remains available upstream.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The factorial log kernel with its complete complex prime phase. -/
def zetaPrimeLogKernel (k : ℕ) (s : ℂ) (m : ℕ) : ℂ :=
  ((Real.log m : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s m

/-- The scalar exponential weight used to bound an arithmetic series. -/
def zetaPrimeExpWeight (σ : ℝ) (m : ℕ) : ℝ := Real.exp (-σ * Real.log m)

/-- The feature norm depends only on the real part of its exponent. -/
theorem norm_zetaPrimeFeature (s : ℂ) (m : ℕ) :
    ‖zetaPrimeFeature s m‖ = zetaPrimeExpWeight s.re m := by
  simp only [zetaPrimeFeature, zetaPrimeExpWeight, Complex.norm_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]

/-- The exact norm of the log kernel retains its factorial normalization. -/
theorem norm_zetaPrimeLogKernel (k : ℕ) (s : ℂ) (m : ℕ) :
    ‖zetaPrimeLogKernel k s m‖ =
      (Real.log m) ^ k / (k.factorial : ℝ) * zetaPrimeExpWeight s.re m := by
  simp only [zetaPrimeLogKernel, norm_mul, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg m),
    Complex.norm_natCast, norm_zetaPrimeFeature]

/-- The exponential series gives an elementary envelope for every
factorial log moment, with an arbitrary positive exponential tilt. -/
theorem logMoment_exp_envelope (k : ℕ) {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) (σ : ℝ) :
    t ^ k / (k.factorial : ℝ) * Real.exp (-σ * t) ≤
      q⁻¹ ^ k * Real.exp (-(σ - q) * t) := by
  have h := mul_le_mul_of_nonneg_right
    (Real.pow_div_factorial_le_exp (q * t) (mul_nonneg hq.le ht) k)
    (show 0 ≤ q⁻¹ ^ k * Real.exp (-σ * t) by positivity)
  have he : Real.exp (q * t) * (q⁻¹ ^ k * Real.exp (-σ * t)) =
      q⁻¹ ^ k * Real.exp (-(σ - q) * t) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he] at h
  calc
    _ = (q * t) ^ k / (k.factorial : ℝ) * (q⁻¹ ^ k * Real.exp (-σ * t)) := by
      rw [mul_pow, inv_pow]
      field_simp
    _ ≤ _ := h

/-- An independent bound for each actual complex log kernel. -/
theorem norm_zetaPrimeLogKernel_le (k : ℕ) (s : ℂ) (m : ℕ) {q : ℝ} (hq : 0 < q) :
    ‖zetaPrimeLogKernel k s m‖ ≤ q⁻¹ ^ k * zetaPrimeExpWeight (s.re - q) m := by
  rw [norm_zetaPrimeLogKernel]
  exact logMoment_exp_envelope k (Real.log_natCast_nonneg m) hq s.re

/-- For coefficients vanishing at zero, the exponential carrier agrees
with the genuine real-axis Dirichlet series term. -/
theorem LSeries_term_eq_expWeight (f : ℕ → ℝ) (hf0 : f 0 = 0) (σ : ℝ) (m : ℕ) :
    LSeries.term (fun n ↦ (f n : ℂ)) (σ : ℂ) m =
      ((f m * zetaPrimeExpWeight σ m : ℝ) : ℂ) := by
  by_cases hm : m = 0
  · subst m
    simp [hf0]
  · rw [LSeries.term_of_ne_zero hm, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hm),
      ← Complex.natCast_log, ← Complex.exp_neg]
    simp only [zetaPrimeExpWeight, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    congr 2
    ring

/-- Absolute convergence of the real-axis Dirichlet series transfers to
the exponential arithmetic weights, including the zero coefficient. -/
theorem summable_zetaPrimeExpWeight_mul (f : ℕ → ℝ) (hf0 : f 0 = 0) {σ : ℝ}
    (hs : LSeriesSummable (fun n ↦ (f n : ℂ)) (σ : ℂ)) :
    Summable (fun m ↦ f m * zetaPrimeExpWeight σ m) := by
  have he : LSeries.term (fun n ↦ (f n : ℂ)) (σ : ℂ) =
      (fun m ↦ ((f m * zetaPrimeExpWeight σ m : ℝ) : ℂ)) :=
    funext (LSeries_term_eq_expWeight f hf0 σ)
  rw [LSeriesSummable, he] at hs
  exact Complex.summable_ofReal.mp hs

/-- Positive coefficient weights at a smaller real exponent dominate
the full complex log-weighted series. -/
theorem summable_mul_zetaPrimeLogKernel (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m)
    (k : ℕ) (s : ℂ) {q : ℝ} (hq : 0 < q)
    (hs : Summable (fun m ↦ f m * zetaPrimeExpWeight (s.re - q) m)) :
    Summable (fun m ↦ (f m : ℂ) * zetaPrimeLogKernel k s m) := by
  apply (hs.mul_left (q⁻¹ ^ k)).of_norm_bounded
  intro m
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf m)]
  calc
    _ ≤ f m * (q⁻¹ ^ k * zetaPrimeExpWeight (s.re - q) m) :=
      mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le k s m hq) (hf m)
    _ = _ := by ring

/-- The complete complex arithmetic moment has a quantitative envelope
obtained only from absolute convergence at the tilted real exponent. -/
theorem norm_tsum_mul_zetaPrimeLogKernel_le (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m)
    (k : ℕ) (s : ℂ) {q : ℝ} (hq : 0 < q)
    (hs : Summable (fun m ↦ f m * zetaPrimeExpWeight (s.re - q) m)) :
    ‖∑' m, (f m : ℂ) * zetaPrimeLogKernel k s m‖ ≤
      q⁻¹ ^ k * ∑' m, f m * zetaPrimeExpWeight (s.re - q) m := by
  calc
    _ ≤ ∑' m, q⁻¹ ^ k * (f m * zetaPrimeExpWeight (s.re - q) m) := by
      apply (norm_tsum_le_tsum_norm (summable_mul_zetaPrimeLogKernel f hf k s hq hs).norm).trans
      apply Summable.tsum_le_tsum
      · intro m
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf m)]
        calc
          _ ≤ f m * (q⁻¹ ^ k * zetaPrimeExpWeight (s.re - q) m) :=
            mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le k s m hq) (hf m)
          _ = _ := by ring
      · exact (summable_mul_zetaPrimeLogKernel f hf k s hq hs).norm
      · exact hs.mul_left _
    _ = _ := tsum_mul_left

end

end RiemannGaussian
