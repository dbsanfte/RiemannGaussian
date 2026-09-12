/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseArithmetic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The actual logarithmic zeta series with every prime-power phase

On the half-plane of absolute convergence, the real logarithm of the
norm of zeta is exactly the cosine series with coefficient
`Lambda(n)/log(n)`. Its positive arithmetic mass controls every ordinate.
The exponential reconstruction avoids choosing a complex logarithm branch.
These identities supply the original right boundary for vertical averaging.
-/

namespace RiemannGaussian.ZetaLogPrimeSeries
noncomputable section
open Complex ArithmeticFunction

/-- The logarithmic Euler coefficient retains every prime power with
its reciprocal exponent, and vanishes at zero and one. -/
def coefficient (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.log n

/-- Every original logarithmic Euler coefficient is nonnegative. -/
theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- The logarithmic Euler coefficients are uniformly at most one. -/
theorem coefficient_le_one (n : ℕ) : coefficient n ≤ 1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num [coefficient]
  · apply (div_le_one (Real.log_pos (by exact_mod_cast (lt_of_not_ge hn)))).mpr
    exact ArithmeticFunction.vonMangoldt_le_log

/-- The literal complex logarithmic Euler series is absolutely convergent
on the whole right half-plane. -/
theorem summable_series {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coefficient n : ℂ)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
  intro n _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (coefficient_nonneg n)]
  exact coefficient_le_one n

/-- The actual zeta function is the exponential of its complete prime-power
series. No complex logarithm branch is selected. -/
theorem exp_series_eq {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (fun n => (coefficient n : ℂ)) s) = riemannZeta s := by
  simpa only [coefficient, Complex.ofReal_div] using riemannZeta_eq_exp_LSeries hs

/-- Taking the norm logarithm of the exponential reconstruction retains
the exact real part of the whole convergent logarithmic Euler series. -/
theorem log_norm_eq {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ = (LSeries (fun n => (coefficient n : ℂ)) s).re := by
  rw [← exp_series_eq hs, Complex.norm_exp, Real.log_exp]

/-- The positive amplitude of the original prime-power logarithmic term. -/
def weight (σ : ℝ) (n : ℕ) : ℝ := coefficient n * Real.exp (-σ * Real.log n)

/-- All logarithmic prime-power amplitudes are nonnegative. -/
theorem weight_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ weight σ n :=
  mul_nonneg (coefficient_nonneg n) (Real.exp_pos _).le

/-- The full complex logarithmic term retains its phase before taking
a real part or an absolute value. -/
theorem term_eq_phase (σ t : ℝ) (n : ℕ) :
    LSeries.term (fun m => (coefficient m : ℂ)) ((σ : ℂ) + I * t) n =
      (weight σ n : ℂ) * Complex.exp (-(I * ((t * Real.log n : ℝ) : ℂ))) := by
  by_cases hn : n = 0
  · subst n
    simp [weight, coefficient]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log,
      ← Complex.exp_neg]
    have he : -((Real.log (n : ℝ) : ℂ) * ((σ : ℂ) + I * t)) =
        ((-σ * Real.log (n : ℝ) : ℝ) : ℂ) + -(I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [he, Complex.exp_add, ← Complex.ofReal_exp]
    unfold weight
    push_cast
    ring

/-- The literal real logarithmic term is its positive prime-power
amplitude times the original cosine phase. -/
theorem term_re (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun m => (coefficient m : ℂ)) ((σ : ℂ) + I * t) n).re =
      weight σ n * Real.cos (t * Real.log n) := by
  rw [term_eq_phase, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [neg_re, neg_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, neg_zero, Real.exp_zero, Real.cos_neg]

/-- The complete cosine series sums to the actual norm logarithm of zeta.
All prime powers, including their reciprocal exponent weights, are kept. -/
theorem hasSum_log_norm {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasSum (fun n => weight σ n * Real.cos (t * Real.log n))
      (Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖) := by
  have hs := summable_series (s := (σ : ℂ) + I * t) (by simpa using hσ)
  rw [log_norm_eq (by simpa using hσ), LSeries, Complex.re_tsum hs]
  have h := (Complex.reCLM.summable hs).hasSum
  simpa only [Complex.reCLM_apply, term_re] using h

/-- The actual positive arithmetic mass is the real-axis norm logarithm. -/
theorem hasSum_weight {σ : ℝ} (hσ : 1 < σ) :
    HasSum (weight σ) (Real.log ‖riemannZeta (σ : ℂ)‖) := by
  simpa only [ofReal_zero, mul_zero, add_zero, zero_mul, Real.cos_zero, mul_one]
    using hasSum_log_norm hσ 0

/-- Absolute values of the original logarithmic zeta carrier are bounded
by the same convergent prime-power mass at every ordinate. -/
theorem abs_log_norm_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    |Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖| ≤ Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hs := hasSum_log_norm hσ t
  have hw := hasSum_weight hσ
  rw [← hs.tsum_eq, ← hw.tsum_eq]
  calc
    _ ≤ ∑' n, ‖weight σ n * Real.cos (t * Real.log n)‖ := norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' n, weight σ n := hs.summable.norm.tsum_le_tsum (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg σ n)]
      exact mul_le_of_le_one_right (weight_nonneg σ n) (Real.abs_cos_le_one _)) hw.summable

end
end RiemannGaussian.ZetaLogPrimeSeries
