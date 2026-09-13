/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFilterCalculus

/-!
# Localization of every fixed factorial filter

After removing the common factorial monomial, a fixed complex filter on
`c * N ≤ t ≤ c * N + h` converges uniformly to its polynomial value at `c`.
The exact complex factorization is retained. In particular a filter
normalized at `1/u` cannot suppress the local kernel near `N/u`.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The real factorial ratio in the `k`th coefficient after extracting
the common moment monomial. -/
def zetaFactorialLocalRatio (N k : ℕ) (t : ℝ) : ℝ :=
  t ^ k * (N.factorial : ℝ) / ((N + k).factorial : ℝ)

/-- The full complex polynomial amplitude, with every coefficient retained. -/
def zetaFactorialLocalAmplitude (p : Polynomial ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * (zetaFactorialLocalRatio N k t : ℂ)

/-- Exact factorization of the original factorial polynomial, including
zero logarithmic coordinate and moment order zero. -/
theorem zetaFactorialPolynomial_eq_localAmplitude (p : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaFactorialPolynomial p N (t : ℂ) =
      ((t : ℂ) ^ N / (N.factorial : ℂ)) * zetaFactorialLocalAmplitude p N t := by
  unfold zetaFactorialPolynomial zetaFactorialLocalAmplitude Polynomial.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hN : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  simp only [zetaFactorialLocalRatio, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_natCast, pow_add]
  field_simp

/-- The complete prime kernel is the unfiltered kernel times the exact
local amplitude; both complex phases remain unchanged. -/
theorem zetaPrimeFilterKernel_eq_one_mul_localAmplitude
    (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (x : ℝ) :
    zetaPrimeFilterKernel p N s x =
      zetaPrimeFilterKernel 1 N s x * zetaFactorialLocalAmplitude p N (Real.log x) := by
  have h1 : zetaFactorialPolynomial 1 N (Real.log x : ℂ) =
      (Real.log x : ℂ) ^ N / (N.factorial : ℂ) := by
    simpa only [Polynomial.monomial_zero_one, Nat.add_zero, one_mul] using
      zetaFactorialPolynomial_monomial 0 1 N (Real.log x : ℂ)
  rw [zetaPrimeFilterKernel, zetaFactorialPolynomial_eq_localAmplitude,
    zetaPrimeFilterKernel, h1]
  ring

/-- Each fixed factorial ratio converges along any fixed affine logarithmic
coordinate. The limit is independent of the bounded displacement. -/
theorem tendsto_zetaFactorialLocalRatio (k : ℕ) (c a : ℝ) :
    Tendsto (fun N : ℕ ↦ zetaFactorialLocalRatio N k (c * N + a)) atTop (𝓝 (c ^ k)) := by
  induction k with
  | zero =>
    simp [zetaFactorialLocalRatio, Nat.factorial_ne_zero]
  | succ k ih =>
    have hr : Tendsto (fun N : ℕ ↦ (c * N + a) / (N + k + 1)) atTop (𝓝 c) := by
      simpa only [one_mul, div_one, add_comm, add_left_comm, add_assoc] using
        tendsto_add_mul_div_add_mul_atTop_nhds a ((k : ℝ) + 1) c (d := 1) one_ne_zero
    have he (N : ℕ) : zetaFactorialLocalRatio N (k + 1) (c * N + a) =
        zetaFactorialLocalRatio N k (c * N + a) * ((c * N + a) / (N + k + 1)) := by
      unfold zetaFactorialLocalRatio
      rw [show N + (k + 1) = (N + k) + 1 by omega, Nat.factorial_succ, pow_succ]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simpa only [he, pow_succ] using ih.mul hr

/-- For nonnegative logarithmic coordinates the individual real ratios
are monotone. Complex polynomial coefficients are not assumed positive. -/
theorem zetaFactorialLocalRatio_mono (N k : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    zetaFactorialLocalRatio N k a ≤ zetaFactorialLocalRatio N k b := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab k) (by positivity)) (by positivity)

/-- A concrete error allowance using the two endpoints of the logarithmic
window. It controls all interior coordinates simultaneously. -/
def zetaFactorialLocalError (p : Polynomial ℂ) (N : ℕ) (c h : ℝ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ *
    (|zetaFactorialLocalRatio N k (c * N) - c ^ k| +
      |zetaFactorialLocalRatio N k (c * N + h) - c ^ k|)

/-- Every fixed polynomial has a vanishing common endpoint allowance. -/
theorem tendsto_zetaFactorialLocalError (p : Polynomial ℂ) (c h : ℝ) :
    Tendsto (fun N : ℕ ↦ zetaFactorialLocalError p N c h) atTop (𝓝 0) := by
  have hlo (k : ℕ) : Tendsto
      (fun N : ℕ ↦ |zetaFactorialLocalRatio N k (c * N) - c ^ k|) atTop (𝓝 0) := by
    simpa only [add_zero, sub_self, abs_zero] using
      ((tendsto_zetaFactorialLocalRatio k c 0).sub_const (c ^ k)).abs
  have hhi (k : ℕ) : Tendsto
      (fun N : ℕ ↦ |zetaFactorialLocalRatio N k (c * N + h) - c ^ k|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_zetaFactorialLocalRatio k c h).sub_const (c ^ k)).abs
  simpa only [zetaFactorialLocalError, add_zero, mul_zero, Finset.sum_const_zero] using
    tendsto_finsetSum p.support (fun k _ ↦ ((hlo k).add (hhi k)).const_mul ‖p.coeff k‖)

/-- The original complex amplitude is uniformly close to polynomial
evaluation on the entire logarithmic window. No coefficient sign is dropped
until this named error estimate. -/
theorem norm_zetaFactorialLocalAmplitude_sub_eval_le (p : Polynomial ℂ) (N : ℕ)
    {c h t : ℝ} (hc : 0 ≤ c) (ht : c * N ≤ t) (htu : t ≤ c * N + h) :
    ‖zetaFactorialLocalAmplitude p N t - p.eval (c : ℂ)‖ ≤
      zetaFactorialLocalError p N c h := by
  rw [zetaFactorialLocalAmplitude, Polynomial.eval_eq_sum, Polynomial.sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hlo := zetaFactorialLocalRatio_mono N k (mul_nonneg hc (Nat.cast_nonneg N)) ht
  have hhi := zetaFactorialLocalRatio_mono N k
    ((mul_nonneg hc (Nat.cast_nonneg N)).trans ht) htu
  have hb : |zetaFactorialLocalRatio N k t - c ^ k| ≤
      |zetaFactorialLocalRatio N k (c * N) - c ^ k| +
        |zetaFactorialLocalRatio N k (c * N + h) - c ^ k| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (zetaFactorialLocalRatio N k (c * N) - c ^ k),
        abs_nonneg (zetaFactorialLocalRatio N k (c * N + h) - c ^ k)]
    · linarith [le_abs_self (zetaFactorialLocalRatio N k (c * N + h) - c ^ k),
        abs_nonneg (zetaFactorialLocalRatio N k (c * N) - c ^ k)]
  rw [← mul_sub, norm_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- Every fixed filter normalized at a positive real coordinate is
uniformly close to one throughout its corresponding logarithmic window. -/
theorem eventually_zetaFactorialLocalAmplitude_near_one (p : Polynomial ℂ)
    {c : ℝ} (hc : 0 ≤ c) (hp : p.eval (c : ℂ) = 1) (h : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, c * N ≤ t → t ≤ c * N + h →
      ‖zetaFactorialLocalAmplitude p N t - 1‖ < ε := by
  filter_upwards [(tendsto_zetaFactorialLocalError p c h).eventually_lt_const hε] with N hN t ht htu
  rw [← hp]
  exact (norm_zetaFactorialLocalAmplitude_sub_eval_le p N hc ht htu).trans_lt hN

end
end RiemannGaussian
