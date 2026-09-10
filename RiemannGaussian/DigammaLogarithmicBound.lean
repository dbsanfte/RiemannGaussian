/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianDigammaGauss

/-!
# A logarithmic upper bound for the real part of digamma

The complete Euler approximants retain their complex reciprocals. Their
real parts dominate one shifted harmonic sequence, whose lower bound
telescopes exactly through logarithms. Passing to the already proved
digamma limit gives a bound uniform on the positive half-plane.

This signed bound is intended for the genuine completed-zeta zero budget;
it does not replace a complex norm estimate or assume a zero-free strip.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter
open scoped Topology

private theorem reciprocal_real_lower {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    1 / (Complex.normSq z / z.re + n) ≤ ((z + n)⁻¹).re := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hzN : 0 < Complex.normSq z :=
    Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hz)
  have hden : 0 < Complex.normSq z / z.re + n := by positivity
  have hzn : 0 < Complex.normSq (z + n) := by
    apply Complex.normSq_pos.mpr
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  rw [Complex.inv_re, div_le_div_iff₀ hden hzn]
  have he : (Complex.normSq z / z.re) * z.re = Complex.normSq z :=
    div_mul_cancel₀ _ hz.ne'
  have hR : z.re ≤ Complex.normSq z / z.re := by
    apply (le_div_iff₀ hz).mpr
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  have hmul := mul_le_mul_of_nonneg_right hR hn
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.natCast_re, Complex.natCast_im, add_zero] at he hmul ⊢
  nlinarith

private theorem log_increment_le_reciprocal {A : ℝ} (hA : 0 < A) (j : ℕ) :
    Real.log (A + (j + 1 : ℕ)) - Real.log (A + j) ≤ 1 / (A + j) := by
  have hj : 0 < A + (j : ℝ) := by positivity
  have hj1 : 0 < A + ((j + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hj1 hj)
  rw [Real.log_div hj1.ne' hj.ne'] at h
  have he : (A + ((j + 1 : ℕ) : ℝ)) / (A + j) - 1 = 1 / (A + j) := by
    push_cast
    field_simp
    ring
  rwa [he] at h

private theorem logarithmic_harmonic_lower {A : ℝ} (hA : 0 < A) (N : ℕ) :
    Real.log (A + N) - Real.log A ≤ ∑ j ∈ Finset.range N, 1 / (A + j) := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) =>
    log_increment_le_reciprocal hA j)
  have he := Finset.sum_range_sub (fun j : ℕ => Real.log (A + j)) N
  simpa only [Nat.cast_zero, add_zero, he] using h

/-- On the whole positive half-plane, the real part of digamma is at
most the logarithm of `normSq z / re z`. The actual Euler limit supplies
the bound, with no asymptotic constant or omitted finite tail. -/
theorem re_digamma_le_log_normSq_div_re {z : ℂ} (hz : 0 < z.re) :
    (Complex.digamma z).re ≤ Real.log (Complex.normSq z / z.re) := by
  let A : ℝ := Complex.normSq z / z.re
  have hA : 0 < A := div_pos
    (Complex.normSq_pos.mpr (Complex.ne_zero_of_re_pos hz)) hz
  have hlim := Complex.continuous_re.tendsto (Complex.digamma z) |>.comp
    (Complex.digamma_tendsto_euler hz)
  apply le_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrec := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (N + 1)) =>
    reciprocal_real_lower hz j)
  have hlog := logarithmic_harmonic_lower hA (N + 1)
  have hNlog : Real.log (N : ℝ) ≤ Real.log (A + (N + 1 : ℕ)) :=
    Real.log_le_log hNR (by push_cast; linarith)
  change (Complex.log (N : ℂ) - ∑ j ∈ Finset.range (N + 1), (z + j)⁻¹).re ≤ Real.log A
  simp only [Complex.sub_re, Complex.log_re, Complex.norm_natCast, Complex.re_sum]
  change Real.log (N : ℝ) - (∑ j ∈ Finset.range (N + 1), ((z + j)⁻¹).re) ≤ Real.log A
  change (∑ j ∈ Finset.range (N + 1), 1 / (A + j)) ≤ _ at hrec
  linarith

end
end RiemannGaussian
