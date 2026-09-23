/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerTruncation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A uniform logarithmic bound across the one-line

The original finite Dirichlet prefix is bounded by its harmonic mass.
At a height-sized cutoff, the full Euler remainder and actual pole
endpoint have absolute bounds when 1 <= Re(s) <= 3/2. This pays the
right-hand part of a local zero-detection disc without dividing by
Re(s)-1 or propagating a large low-height coefficient.
-/

namespace RiemannGaussian.ZetaEulerRightStrip
noncomputable section
open ZetaEulerCell
open scoped ComplexConjugate

/-- The original ordinary prefix has its harmonic mass throughout the
closed Euler half-plane, including the one-line. -/
theorem partialSum_le_harmonic (N : ℕ) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖partialSum N s‖ ≤ (harmonic N : ℝ) := by
  unfold partialSum
  apply (norm_sum_le _ _).trans
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro m _
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have he : (m + 1 : ℂ) = (((m + 1 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hm, Complex.neg_re]
  have hp := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ (m + 1 : ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    (show -s.re ≤ (-1 : ℝ) by linarith)
  simpa only [Real.rpow_neg_one] using hp

/-- The actual zeta function is at most sixteen logarithms of height
on the whole closed strip from one through three halves. -/
theorem bound {s : ℂ} (hs : 1 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (ht : 2 ≤ s.im) : ‖riemannZeta s‖ ≤ 16 * Real.log s.im := by
  let N : ℕ := ⌈s.im⌉₊
  have htpos : 0 < s.im := by linarith
  have htN : s.im ≤ (N : ℝ) := Nat.le_ceil s.im
  have hN1 : 1 ≤ N := by
    have h : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast h
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNup : (N : ℝ) ≤ 2 * s.im := by
    have h := Nat.ceil_lt_add_one htpos.le
    change (N : ℝ) < s.im + 1 at h
    linarith
  have hnorm : ‖s‖ ≤ 2 * (N : ℝ) := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg (by linarith : 0 ≤ s.re), abs_of_pos htpos] at h
    linarith
  have hspos : 0 < s.re := by linarith
  have hne : s ≠ 1 := by intro h; norm_num [h] at ht
  have h := ZetaEulerTruncation.norm_zeta_sub_partialSum_le hspos hne hN1
  have hpow : (N : ℝ) ^ (-s.re) ≤ (N : ℝ)⁻¹ := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ N by exact_mod_cast hN1) (show -s.re ≤ (-1 : ℝ) by linarith)
    simpa only [Real.rpow_neg_one] using hp
  have hrem : ‖s‖ / s.re * (N : ℝ) ^ (-s.re) ≤ 2 := by
    calc
      _ ≤ ‖s‖ * (N : ℝ)⁻¹ := mul_le_mul (div_le_self (norm_nonneg s) hs)
        hpow (by positivity) (norm_nonneg s)
      _ ≤ (2 * (N : ℝ)) * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hnorm (by positivity)
      _ = 2 := by field_simp
  have hend : (N + 1 : ℝ) ^ (1 - s.re) / ‖s - 1‖ ≤ 1 := by
    have hden : s.im ≤ ‖s - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.im_le_norm (s - 1)
    have hp := Real.rpow_le_one_of_one_le_of_nonpos
      (show (1 : ℝ) ≤ N + 1 by linarith) (show 1 - s.re ≤ 0 by linarith)
    exact (div_le_self (by positivity) (by linarith : 1 ≤ ‖s - 1‖)).trans hp
  have hpref := (partialSum_le_harmonic N hs).trans (harmonic_le_one_add_log N)
  have hlogN := Real.log_le_log hNp hNup
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) htpos.ne'] at hlogN
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := by linarith [Real.log_two_gt_d9]
  have htri := norm_add_le (riemannZeta s - partialSum N s) (partialSum N s)
  simp only [sub_add_cancel] at htri
  linarith

/-- The complete right-strip estimate holds at both signs of height. -/
theorem bound_abs {s : ℂ} (hs : 1 ≤ s.re) (hs' : s.re ≤ 3 / 2)
    (ht : 2 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 16 * Real.log |s.im| := by
  by_cases h : 0 ≤ s.im
  · rw [abs_of_nonneg h] at ht ⊢
    exact bound hs hs' ht
  · have hh := bound (s := conj s) (by simpa using hs) (by simpa using hs')
      (by simpa [abs_of_neg (lt_of_not_ge h)] using ht)
    simpa [abs_of_neg (lt_of_not_ge h)] using hh

end
end RiemannGaussian.ZetaEulerRightStrip
