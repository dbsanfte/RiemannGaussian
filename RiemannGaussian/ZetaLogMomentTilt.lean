/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaDominatedMomentBand
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential tilts localize the complete logarithmic moment kernel

An arbitrary positive tilt and a genuinely summable reference exponent
give a geometric bound outside a logarithmic window. The phase is kept in
the original complex kernel; norms are used only on discarded shells.
The resulting Chernoff rate is explicit for every window endpoint, rather
than being tied to the old dyadic band. A concrete window is established
for the actual sampling line at real part three halves.
-/

open Complex
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- A general exponential tilt, retaining the reference Euler weight
and the complete offset moment. The hypothesis concerns only the index's
logarithmic location, not its arithmetic coefficient or phase. -/
theorem norm_zetaPrimeLogKernel_le_tilt (N k n : ℕ) (s : ℂ)
    {q τ A : ℝ} (hq : 0 < q)
    (hcut : (q + τ - s.re) * Real.log n ≤ A * (N : ℝ)) :
    ‖zetaPrimeLogKernel (N + k) s n‖ ≤
      (q⁻¹ * Real.exp A) ^ N * q⁻¹ ^ k * zetaPrimeExpWeight τ n := by
  have he : zetaPrimeExpWeight (s.re - q) n =
      Real.exp ((q + τ - s.re) * Real.log n) * zetaPrimeExpWeight τ n := by
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add]
    congr 1
    ring
  have hb := norm_zetaPrimeLogKernel_le (N + k) s n hq
  rw [he] at hb
  have hexp := Real.exp_le_exp.mpr hcut
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-τ * Real.log n)).le)
    (show 0 ≤ q⁻¹ ^ (N + k) by positivity)
  have heN : Real.exp (A * (N : ℝ)) = (Real.exp A) ^ N := by
    rw [mul_comm, Real.exp_nat_mul]
  exact (hb.trans hm).trans_eq (by rw [heN, pow_add, mul_pow]; unfold zetaPrimeExpWeight; ring)

/-- The endpoint-dependent Chernoff rate. Its dependence on the
reference abscissa is explicit and remains available for adaptive windows. -/
def zetaLogMomentRate (gap endpoint : ℝ) : ℝ :=
  endpoint * Real.exp (1 - gap * endpoint)

/-- The reciprocal endpoint tilt controls every lower logarithmic
shell before summation, for arbitrary complex sampling points. -/
theorem norm_zetaPrimeLogKernel_le_lower_chernoff (N k n : ℕ) (s : ℂ)
    {τ a : ℝ} (ha : 0 < a) (hgap : (s.re - τ) * a ≤ 1)
    (hn : Real.log n ≤ a * (N : ℝ)) :
    ‖zetaPrimeLogKernel (N + k) s n‖ ≤
      zetaLogMomentRate (s.re - τ) a ^ N * a ^ k * zetaPrimeExpWeight τ n := by
  have hcoeff : 0 ≤ a⁻¹ + τ - s.re := by
    have h := (le_div_iff₀ ha).mpr hgap
    rw [one_div] at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hn hcoeff
  have he : (a⁻¹ + τ - s.re) * (a * (N : ℝ)) =
      (1 - (s.re - τ) * a) * (N : ℝ) := by field_simp; ring
  rw [he] at hm
  simpa only [inv_inv, zetaLogMomentRate] using
    norm_zetaPrimeLogKernel_le_tilt N k n s (q := a⁻¹) (by positivity) hm

/-- The same endpoint rate controls every upper logarithmic shell.
The direction reverses with the tilt coefficient, preserving the full
geometric dependence rather than imposing a fixed dyadic endpoint. -/
theorem norm_zetaPrimeLogKernel_le_upper_chernoff (N k n : ℕ) (s : ℂ)
    {τ b : ℝ} (hb : 0 < b) (hgap : 1 ≤ (s.re - τ) * b)
    (hn : b * (N : ℝ) ≤ Real.log n) :
    ‖zetaPrimeLogKernel (N + k) s n‖ ≤
      zetaLogMomentRate (s.re - τ) b ^ N * b ^ k * zetaPrimeExpWeight τ n := by
  have hcoeff : b⁻¹ + τ - s.re ≤ 0 := by
    have h := (div_le_iff₀ hb).mpr hgap
    rw [one_div] at h
    linarith
  have hm := mul_le_mul_of_nonpos_left hn hcoeff
  have he : (b⁻¹ + τ - s.re) * (b * (N : ℝ)) =
      (1 - (s.re - τ) * b) * (N : ℝ) := by field_simp; ring
  rw [he] at hm
  simpa only [inv_inv, zetaLogMomentRate] using
    norm_zetaPrimeLogKernel_le_tilt N k n s (q := b⁻¹) (by positivity) hm

private theorem lower_rate : (1 / 2 : ℝ) * Real.exp (5 / 8) ≤ 15 / 16 := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 15 / 16)
  have he : Real.log (15 / 8 : ℝ) = Real.log 2 + Real.log (15 / 16 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (15 / 16 : ℝ) ≠ 0)]
    norm_num
  have hb : (5 / 8 : ℝ) ≤ Real.log (15 / 8 : ℝ) := by
    rw [he]
    norm_num at hl
    linarith [Real.log_two_gt_d9]
  have hx := Real.exp_le_exp.mpr hb
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 15 / 8)] at hx
  linarith

private theorem upper_rate : (8 : ℝ) * Real.exp (-(5 / 2)) ≤ 3 / 4 := by
  have hl : Real.log (32 / 3 : ℝ) ≤ 5 / 2 := by
    rw [Real.log_div (by norm_num : (32 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
      show Real.log (32 : ℝ) = 5 * Real.log 2 by
        rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num]
    linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hx := Real.exp_le_exp.mpr (neg_le_neg hl)
  rw [Real.exp_neg (Real.log (32 / 3)),
    Real.exp_log (by norm_num : (0 : ℝ) < 32 / 3)] at hx
  norm_num at hx
  linarith

/-- Every index below `exp(2*N/5)` has an independently decaying
kernel, using the genuinely summable reference exponent `17/16`. -/
theorem norm_zetaPrimeLogKernel_le_lower_window (N k n : ℕ) (y : ℝ)
    (hn : Real.log n ≤ (2 / 5 : ℝ) * N) :
    ‖zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      (15 / 16 : ℝ) ^ N * (1 / 2 : ℝ) ^ k * zetaPrimeExpWeight (17 / 16) n := by
  have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have hc : (2 + (17 / 16 : ℝ) - (3 / 2 + I * (y : ℂ)).re) * Real.log n ≤
      (5 / 8 : ℝ) * N := by rw [hs]; nlinarith only [hn]
  have hb := norm_zetaPrimeLogKernel_le_tilt N k n (3 / 2 + I * y)
    (q := 2) (by norm_num) hc
  norm_num only [inv_eq_one_div] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) lower_rate N) (by positivity)) (Real.exp_pos _).le)

/-- Every index above `exp(8*N)` has an independently decaying
kernel with the same reference arithmetic mass as the lower shell. -/
theorem norm_zetaPrimeLogKernel_le_upper_window (N k n : ℕ) (y : ℝ)
    (hn : (8 : ℝ) * N ≤ Real.log n) :
    ‖zetaPrimeLogKernel (N + k) (3 / 2 + I * y) n‖ ≤
      (3 / 4 : ℝ) ^ N * (8 : ℝ) ^ k * zetaPrimeExpWeight (17 / 16) n := by
  have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have hc : ((1 / 8 : ℝ) + 17 / 16 - (3 / 2 + I * (y : ℂ)).re) * Real.log n ≤
      (-5 / 2 : ℝ) * N := by rw [hs]; nlinarith only [hn]
  have hb := norm_zetaPrimeLogKernel_le_tilt N k n (3 / 2 + I * y)
    (q := 1 / 8) (by norm_num) hc
  norm_num only [one_div, inv_inv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) upper_rate N) (by positivity)) (Real.exp_pos _).le)

end
end RiemannGaussian
