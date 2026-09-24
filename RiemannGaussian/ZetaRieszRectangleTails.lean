/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleCube

/-!
# Kernel bounds only on failures of the concrete rectangle's masks

All three prime phases remain in the literal kernel. Absolute values are
used here solely to pay exceptional geometry with a strict geometric rate.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical

/-- One exact factorial kernel with a freely tilted real exponent. -/
theorem rectangle_kernel_tilt (k n : ℕ) (y : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖zetaPrimeLogKernel k (3 / 2 + Complex.I * y) n‖ ≤
      rectangleTilt⁻¹ ^ k *
        Real.exp (k * Real.log (rectangleTilt / q) + (q - rectangleTilt) * Real.log n) *
          zetaPrimeExpWeight (1 + 1 / 262144) n := by
  have h := norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * y) n hq
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs] at h
  have hd : 0 < rectangleTilt := by norm_num [rectangleTilt]
  have hp : rectangleTilt⁻¹ ^ k * (rectangleTilt / q) ^ k = q⁻¹ ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have he : Real.exp ((q - rectangleTilt) * Real.log n) *
      zetaPrimeExpWeight (1 + 1 / 262144) n = zetaPrimeExpWeight (3 / 2 - q) n := by
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add]
    congr 1
    dsimp [rectangleTilt]
    ring
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hd hq),
    ← mul_assoc, hp, mul_assoc, he]
  exact h

/-- Three tilted kernels retain the correlated total order. This
bound has no primality, ordering or independence hypothesis. -/
theorem rectangle_product_tilt {N j h : ℕ} (hj : j < N + 2)
    (hh : h ∈ rectangleOrders N j) (y : ℝ) (a : ℕ × ℕ × ℕ)
    {q₁ q₂ q₃ E : ℝ} (h₁ : 0 < q₁) (h₂ : 0 < q₂) (h₃ : 0 < q₃)
    (hE : j * Real.log (rectangleTilt / q₁) + (q₁ - rectangleTilt) * Real.log a.1 +
      ((N + 1 - j - h : ℕ) * Real.log (rectangleTilt / q₂) +
        (q₂ - rectangleTilt) * Real.log a.2.1) +
      ((h + 1 : ℕ) * Real.log (rectangleTilt / q₃) +
        (q₃ - rectangleTilt) * Real.log a.2.2) ≤ E) :
    ‖rectangleKernel y N j h a‖ ≤
      (N + 2 : ℝ) * rectangleTilt⁻¹ ^ (N + 2) * Real.exp E *
        (zetaPrimeExpWeight (1 + 1 / 262144) a.1 *
          zetaPrimeExpWeight (1 + 1 / 262144) a.2.1 *
            zetaPrimeExpWeight (1 + 1 / 262144) a.2.2) := by
  have hd : 0 < rectangleTilt := by norm_num [rectangleTilt]
  have H₁ := rectangle_kernel_tilt j a.1 y h₁
  have H₂ := rectangle_kernel_tilt (N + 1 - j - h) a.2.1 y h₂
  have H₃ := rectangle_kernel_tilt (h + 1) a.2.2 y h₃
  have horders : j + (N + 1 - j - h) + (h + 1) = N + 2 := by
    have := rectangle_orders_sum hj hh
    omega
  have hH : (h + 1 : ℕ) ≤ N + 2 := by omega
  have hprod := mul_le_mul (mul_le_mul H₁ H₂ (norm_nonneg _)
    (by unfold zetaPrimeExpWeight; positivity)) H₃
      (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)
  have he := Real.exp_le_exp.mpr hE
  rw [rectangleKernel, norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (N + 2 : ℝ) * ((rectangleTilt⁻¹ ^ j *
        Real.exp (j * Real.log (rectangleTilt / q₁) + (q₁ - rectangleTilt) * Real.log a.1) *
          zetaPrimeExpWeight (1 + 1 / 262144) a.1) *
        (rectangleTilt⁻¹ ^ (N + 1 - j - h) *
          Real.exp ((N + 1 - j - h : ℕ) * Real.log (rectangleTilt / q₂) +
            (q₂ - rectangleTilt) * Real.log a.2.1) * zetaPrimeExpWeight (1 + 1 / 262144) a.2.1) *
        (rectangleTilt⁻¹ ^ (h + 1) *
          Real.exp ((h + 1 : ℕ) * Real.log (rectangleTilt / q₃) +
            (q₃ - rectangleTilt) * Real.log a.2.2) * zetaPrimeExpWeight (1 + 1 / 262144) a.2.2)) := by
      simpa only [mul_assoc] using mul_le_mul (show ((h + 1 : ℕ) : ℝ) ≤ N + 2 by exact_mod_cast hH)
        hprod (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (by positivity)
    _ = (N + 2 : ℝ) * rectangleTilt⁻¹ ^ (N + 2) *
        Real.exp (j * Real.log (rectangleTilt / q₁) + (q₁ - rectangleTilt) * Real.log a.1 +
          ((N + 1 - j - h : ℕ) * Real.log (rectangleTilt / q₂) +
            (q₂ - rectangleTilt) * Real.log a.2.1) +
          ((h + 1 : ℕ) * Real.log (rectangleTilt / q₃) +
            (q₃ - rectangleTilt) * Real.log a.2.2)) *
          (zetaPrimeExpWeight (1 + 1 / 262144) a.1 *
            zetaPrimeExpWeight (1 + 1 / 262144) a.2.1 *
              zetaPrimeExpWeight (1 + 1 / 262144) a.2.2) := by
      rw [← horders]
      simp only [pow_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity))
      (by unfold zetaPrimeExpWeight; positivity)

/-- All five exceptional individual-prime ranges are geometrically paid. -/
theorem rectangle_bad_leg_bound {N j h : ℕ} (hj : j < N + 2)
    (hh : h ∈ rectangleOrders N j) (y : ℝ) (a : ℕ × ℕ × ℕ)
    (hbad : ¬ rectangleLogBox N a.1 a.2.1 a.2.2) :
    ‖rectangleKernel y N j h a‖ ≤
      (N + 2 : ℝ) * rectangleTilt⁻¹ ^ (N + 2) * Real.exp (1 - (N : ℝ) / 4000) *
        (zetaPrimeExpWeight (1 + 1 / 262144) a.1 *
          zetaPrimeExpWeight (1 + 1 / 262144) a.2.1 *
            zetaPrimeExpWeight (1 + 1 / 262144) a.2.2) := by
  have hd : 0 < rectangleTilt := by norm_num [rectangleTilt]
  have he := rectangle_leg_exponents hh
  have hd0 : rectangleTilt ≠ 0 := hd.ne'
  simp only [rectangleLogBox, not_and_or, not_lt, not_le] at hbad
  rcases hbad with h | h | h | h | h
  · apply rectangle_product_tilt hj hh y a (q₁ := 21 / 40) (q₂ := rectangleTilt)
      (q₃ := rectangleTilt) (by norm_num) hd hd
    simpa only [div_self hd0, Real.log_one, sub_self, mul_zero, zero_mul, add_zero] using
      (he.1 _ h).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])
  · apply rectangle_product_tilt hj hh y a (q₁ := 23 / 50) (q₂ := rectangleTilt)
      (q₃ := rectangleTilt) (by norm_num) hd hd
    simpa only [div_self hd0, Real.log_one, sub_self, mul_zero, zero_mul, add_zero] using
      (he.2.1 _ h.le).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])
  · apply rectangle_product_tilt hj hh y a (q₁ := rectangleTilt) (q₂ := 11 / 20)
      (q₃ := rectangleTilt) hd (by norm_num) hd
    simpa only [div_self hd0, Real.log_one, sub_self, mul_zero, zero_mul, add_zero, zero_add] using
      (he.2.2.1 _ h).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])
  · apply rectangle_product_tilt hj hh y a (q₁ := rectangleTilt) (q₂ := 93 / 200)
      (q₃ := rectangleTilt) hd (by norm_num) hd
    simpa only [div_self hd0, Real.log_one, sub_self, mul_zero, zero_mul, add_zero, zero_add] using
      (he.2.2.2.1 _ h.le).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])
  · apply rectangle_product_tilt hj hh y a (q₁ := rectangleTilt) (q₂ := rectangleTilt)
      (q₃ := 2 / 5) hd hd (by norm_num)
    simpa only [div_self hd0, Real.log_one, sub_self, mul_zero, zero_mul, add_zero, zero_add] using
      (he.2.2.2.2 _ h.le).trans (by linarith [Nat.cast_nonneg (α := ℝ) N])

/-- The original total window is paid using the coupled total order,
without treating the three prime logarithms independently. -/
theorem rectangle_bad_total_bound {N j h : ℕ} (hj : j < N + 2)
    (hh : h ∈ rectangleOrders N j) (y : ℝ) (a : ℕ × ℕ × ℕ)
    (hp : 0 < a.1) (hq : 0 < a.2.1) (hr : 0 < a.2.2)
    (hbad : ¬ ((39 / 20 : ℝ) * N < Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ∧
      Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ≤ (41 / 20 : ℝ) * N)) :
    ‖rectangleKernel y N j h a‖ ≤
      (N + 2 : ℝ) * rectangleTilt⁻¹ ^ (N + 2) * Real.exp (1 - (N : ℝ) / 4000) *
        (zetaPrimeExpWeight (1 + 1 / 262144) a.1 *
          zetaPrimeExpWeight (1 + 1 / 262144) a.2.1 *
            zetaPrimeExpWeight (1 + 1 / 262144) a.2.2) := by
  have horders : (j : ℝ) + (N + 1 - j - h : ℕ) + (h + 1 : ℕ) = (N + 2 : ℕ) := by
    exact_mod_cast (show j + (N + 1 - j - h) + (h + 1) = N + 2 by
      have := rectangle_orders_sum hj hh
      omega)
  have hlog := ZetaRieszTypeII.pair_log a.1 a.2.1 a.2.2 hp.ne' hq.ne' hr.ne'
  have he (q : ℝ) :
      j * Real.log (rectangleTilt / q) + (q - rectangleTilt) * Real.log a.1 +
      ((N + 1 - j - h : ℕ) * Real.log (rectangleTilt / q) +
        (q - rectangleTilt) * Real.log a.2.1) +
      ((h + 1 : ℕ) * Real.log (rectangleTilt / q) +
        (q - rectangleTilt) * Real.log a.2.2) =
      (N + 2 : ℕ) * Real.log (rectangleTilt / q) +
        (q - rectangleTilt) * Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) := by
    rw [hlog, ← horders]
    ring
  simp only [not_and_or, not_lt, not_le] at hbad
  rcases hbad with hlo | hhi
  · apply rectangle_product_tilt hj hh y a
      (q₁ := 20 / 39) (q₂ := 20 / 39) (q₃ := 20 / 39) (by norm_num) (by norm_num) (by norm_num)
    rw [he]
    exact (rectangle_total_exponents N).1 _ hlo
  · apply rectangle_product_tilt hj hh y a
      (q₁ := 20 / 41) (q₂ := 20 / 41) (q₃ := 20 / 41) (by norm_num) (by norm_num) (by norm_num)
    rw [he]
    exact (rectangle_total_exponents N).2 _ hhi.le

end
end RiemannGaussian.ZetaRieszSkewAllocation
