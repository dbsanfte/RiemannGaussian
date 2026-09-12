/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerFourier
import RiemannGaussian.OscillatoryPowerPrimitive

/-!
# Oscillatory control of the complete actual Bernoulli tail

The entire interval is assembled before its Fourier channels are bounded.
When the cutoff exceeds the imaginary height, every nonzero Bernoulli
frequency is separated from the logarithmic phase. This gains a full
cutoff power over the absolute cell estimate, with all infinite exchanges
justified by the preceding exact Fourier representation.
-/

namespace RiemannGaussian.ZetaEulerOscillation
noncomputable section
open Complex Filter MeasureTheory Set Topology ZetaEulerBernoulli ZetaEulerFourier
open scoped Interval

/-- The common separated-frequency envelope on one whole interval. -/
def envelope (s : ℂ) (a b : ℝ) : ℝ :=
  1 / Real.pi * (a ^ (-s.re - 2) + b ^ (-s.re - 2)) +
    ‖s + 2‖ / Real.pi ^ 2 * ∫ x : ℝ in a..b, x ^ (-s.re - 4)

/-- Every actual Fourier channel satisfies the same whole-interval
oscillatory bound times its original summable coefficient. -/
theorem norm_channel_integral_le (s : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht : |s.im| ≤ a) (n : ℕ) :
    ‖∫ x : ℝ in a..b, channel s n x‖ ≤ weight n * envelope s a b := by
  have hbpos := ha.trans_le hab
  by_cases hn : n = 0
  · subst n
    simp [channel, weight_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : 0 < Real.pi := Real.pi_pos
  have hw : 0 < 2 * Real.pi * n := by positivity
  have hwlo : 2 * Real.pi ≤ 2 * Real.pi * n := by nlinarith
  have hsep : 2 * |(-s - 2).im| ≤ |2 * Real.pi * n| * a := by
    change 2 * |-s.im - 0| ≤ |2 * Real.pi * n| * a
    simp only [sub_zero, abs_neg, abs_of_pos hw]
    have hp1 := Real.pi_gt_three
    nlinarith [mul_le_mul_of_nonneg_right hwlo ha.le]
  have h := OscillatoryPowerPrimitive.norm_cosine_integral_le (-s - 2) hw.ne' ha hab hsep
  have he : ‖-s - 2‖ = ‖s + 2‖ := by rw [show -s - 2 = -(s + 2) by ring, norm_neg]
  change ‖∫ x : ℝ in a..b, (Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
    2 / |2 * Real.pi * n| * (a ^ (-s.re - 2) + b ^ (-s.re - 2)) +
      (4 * ‖-s - 2‖ / |2 * Real.pi * n| ^ 2) * ∫ x : ℝ in a..b, x ^ (-s.re - 2 - 2) at h
  rw [he, abs_of_pos hw, show -s.re - 2 - 2 = -s.re - 4 by ring] at h
  have h1 : 2 / (2 * Real.pi * n) ≤ 1 / Real.pi := by
    calc
      _ ≤ 2 / (2 * Real.pi) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hwlo
      _ = _ := by field_simp
  have h2 : 4 / (2 * Real.pi * n) ^ 2 ≤ 1 / Real.pi ^ 2 := by
    calc
      _ ≤ 4 / (2 * Real.pi) ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (by positivity) hwlo 2)
      _ = _ := by field_simp; ring
  have hi : 0 ≤ ∫ x : ℝ in a..b, x ^ (-s.re - 4) :=
    intervalIntegral.integral_nonneg hab (fun x hx ↦ Real.rpow_nonneg (ha.trans_le hx.1).le _)
  have hb : ‖∫ x : ℝ in a..b, (Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
      envelope s a b := by
    apply h.trans
    unfold envelope
    have h2' : 4 * ‖s + 2‖ / (2 * Real.pi * n) ^ 2 ≤ ‖s + 2‖ / Real.pi ^ 2 := by
      simpa only [div_eq_mul_inv, mul_one, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_right h2 (norm_nonneg (s + 2))
    exact add_le_add
      (mul_le_mul_of_nonneg_right h1 (by positivity))
      (mul_le_mul_of_nonneg_right h2' hi)
  have hc : (fun x : ℝ ↦ channel s n x) =
      fun x ↦ (weight n : ℂ) * ((Real.cos (2 * Real.pi * n * x) : ℂ) * (x : ℂ) ^ (-s - 2)) := by
    funext x
    simp only [channel, ofReal_mul, mul_assoc]
  rw [hc, intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg n)]
  exact mul_le_mul_of_nonneg_left hb (weight_nonneg n)

/-- The complete finite Bernoulli interval obeys the oscillatory
bound after all cell phases have been joined exactly. -/
theorem norm_blocks_le (s : ℂ) (N M : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖∑ j ∈ Finset.range M, block s (j + N)‖ ≤ envelope s (N + 1) (M + N + 1) / 6 := by
  have h := (hasSum_blocks s N M).norm_le_of_bounded
    (hasSum_weight.mul_right (envelope s (N + 1) (M + N + 1)))
    (fun n ↦ norm_channel_integral_le s (by positivity)
      (by have hM := Nat.cast_nonneg (α := ℝ) M; linarith) ht n)
  convert h using 1
  ring

private theorem power_integral_le {s : ℂ} (hs : 0 < s.re)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, x ^ (-s.re - 4)) ≤ a ^ (-s.re - 3) / (s.re + 3) := by
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]⟩)]
  rw [show -s.re - 4 + 1 = -s.re - 3 by ring]
  have he : (b ^ (-s.re - 3) - a ^ (-s.re - 3)) / (-s.re - 3) =
      (a ^ (-s.re - 3) - b ^ (-s.re - 3)) / (s.re + 3) := by
    field_simp [show s.re + 3 ≠ 0 by linarith, show -s.re - 3 ≠ 0 by linarith]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (ha.trans_le hab).le _)) (by positivity)

/-- The full actual Bernoulli tail gains a cutoff power by retaining
all phases across cells and controlling their separated Fourier integrals. -/
theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) (ht : |s.im| ≤ N + 1) :
    ‖tail N s‖ ≤
      (1 / Real.pi * (N + 1 : ℝ) ^ (-s.re - 2) +
        ‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3)) / 6 := by
  have hbound M : ‖∑ j ∈ Finset.range M, block s (j + N)‖ ≤
      (1 / Real.pi * ((N + 1 : ℝ) ^ (-s.re - 2) + (M + N + 1 : ℝ) ^ (-s.re - 2)) +
        ‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3)) / 6 := by
    apply (norm_blocks_le s N M ht).trans
    unfold envelope
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add_right
    have hi := power_integral_le hs (a := (N + 1 : ℝ)) (b := (M + N + 1 : ℝ))
      (by positivity) (by have hM := Nat.cast_nonneg (α := ℝ) M; linarith)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hi
      (div_nonneg (norm_nonneg (s + 2)) (sq_nonneg Real.pi))
  have htend : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ)) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop ((N : ℝ) + 1)
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_assoc] using h
  have hp : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ) ^ (-s.re - 2)) atTop (𝓝 0) := by
    have hr := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re + 2)).comp htend
    change Tendsto (fun M : ℕ ↦ (M + N + 1 : ℝ) ^ (-(s.re + 2))) atTop (𝓝 0) at hr
    simpa only [show -(s.re + 2) = -s.re - 2 by ring] using hr
  have hc := (((tendsto_const_nhds (x := (N + 1 : ℝ) ^ (-s.re - 2))).add hp).const_mul
    (1 / Real.pi)).add_const
      (‖s + 2‖ / Real.pi ^ 2 * (N + 1 : ℝ) ^ (-s.re - 3) / (s.re + 3))
  have h := le_of_tendsto_of_tendsto (summable_block hs N).tendsto_sum_tsum_nat.norm
    (hc.div_const 6) (Filter.Eventually.of_forall hbound)
  simpa only [add_zero, tail] using h

end
end RiemannGaussian.ZetaEulerOscillation
