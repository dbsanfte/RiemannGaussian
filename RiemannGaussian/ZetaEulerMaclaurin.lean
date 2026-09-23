/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinKernel

/-!
# Arbitrary-order Euler--Maclaurin evaluation of actual zeta

The finite evaluator retains the literal complex Dirichlet prefix, pole
term and every Bernoulli endpoint. An absolutely convergent signed tail
gives its exact error. The separate explicit norm bound can support a
checked low-zero computation; no zero verification is assumed or asserted.

This is the classical Euler--Maclaurin expansion used, for example, in
Lehmer's 1956 *On the roots of the Riemann zeta-function*, equation (1).
-/

namespace RiemannGaussian.ZetaEulerMaclaurin
noncomputable section
open Complex Filter MeasureTheory Set Topology ZetaEulerMaclaurinKernel

private theorem sum_block_step {m : ℕ} (hm : 1 ≤ m) (s : ℂ) (N M : ℕ) :
    (∑ n ∈ Finset.range M, block m s (n + N)) = (boundary (m + 1) : ℂ) *
      ((M + N + 1 : ℂ) ^ (-s - m) - (N + 1 : ℂ) ^ (-s - m)) +
        (s + m) * ∑ n ∈ Finset.range M, block (m + 1) s (n + N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, block_step hm]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (M : ℂ) + 1 + N + 1 = M + N + 2 by ring]
    ring

/-- Integration by parts for the complete absolutely convergent signed tail. -/
theorem tail_step {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    tail m N s = -(boundary (m + 1) : ℂ) * (N + 1 : ℂ) ^ (-s - m) +
      (s + m) * tail (m + 1) N s := by
  have he := (summable_block hm hs N).tendsto_sum_tsum_nat
  simp_rw [sum_block_step (by omega : 1 ≤ m)] at he
  have h0 := (ZetaEulerContinuation.endpoint_tendsto_zero (s := s + m + 1)
    (by simp only [add_re, natCast_re, one_re]; linarith [Nat.cast_nonneg (α := ℝ) m])).comp
      (tendsto_add_atTop_nat N)
  have h0' : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℂ) ^ (-s - m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add,
      show 1 - (s + (m : ℂ) + 1) = -s - m by ring] using h0
  have ht := ((h0'.sub_const ((N + 1 : ℂ) ^ (-s - m))).const_mul
    (boundary (m + 1) : ℂ)).add
      (((summable_block (by omega : 2 ≤ m + 1) hs N).tendsto_sum_tsum_nat).const_mul (s + m))
  have hh := tendsto_nhds_unique he ht
  simpa only [zero_sub, mul_neg, neg_mul, tail] using hh

/-- The literal rising factorial, including all complex factors. -/
def rising (s : ℂ) (m : ℕ) : ℂ := ∏ j ∈ Finset.range m, (s + j)

/-- The rising factorial's exact successor law. -/
theorem rising_succ (s : ℂ) (m : ℕ) : rising s (m + 1) = rising s m * (s + m) := by
  simp only [rising, Finset.prod_range_succ]

/-- The finite zeta evaluator after `M+1` potential Bernoulli corrections.
Odd Bernoulli numbers vanish automatically; no infinite series occurs. -/
def approximation (N : ℕ) (s : ℂ) (M : ℕ) : ℂ :=
  ZetaEulerCell.partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) +
    (N + 1 : ℂ) ^ (-s) / 2 +
      ∑ j ∈ Finset.range (M + 1), rising s (j + 1) * (boundary (j + 2) : ℂ) *
        (N + 1 : ℂ) ^ (-s - (j + 1))

private theorem boundary_two : boundary 2 = (1 / 12 : ℝ) := by
  norm_num [boundary, bernoulli]

private theorem approximation_succ (N : ℕ) (s : ℂ) (M : ℕ) :
    approximation N s (M + 1) = approximation N s M +
      rising s (M + 2) * (boundary (M + 3) : ℂ) * (N + 1 : ℂ) ^ (-s - (M + 2)) := by
  simp only [approximation, Finset.sum_range_succ]
  push_cast
  ring_nf

/-- Actual zeta equals the finite arbitrary-order evaluator minus its
complete signed remainder at the unchanged cutoff. -/
theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) (N M : ℕ) :
    riemannZeta s = approximation N s M - rising s (M + 2) * tail (M + 2) N s := by
  induction M with
  | zero =>
    rw [ZetaEulerBernoulli.zeta_eq hs hsne N]
    simp only [approximation, Finset.sum_range_one, zero_add, boundary_two, tail_two,
      rising, Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, add_zero, one_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    norm_num
    ring
  | succ M ih =>
    rw [ih, tail_step (by omega : 2 ≤ M + 2) hs, approximation_succ]
    rw [show M + 1 + 2 = (M + 2) + 1 by omega, rising_succ s (M + 2)]
    push_cast
    ring

/-- An explicit unconditional error bound for the literal finite evaluator. -/
theorem norm_error_le {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) (N M : ℕ) :
    ‖riemannZeta s - approximation N s M‖ ≤
      ‖rising s (M + 2)‖ * allowance (M + 2) *
        (N + 1 : ℝ) ^ (-s.re - (M + 2) + 1) / (s.re + (M + 2) - 1) := by
  rw [zeta_eq hs hsne N M, sub_sub_cancel_left, norm_neg, norm_mul]
  have hh := mul_le_mul_of_nonneg_left (norm_tail_le (by omega : 2 ≤ M + 2) hs N)
    (norm_nonneg (rising s (M + 2)))
  convert! hh using 1
  push_cast
  ring

/-- A scalar box bounds every factor of the actual rising factorial. -/
theorem norm_rising_le {s : ℂ} {T : ℝ} (hT : ‖s‖ ≤ T) (m : ℕ) :
    ‖rising s m‖ ≤ (T + m) ^ m := by
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  rw [rising, norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range m, (T + m) := by
      apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
      intro j hj
      have hjR : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hj).le
      calc
        ‖s + j‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
        _ ≤ T + m := by simpa only [Complex.norm_natCast] using add_le_add hT hjR
    _ = _ := by simp

end
end RiemannGaussian.ZetaEulerMaclaurin
