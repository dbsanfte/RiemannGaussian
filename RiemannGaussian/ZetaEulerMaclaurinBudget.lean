/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurin
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An explicit Euler--Maclaurin error budget through height 22000

All Bernoulli arithmetic is checked by Lean. The resulting error bound
is uniform over the right half of the critical strip. This is a bound
for evaluating zeta, not a certificate that all low zeros lie on the line.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinBudget
noncomputable section
open Complex Real ZetaEulerMaclaurinKernel ZetaEulerMaclaurin

private theorem b0 : bernoulli' 0 = (1 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ]

private theorem b1 : bernoulli' 1 = (1 / 2 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0]

private theorem b2 : bernoulli' 2 = (1 / 6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1]

private theorem b3 : bernoulli' 3 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2]

private theorem b4 : bernoulli' 4 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3]

private theorem b5 : bernoulli' 5 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4]

private theorem b6 : bernoulli' 6 = (1 / 42 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5]

private theorem b7 : bernoulli' 7 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6]

private theorem b8 : bernoulli' 8 = (-1 / 30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7]

private theorem b9 : bernoulli' 9 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8]

private theorem b10 : bernoulli' 10 = (5 / 66 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]

private theorem b11 : bernoulli' 11 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10]

private theorem b12 : bernoulli' 12 = (-691 / 2730 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]

private theorem b13 : bernoulli' 13 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12]

private theorem b14 : bernoulli' 14 = (7 / 6 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]

private theorem b15 : bernoulli' 15 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14]

private theorem b16 : bernoulli' 16 = (-3617 / 510 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]

private theorem b17 : bernoulli' 17 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16]

private theorem b18 : bernoulli' 18 = (43867 / 798 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17]

private theorem b19 : bernoulli' 19 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18]

private theorem b20 : bernoulli' 20 = (-174611 / 330 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, Finset.sum_range_succ, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19]

/-- The entire coefficient allowance at order twenty, enclosed by exact
rational arithmetic rather than floating-point Bernoulli values. -/
theorem allowance_twenty : allowance 20 < (6 / 10 ^ 14 : ℝ) := by
  rw [allowance_eq]
  norm_num [Nat.choose, Finset.sum_range_succ, bernoulli, Nat.factorial,
    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20]

/-- Exact cached normalized Bernoulli coefficients for orders two through
 twenty. The following theorem checks each entry against the recurrence. -/
def coefficientTable : List ℚ :=
  [1 / 12,
   0,
   -1 / 720,
   0,
   1 / 30240,
   0,
   -1 / 1209600,
   0,
   1 / 47900160,
   0,
   -691 / 1307674368000,
   0,
   1 / 74724249600,
   0,
   -3617 / 10670622842880000,
   0,
   43867 / 5109094217170944000,
   0,
   -174611 / 802857662698291200000]

/-- Read the finite coefficient table; only indices below nineteen are used. -/
def coefficientAt (j : ℕ) : ℚ := coefficientTable[j]?.getD 0

/-- Every cached entry equals the actual normalized Bernoulli coefficient. -/
theorem coefficientAt_eq (j : ℕ) (hj : j < 19) :
    coefficientAt j = bernoulli (j + 2) / (j + 2).factorial := by
  interval_cases j <;>
    norm_num [coefficientAt, coefficientTable, bernoulli, Nat.factorial,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20]

/-- The same rigorous error budget allows a shorter prefix whenever the
actual complex norm fits below its endpoint minus twenty. The maximum
cutoff keeps the numerical square-root allowance uniform. -/
theorem uniform_error_of_norm {s : ℂ} (hs : 1 / 2 ≤ s.re) (hsne : s ≠ 1)
    (N : ℕ) (hN : N ≤ 22020) (hn : ‖s‖ + 20 ≤ (N + 1 : ℝ)) :
    ‖riemannZeta s - approximation N s 18‖ < (1 / 10 ^ 12 : ℝ) := by
  have hs0 : 0 < s.re := by linarith
  have hNR : (N : ℝ) ≤ 22020 := by exact_mod_cast hN
  have hr : ‖rising s 20‖ ≤ (N + 1 : ℝ) ^ (20 : ℕ) := by
    have hh := norm_rising_le (le_refl ‖s‖) 20
    simp only [Nat.cast_ofNat] at hh
    exact hh.trans (pow_le_pow_left₀ (by positivity) hn 20)
  have he := norm_error_le hs0 hsne N 18
  norm_num at he
  have hexp : (N + 1 : ℝ) ^ (-s.re - 20 + 1) =
      (N + 1 : ℝ) ^ (1 - s.re) / (N + 1 : ℝ) ^ (20 : ℕ) := by
    rw [show -s.re - 20 + 1 = (1 - s.re) - (20 : ℕ) by norm_num; ring,
      Real.rpow_sub_natCast (by positivity)]
  have hpow : (N + 1 : ℝ) ^ (1 - s.re) < 150 := by
    calc
      _ ≤ (N + 1 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by linarith)
      _ = Real.sqrt (N + 1 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ < 150 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hpow0 : 0 ≤ (N + 1 : ℝ) ^ (1 - s.re) := by positivity
  have hden : 19 ≤ s.re + 20 - 1 := by linarith
  have hc : ‖rising s 20‖ * allowance 20 * (N + 1 : ℝ) ^ (-s.re - 20 + 1) /
      (s.re + 20 - 1) ≤ allowance 20 * (N + 1 : ℝ) ^ (1 - s.re) / 19 := by
    calc
      _ ≤ (N + 1 : ℝ) ^ (20 : ℕ) * allowance 20 *
          (N + 1 : ℝ) ^ (-s.re - 20 + 1) / (s.re + 20 - 1) := by
        gcongr
        exact allowance_nonneg 20
      _ = allowance 20 * (N + 1 : ℝ) ^ (1 - s.re) / (s.re + 20 - 1) := by
        rw [hexp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (allowance_nonneg 20) hpow0)
        (by norm_num) hden
  have hlast : allowance 20 * (N + 1 : ℝ) ^ (1 - s.re) / 19 < (1 / 10 ^ 12 : ℝ) := by
    have hh := mul_le_mul allowance_twenty.le hpow.le hpow0 (by norm_num : (0 : ℝ) ≤ 6 / 10 ^ 14)
    have hh' := div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 19)
    exact hh'.trans_lt (by norm_num)
  exact (he.trans hc).trans_lt hlast

/-- Twenty Bernoulli orders at cutoff 22020 give a uniform absolute
error below `10⁻¹²` on the entire right half-strip through height 22000.
The pole at one is explicitly excluded. -/
theorem uniform_error {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 1)
    (ht : |s.im| ≤ 22000) (hsne : s ≠ 1) :
    ‖riemannZeta s - approximation 22020 s 18‖ < (1 / 10 ^ 12 : ℝ) := by
  apply uniform_error_of_norm hs hsne 22020 le_rfl
  have hh := norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (by linarith : 0 ≤ s.re)] at hh
  norm_num
  linarith

/-- The literal low-zero height used by Rosser--Schoenfeld is inside
the whole rectangle covered by the evaluator's error budget. -/
theorem rosser_height_lt : Real.exp (999 / 100) < (22000 : ℝ) := by
  have hbase : Real.exp 1 ≤ (87 / 32 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hh := pow_le_pow_left₀ (Real.exp_pos 1).le hbase 10
  rw [← Real.exp_nat_mul] at hh
  norm_num at hh
  have he := Real.add_one_le_exp (1 / 100 : ℝ)
  have he' := mul_le_mul_of_nonneg_left he (Real.exp_pos (999 / 100)).le
  rw [← Real.exp_add] at he'
  norm_num at he'
  linarith

end
end RiemannGaussian.ZetaEulerMaclaurinBudget
