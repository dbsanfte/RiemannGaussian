/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowCost

/-!
# Exponential decay of the actual homogeneous moment defect

The literal factor (1-1/k)^n is bounded before rounding the number of
degree blocks. Three blocks leave defect at most k^2/40; four leave
at most k^2/100. The moments themselves retain the existing proved
prime packet and all positive integer endpoints.
-/

namespace RiemannGaussian.VinogradovExponentialDefect
noncomputable section
open scoped BigOperators
open VinogradovDiagonalIteration

/-- The exact descent defect has its full exponential rate. -/
theorem defect_le_exp {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    defect k n ≤ ((k : ℝ) ^ 2 / 2) * Real.exp (-(n : ℝ) / k) := by
  have hfactor : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / (k : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (k : ℝ)))]
  have hp := pow_le_pow_left₀ (factor_nonneg hk) hfactor n
  rw [← Real.exp_nat_mul] at hp
  have he : (n : ℝ) * (-(1 / (k : ℝ))) = -(n : ℝ) / k := by ring
  rw [he] at hp
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h := VinogradovDiagonalExponent.power_gap hk 0 (0 : ℝ)
    rw [← Nat.choose_two_right] at h
    norm_num [VinogradovDiagonalExponent.exponent, VinogradovDiagonalExponent.degreeWeight] at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_le_mul hc hp (pow_nonneg (factor_nonneg hk) n)
    (by positivity : 0 ≤ (k : ℝ) ^ 2 / 2)

/-- An exact finite Taylor lower bound pays the three-block exponential. -/
theorem exp_neg_three_le : Real.exp (-3 : ℝ) ≤ 1 / 20 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20)
    (show 20 ≤ Real.exp 3 by linarith)

/-- An exact finite Taylor lower bound pays the four-block exponential. -/
theorem exp_neg_four_le : Real.exp (-4 : ℝ) ≤ 1 / 50 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 50)
    (show 50 ≤ Real.exp 4 by linarith)

/-- Three blocks of actual descent suffice for relative defect 1/40. -/
theorem defect_three_degree_le {k : ℕ} (hk : 1 ≤ k) :
    defect k (3 * k) ≤ (k : ℝ) ^ 2 / 40 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := defect_le_exp hk (3 * k)
  have he : -((3 * k : ℕ) : ℝ) / k = -3 := by push_cast; field_simp
  rw [he] at h
  calc
    _ ≤ (k : ℝ) ^ 2 / 2 * Real.exp (-3) := h
    _ ≤ (k : ℝ) ^ 2 / 2 * (1 / 20) :=
      mul_le_mul_of_nonneg_left exp_neg_three_le (by positivity)
    _ = _ := by ring

/-- Four blocks of actual descent suffice for relative defect 1/100. -/
theorem defect_four_degree_le {k : ℕ} (hk : 1 ≤ k) :
    defect k (4 * k) ≤ (k : ℝ) ^ 2 / 100 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := defect_le_exp hk (4 * k)
  have he : -((4 * k : ℕ) : ℝ) / k = -4 := by push_cast; field_simp
  rw [he] at h
  calc
    _ ≤ (k : ℝ) ^ 2 / 2 * Real.exp (-4) := h
    _ ≤ (k : ℝ) ^ 2 / 2 * (1 / 50) :=
      mul_le_mul_of_nonneg_left exp_neg_four_le (by positivity)
    _ = _ := by ring

end
end RiemannGaussian.VinogradovExponentialDefect
