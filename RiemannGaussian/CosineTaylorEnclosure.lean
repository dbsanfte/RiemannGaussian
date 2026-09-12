/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Global cosine enclosures with the exact factorial remainder

Lagrange's remainder bounds every Taylor order on the entire nonnegative
ray. The quartic and degree-twelve consequences are used against a Gaussian
measure, retaining all alternating polynomial coefficients in the integral.
-/

namespace RiemannGaussian.CosineTaylorEnclosure
noncomputable section
open Set

/-- Every cosine Taylor order has a global bound with the full factorial. -/
theorem abs_sub_taylor_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |Real.cos x - taylorWithinEval Real.cos n (Icc 0 x) 0 x| ≤ x ^ (n + 1) / (n + 1).factorial := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (ne_of_lt hx) (Real.contDiff_cos.contDiffOn (n := (n + 1)))
  rw [uIcc_of_le hx.le] at hy
  rw [hy, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hx, Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (pow_nonneg hx.le _) (Real.abs_iteratedDeriv_cos_le_one _ _))
    (Nat.cast_nonneg _)

/-- The global quartic upper bound is valid without a small-angle condition. -/
theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := abs_sub_taylor_le 3 hx.le
  have he : taylorWithinEval Real.cos 3 (Icc 0 x) 0 x = 1 - x ^ 2 / 2 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, Real.iteratedDerivWithin_cos_Icc _ hx (left_mem_Icc.mpr hx.le)]
    ring
  rw [he] at h
  norm_num at h
  linarith [(abs_le.mp h).2]

/-- The global degree-twelve upper bound keeps every alternating term. -/
theorem cos_le_degree_twelve {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 +
      x ^ 8 / 40320 - x ^ 10 / 3628800 + x ^ 12 / 479001600 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := abs_sub_taylor_le 11 hx.le
  have he : taylorWithinEval Real.cos 11 (Icc 0 x) 0 x =
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ, Real.iteratedDerivWithin_cos_Icc _ hx (left_mem_Icc.mpr hx.le)]
    ring
  rw [he] at h
  norm_num at h
  linarith [(abs_le.mp h).2]

end
end RiemannGaussian.CosineTaylorEnclosure
