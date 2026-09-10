/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticSmallProduct

/-!
# Cubic head decay with a full quadratic coefficient allowance

Retaining the exact source parameter u pays a coefficient cost D_N^2
through n <= D_N^3. The resulting rate is 1/(2*u), which is strictly
below one throughout the actual range 1/2 < u < 1. The estimate applies
to arbitrary complex coefficients and arbitrary selected finite subsets.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- Keeping the exact source scale pays a quadratic coefficient cost
through the full cubic physical range. The rate remains below one. -/
theorem norm_normalized_sum_zetaArithmetic_quadratic_cubic_le
    (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (ha : ∀ n, ‖a n‖ ≤
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N : ℝ) ^ 2 * zetaMoebiusLogMajorant n)
    (T : Finset ℕ)
    (hT : ∀ n ∈ T, n ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N ^ 3) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T, a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      zetaArithmeticSmallProductConstant p * (1 / (2 * u)) ^ N := by
  let q := zetaMoebiusHeadGrowth u
  let D := zetaMoebiusGeometricCutoff q N
  let C := zetaArithmeticSmallProductConstant p
  have hu0 : 0 < u := by linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu0 hu1).le
  have hD : 1 ≤ D := Nat.le_floor (by simpa using one_le_pow₀ hq (n := N))
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDq : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith : 0 ≤ q) N)
  have hC : 0 ≤ C := zetaArithmeticSmallProductConstant_nonneg p
  let b := fun n ↦ a n / (D : ℂ) ^ 2
  have hb : ∀ n, ‖b n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n
    dsimp [b]
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply (div_le_iff₀ (sq_pos_of_pos hD0)).mpr
    simpa only [mul_comm] using ha n
  have he := norm_sum_zetaArithmetic_small_product_le b hb p N y T (D ^ 3) hT
  simp only [b, div_mul_eq_mul_div] at he
  rw [← Finset.sum_div, norm_div, norm_pow, Complex.norm_natCast] at he
  have he' := (div_le_iff₀ (sq_pos_of_pos hD0)).mp he
  have hraw : ‖∑ n ∈ T, a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N * (D : ℝ) ^ 8 * C := by
    exact he'.trans_eq (by push_cast; ring)
  have hq2 : q ^ 2 = (Real.sqrt u)⁻¹ := by
    rw [show q = (Real.sqrt (Real.sqrt u))⁻¹ from rfl,
      inv_pow, Real.sq_sqrt (Real.sqrt_nonneg u)]
  have hq4 : q ^ 4 = u⁻¹ := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hq2, inv_pow, Real.sq_sqrt hu0.le]
  have hrate : u * q ^ 8 / 2 = 1 / (2 * u) := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hq4]
    field_simp
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  calc
    _ ≤ u ^ (N + 1) * ((1 / 2 : ℝ) ^ N * (D : ℝ) ^ 8 * C) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ ≤ u ^ (N + 1) * ((1 / 2 : ℝ) ^ N * (q ^ N) ^ 8 * C) := by gcongr
    _ = (u * C) * (u * q ^ 8 / 2) ^ N := by
      rw [show (q ^ N) ^ 8 = (q ^ 8) ^ N by rw [← pow_mul, Nat.mul_comm N, pow_mul]]
      simp only [div_eq_mul_inv, mul_pow, pow_succ]
      ring
    _ = (u * C) * (1 / (2 * u)) ^ N := by rw [hrate]
    _ ≤ _ := by gcongr; exact mul_le_of_le_one_left hC hu1.le

/-- The retained source-scale rate is strictly between zero and one. -/
theorem zetaArithmetic_quadratic_cubic_rate_bounds {u : ℝ} (hu : 1 / 2 < u) :
    0 < 1 / (2 * u) ∧ 1 / (2 * u) < 1 := by
  have h : 0 < 2 * u := by linarith
  constructor
  · positivity
  · exact (div_lt_iff₀ h).mpr (by linarith)

end
end RiemannGaussian
