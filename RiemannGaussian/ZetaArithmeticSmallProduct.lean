/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusMomentBand
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Independent bounds below a cubic product cutoff

A positive exponential tilt bounds the full factorial kernel on every
finite initial product range. At the actual geometric divisor schedule,
all products through its cube have a geometric source-normalized bound.
The estimate is independent of a zero-source asymptotic and is uniform in
the coefficient family, ordinate, and choice of subset in that range.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The explicit full-polynomial cost for a small product range. -/
def zetaArithmeticSmallProductConstant (P : Polynomial ℂ) : ℝ :=
  (∑ k ∈ P.support, ‖P.coeff k‖ * (1 / 2 : ℝ) ^ k) *
    zetaMoebiusLogMajorantMass (3 / 2)

/-- The small-product constant is nonnegative, including the zero filter. -/
theorem zetaArithmeticSmallProductConstant_nonneg (P : Polynomial ℂ) :
    0 ≤ zetaArithmeticSmallProductConstant P := by
  apply mul_nonneg _ (zetaMoebiusLogMajorantMass_nonneg _)
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (by positivity))

private theorem small_product_kernel_bound (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖zetaPrimeFilterKernel P N (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N * (n : ℝ) ^ 2 * zetaPrimeExpWeight (3 / 2) n *
        ∑ k ∈ P.support, ‖P.coeff k‖ * (1 / 2 : ℝ) ^ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + I * y)
    (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by norm_num : (0 : ℝ) < 2)
  have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have he : Real.exp (-((3 / 2 : ℝ) - 2) * Real.log n) =
      (n : ℝ) ^ 2 * zetaPrimeExpWeight (3 / 2) n := by
    rw [show -((3 / 2 : ℝ) - 2) * Real.log n =
      (2 : ℕ) * Real.log n + -(3 / 2 * Real.log n) by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_log hnR]
    simp only [zetaPrimeExpWeight, neg_mul]
  rw [hs, he] at hb
  norm_num only [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hb
  simpa only [mul_assoc] using hb

/-- The absolute cost of every finite small-product sum is controlled by
one summable divisor-log mass. No prime cancellation is assumed. -/
theorem sum_norm_zetaArithmetic_small_product_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (T : Finset ℕ) (X : ℕ)
    (hT : ∀ n ∈ T, n ≤ X) :
    (∑ n ∈ T, ‖a n * zetaPrimeFilterKernel P N (3 / 2 + I * y) n‖) ≤
      (1 / 2 : ℝ) ^ N * (X : ℝ) ^ 2 * zetaArithmeticSmallProductConstant P := by
  let B := ∑ k ∈ P.support, ‖P.coeff k‖ * (1 / 2 : ℝ) ^ k
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have hw (n : ℕ) : 0 ≤ zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n :=
    mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le
  calc
    _ ≤ ∑ n ∈ T, ((1 / 2 : ℝ) ^ N * X ^ 2 * B) *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        have hz : a 0 = 0 := norm_eq_zero.mp (le_antisymm
          (by simpa [zetaMoebiusLogMajorant] using ha 0) (norm_nonneg _))
        simp [hz, zetaMoebiusLogMajorant]
      have hK := small_product_kernel_bound P N y (Nat.pos_of_ne_zero hn0)
      have hnX : (n : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hT n hn) 2
      have hM := zetaMoebiusLogMajorant_nonneg n
      have hW : 0 ≤ zetaPrimeExpWeight (3 / 2) n := (Real.exp_pos _).le
      rw [norm_mul]
      calc
        _ ≤ zetaMoebiusLogMajorant n *
            ((1 / 2 : ℝ) ^ N * (n : ℝ) ^ 2 * zetaPrimeExpWeight (3 / 2) n * B) :=
          mul_le_mul (ha n) hK (norm_nonneg _) (zetaMoebiusLogMajorant_nonneg n)
        _ ≤ zetaMoebiusLogMajorant n *
            ((1 / 2 : ℝ) ^ N * (X : ℝ) ^ 2 * zetaPrimeExpWeight (3 / 2) n * B) := by
          gcongr
        _ = _ := by ring
    _ = ((1 / 2 : ℝ) ^ N * X ^ 2 * B) *
        ∑ n ∈ T, zetaMoebiusLogMajorant n * zetaPrimeExpWeight (3 / 2) n := by
      exact (Finset.mul_sum T _ _).symm
    _ ≤ ((1 / 2 : ℝ) ^ N * X ^ 2 * B) * zetaMoebiusLogMajorantMass (3 / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 3 / 2)).sum_le_tsum T
        (fun n _ ↦ hw n)
    _ = _ := by unfold zetaArithmeticSmallProductConstant; dsimp [B]; ring

/-- The corresponding complex finite sum is bounded only after all its
signed atoms are specified; the richer sum remains available upstream. -/
theorem norm_sum_zetaArithmetic_small_product_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) (T : Finset ℕ) (X : ℕ)
    (hT : ∀ n ∈ T, n ≤ X) :
    ‖∑ n ∈ T, a n * zetaPrimeFilterKernel P N (3 / 2 + I * y) n‖ ≤
      (1 / 2 : ℝ) ^ N * (X : ℝ) ^ 2 * zetaArithmeticSmallProductConstant P :=
  (norm_sum_le _ _).trans (sum_norm_zetaArithmetic_small_product_le a ha P N y T X hT)

private theorem cubic_small_product_rate {u : ℝ} (hu : 1 / 2 < u) :
    0 ≤ u * zetaMoebiusHeadGrowth u ^ 6 / 2 ∧
      u * zetaMoebiusHeadGrowth u ^ 6 / 2 ≤ 3 / 4 := by
  have hu0 : 0 < u := by linarith
  have hs0 := Real.sqrt_pos.mpr hu0
  have hs := Real.sq_sqrt hu0.le
  have hq2 : zetaMoebiusHeadGrowth u ^ 2 = (Real.sqrt u)⁻¹ := by
    rw [zetaMoebiusHeadGrowth, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg u)]
  have hq6 : zetaMoebiusHeadGrowth u ^ 6 = ((Real.sqrt u)⁻¹) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hq2]
  have he : u * zetaMoebiusHeadGrowth u ^ 6 / 2 = 1 / (2 * Real.sqrt u) := by
    rw [hq6]
    field_simp
    nlinarith [hs]
  have hs23 : 2 / 3 < Real.sqrt u := by nlinarith
  rw [he]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt u)).mpr
    nlinarith

/-- Every coefficient family under the original divisor-log majorant has
an independent geometric bound below the cube of the actual divisor
schedule. The selected subset and ordinate may be arbitrary. -/
theorem norm_normalized_sum_zetaArithmetic_cubic_product_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (T : Finset ℕ)
    (hT : ∀ n ∈ T, n ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N ^ 3) :
    ‖(u : ℂ) ^ (N + 1) *
      ∑ n ∈ T, a n * zetaPrimeFilterKernel P N (3 / 2 + I * y) n‖ ≤
        zetaArithmeticSmallProductConstant P * (3 / 4 : ℝ) ^ N := by
  let q := zetaMoebiusHeadGrowth u
  let D := zetaMoebiusGeometricCutoff q N
  let C := zetaArithmeticSmallProductConstant P
  have hu0 : 0 < u := by linarith
  have hq : 0 ≤ q := by dsimp [q, zetaMoebiusHeadGrowth]; positivity
  have hC : 0 ≤ C := zetaArithmeticSmallProductConstant_nonneg P
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq N)
  have hD6 : (D : ℝ) ^ 6 ≤ (q ^ N) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg D) hD 6
  have hb := norm_sum_zetaArithmetic_small_product_le a ha P N y T (D ^ 3) hT
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  calc
    _ ≤ u ^ (N + 1) * ((1 / 2 : ℝ) ^ N * ((D ^ 3 : ℕ) : ℝ) ^ 2 * C) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hu0.le _)
    _ = u ^ (N + 1) * ((1 / 2 : ℝ) ^ N * (D : ℝ) ^ 6 * C) := by
      push_cast
      ring
    _ ≤ u ^ (N + 1) * ((1 / 2 : ℝ) ^ N * (q ^ N) ^ 6 * C) := by gcongr
    _ = (u * C) * (u * q ^ 6 / 2) ^ N := by
      rw [show (q ^ N) ^ 6 = (q ^ 6) ^ N by rw [← pow_mul, Nat.mul_comm N, pow_mul]]
      simp only [div_eq_mul_inv, mul_pow, pow_succ]
      ring
    _ ≤ C * (3 / 4 : ℝ) ^ N := by
      apply mul_le_mul
      · exact mul_le_of_le_one_left hC hu1.le
      · exact pow_le_pow_left₀ (cubic_small_product_rate hu).1
          (cubic_small_product_rate hu).2 N
      · exact pow_nonneg (cubic_small_product_rate hu).1 N
      · exact hC

/-- The normalized smaller-product contribution vanishes uniformly for
arbitrary changing coefficients and subsets satisfying the same bounds. -/
theorem tendsto_normalized_sum_zetaArithmetic_cubic_product (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (T : ℕ → Finset ℕ)
    (hT : ∀ N n, n ∈ T N → n ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N ^ 3) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      ∑ n ∈ T N, a N n * zetaPrimeFilterKernel P N (3 / 2 + I * y) n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦
    norm_normalized_sum_zetaArithmetic_cubic_product_le (a N) (ha N) P N y hu hu1 (T N) (hT N))
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).const_mul (zetaArithmeticSmallProductConstant P)

end
end RiemannGaussian
