/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovExponentialDefect

/-!
# Smaller actual moment orders with fully paid coefficients

The exact exponential defect allows orders (3k+1)k and (4k+1)k.
The complete finite coefficient is at most (2^41*k^6)^(k^3), and both
moment factors with the original Gaussian cost fit within multiplier
two after their actual high-moment root. All positive endpoints remain.
-/

namespace RiemannGaussian.VinogradovShortMoment
noncomputable section
open VinogradovMeanValue VinogradovDiagonalExponent
open VinogradovDiagonalIteration (order defect degreeWeight_cast)
open VinogradovNarrowThreshold (threshold packetCoefficient)
open VinogradovNarrowCost

/-- One closed coefficient pays every stage through four degree blocks. -/
def coefficient (k : ℕ) : ℕ := (2 ^ 41 * k ^ 6) ^ (k ^ 3)

/-- The shorter iteration retains every small-endpoint reserve, with
only its genuine packet multipliers accumulating. -/
theorem coefficient_le_short {k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ 4 * k) :
    VinogradovNarrowIteration.coefficient k n ≤ coefficient k := by
  have hk0 : 0 < k := by omega
  have horder : order k n ≤ 8 * k ^ 2 := by
    unfold order
    nlinarith
  have hsmall := small_allowance_le hk horder
  have hfac : k.factorial ≤ (8192 * k ^ 6) ^ (k ^ 3) := by
    have hpos : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
    apply (VinogradovDiagonalCost.factorial_le_binary_square k).trans
    calc
      2 ^ (k ^ 2) ≤ 2 ^ (k ^ 3) :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right hk0 (by omega))
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ max k.factorial (threshold k (order k n) ^ degreeWeight k) *
        packetCoefficient k ^ n := coefficient_le hk0 _
    _ ≤ (8192 * k ^ 6) ^ (k ^ 3) * (2 ^ (7 * k ^ 2)) ^ n :=
      Nat.mul_le_mul (max_le hfac hsmall) (Nat.pow_le_pow_left (packetCoefficient_le hk) _)
    _ ≤ (8192 * k ^ 6) ^ (k ^ 3) * (2 ^ (7 * k ^ 2)) ^ (4 * k) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by positivity) hn)
    _ = (8192 * k ^ 6) ^ (k ^ 3) * (2 ^ 28) ^ (k ^ 3) := by
      congr 1
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ = _ := by
      rw [← mul_pow]
      unfold coefficient
      congr 1
      norm_num
      ring

/-- A direct binary envelope for the full finite coefficient. -/
theorem coefficient_le_binary (k : ℕ) : coefficient k ≤ 2 ^ ((41 + 6 * k) * k ^ 3) := by
  have hk6 : k ^ 6 ≤ 2 ^ (6 * k) := by
    simpa only [← pow_mul, Nat.mul_comm k 6] using
      Nat.pow_le_pow_left (show k ≤ 2 ^ k from Nat.lt_two_pow_self.le) 6
  unfold coefficient
  calc
    _ ≤ (2 ^ 41 * 2 ^ (6 * k)) ^ (k ^ 3) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hk6) _
    _ = _ := by rw [← pow_add, ← pow_mul]

/-- Both full moment coefficients and the entire Gaussian allowance
cost at most two at every moment order at least (3k+1)k. -/
theorem two_moments_gaussian_le {k r : ℕ} (hk : 12 ≤ k) (hr : (3 * k + 1) * k ≤ r) :
    coefficient k ^ 2 * 2 ^ (9 * k ^ 2) ≤ 2 ^ (2 * r * r) := by
  have hk2 : 12 * k ≤ k ^ 2 := by
    simpa only [pow_two, Nat.mul_comm k 12] using Nat.mul_le_mul_left k hk
  have hscalar : 82 * k + 12 * k ^ 2 + 9 ≤ 2 * (3 * k + 1) ^ 2 := by nlinarith
  have he : ((41 + 6 * k) * k ^ 3) * 2 + 9 * k ^ 2 ≤ 2 * r * r := by
    calc
      _ = (82 * k + 12 * k ^ 2 + 9) * k ^ 2 := by ring
      _ ≤ (2 * (3 * k + 1) ^ 2) * k ^ 2 := Nat.mul_le_mul_right _ hscalar
      _ = 2 * ((3 * k + 1) * k) * ((3 * k + 1) * k) := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) hr
  calc
    _ ≤ (2 ^ ((41 + 6 * k) * k ^ 3)) ^ 2 * 2 ^ (9 * k ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (coefficient_le_binary k) 2)
    _ = 2 ^ (((41 + 6 * k) * k ^ 3) * 2 + 9 * k ^ 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- The actual moment on every positive endpoint retains the exact
descent defect and the evaluated coefficient through four degree blocks. -/
theorem moment_bound {k n : ℕ} (hk : 2 ≤ k) (hn : n ≤ 4 * k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue (order k n) k P ≤ (coefficient k : ℝ) *
      (P : ℝ) ^ (2 * (order k n : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + defect k n) := by
  have h := VinogradovNarrowIteration.iterated_moment_bound hk n P hP
  unfold exponent at h
  rw [degreeWeight_cast (by omega : 1 ≤ k)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast coefficient_le_short hk hn)
    (Real.rpow_nonneg (Nat.cast_nonneg P) _))

/-- Three blocks give a literal all-endpoint moment with relative defect 1/40. -/
theorem moment_three_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((3 * k + 1) * k) k P ≤ (coefficient k : ℝ) *
      (P : ℝ) ^ (2 * (((3 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 40) := by
  apply (moment_bound hk (show 3 * k ≤ 4 * k by omega) P hP).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP)
  dsimp only [order]
  linarith only [VinogradovExponentialDefect.defect_three_degree_le (by omega : 1 ≤ k)]

/-- Four blocks give a literal all-endpoint moment with relative defect 1/100. -/
theorem moment_four_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((4 * k + 1) * k) k P ≤ (coefficient k : ℝ) *
      (P : ℝ) ^ (2 * (((4 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 100) := by
  apply (moment_bound hk (show 4 * k ≤ 4 * k from le_rfl) P hP).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP)
  dsimp only [order]
  linarith only [VinogradovExponentialDefect.defect_four_degree_le (by omega : 1 ≤ k)]

end
end RiemannGaussian.VinogradovShortMoment
