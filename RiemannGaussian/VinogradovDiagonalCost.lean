/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDiagonalIteration

/-!
# A closed degree cost for the complete diagonal moment iteration

The maximum recurrence keeps the small-endpoint cost outside repeated
multiplication. Elementary integer inequalities then bound every packet
cost and threshold. The resulting actual moment bound has coefficient
at most 2^(18*k^6), valid at all positive integer endpoints. Its tuple
order is (7k+1)k, so it is distinct from the earlier k(k+1)-order bounds.
-/

namespace RiemannGaussian.VinogradovDiagonalCost
noncomputable section
open scoped BigOperators Classical
open VinogradovMeanValue VinogradovDiagonalExponent
open VinogradovDiagonalThreshold VinogradovDiagonalIteration

/-- Increasing the moment order only increases the explicit root-scale threshold. -/
theorem base_mono {s t : ℕ} (hst : s ≤ t) (k : ℕ) : base k s ≤ base k t := by
  unfold base
  apply max_le_max le_rfl
  apply max_le_max le_rfl
  apply max_le_max _ le_rfl
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hst 2))

/-- The physical threshold is monotone in the original moment order. -/
theorem threshold_mono {s t : ℕ} (hst : s ≤ t) (k : ℕ) :
    threshold k s ≤ threshold k t := Nat.pow_le_pow_left (base_mono hst k) k

/-- The complete packet multiplier is a positive explicit integer. -/
theorem packetCoefficient_pos {k : ℕ} (hk : 0 < k) : 0 < packetCoefficient k := by
  unfold packetCoefficient
  positivity

/-- The independent small-endpoint allowance is paid once at the largest
threshold, instead of being multiplied into every previous coefficient. -/
theorem coefficient_le {k : ℕ} (hk : 0 < k) (n : ℕ) :
    coefficient k n ≤
      max k.factorial (threshold k (order k n) ^ degreeWeight k) * packetCoefficient k ^ n := by
  induction n with
  | zero =>
    simpa only [coefficient, pow_zero, mul_one] using
      (le_max_left k.factorial (threshold k (order k 0) ^ degreeWeight k))
  | succ n ih =>
    have horder : order k n ≤ order k (n + 1) := by rw [order_succ]; omega
    have hsmall := Nat.pow_le_pow_left (threshold_mono horder k) (degreeWeight k)
    have hmax := max_le_max (le_refl k.factorial) hsmall
    rw [coefficient, nextCoefficient]
    apply max_le
    · exact (hsmall.trans (le_max_right _ _)).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (packetCoefficient_pos hk) _))
    · calc
        _ ≤ packetCoefficient k *
            (max k.factorial (threshold k (order k n) ^ degreeWeight k) * packetCoefficient k ^ n) :=
          Nat.mul_le_mul_left _ ih
        _ ≤ packetCoefficient k *
            (max k.factorial (threshold k (order k (n + 1)) ^ degreeWeight k) * packetCoefficient k ^ n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmax)
        _ = _ := by rw [pow_succ]; ring

/-- The factorial term has an elementary quadratic binary exponent. -/
theorem factorial_le_binary_square (k : ℕ) : k.factorial ≤ 2 ^ (k ^ 2) := by
  calc
    _ ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (show k ≤ 2 ^ k from Nat.lt_two_pow_self.le) k
    _ = _ := by rw [← pow_mul, pow_two]

/-- The exact critical degree weight is at most k squared. -/
theorem degreeWeight_le_square {k : ℕ} (hk : 1 ≤ k) : degreeWeight k ≤ k ^ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h : (degreeWeight k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rw [degreeWeight_cast hk]
    nlinarith
  exact_mod_cast h

/-- All root-scale conditions up to order 8k^2 fit in one cubic binary exponent. -/
theorem base_le_binary_cube {k s : ℕ} (hk : 2 ≤ k) (hs : s ≤ 8 * k ^ 2) :
    base k s ≤ 2 ^ (4 * k ^ 3) := by
  have hk3 : 4 * k ≤ k ^ 3 := by
    have h := Nat.mul_le_mul_right k (Nat.pow_le_pow_left hk 2)
    norm_num only [Nat.reducePow] at h
    simpa only [pow_succ] using h
  have hkpow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hk4 : k ^ 4 ≤ 2 ^ (4 * k) := by
    simpa only [← pow_mul, Nat.mul_comm k 4] using Nat.pow_le_pow_left hkpow 4
  have hlinear : 2 + 4 * k ≤ 4 * k ^ 3 := by omega
  have htail : 10 + 4 * k + k ^ 3 ≤ 4 * k ^ 3 := by omega
  unfold base
  apply max_le
  · exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : k ≤ 4 * k ^ 3)
  · apply max_le
    · calc
        4 * k ^ 4 ≤ 4 * 2 ^ (4 * k) := Nat.mul_le_mul_left _ hk4
        _ = 2 ^ (2 + 4 * k) := by rw [pow_add]; norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by omega) hlinear
    · apply max_le
      · calc
          16 * s ^ 2 * 2 ^ (k ^ 3) ≤ 16 * (8 * k ^ 2) ^ 2 * 2 ^ (k ^ 3) := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2))
          _ = 2 ^ 10 * k ^ 4 * 2 ^ (k ^ 3) := by norm_num; ring
          _ ≤ 2 ^ 10 * 2 ^ (4 * k) * 2 ^ (k ^ 3) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk4)
          _ = 2 ^ (10 + 4 * k + k ^ 3) := by rw [pow_add, pow_add]
          _ ≤ _ := Nat.pow_le_pow_right (by omega) htail
      · exact (show k + 1 ≤ 2 ^ k from Nat.lt_two_pow_self).trans
          (Nat.pow_le_pow_right (by omega) (by omega : k ≤ 4 * k ^ 3))

/-- The complete small-endpoint allowance has a sixth-degree binary cost. -/
theorem small_allowance_le {k s : ℕ} (hk : 2 ≤ k) (hs : s ≤ 8 * k ^ 2) :
    threshold k s ^ degreeWeight k ≤ 2 ^ (4 * k ^ 6) := by
  have hb := base_le_binary_cube hk hs
  have hw := degreeWeight_le_square (by omega : 1 ≤ k)
  unfold threshold
  calc
    _ ≤ ((2 ^ (4 * k ^ 3)) ^ k) ^ degreeWeight k :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hb k) (degreeWeight k)
    _ = 2 ^ ((4 * k ^ 3) * k * degreeWeight k) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ 2 ^ ((4 * k ^ 3) * k * k ^ 2) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hw)
    _ = _ := by congr 1; ring

/-- The complete single-step multiplier has a fifth-degree binary cost. -/
theorem packetCoefficient_le {k : ℕ} (hk : 2 ≤ k) : packetCoefficient k ≤ 2 ^ (2 * k ^ 5) := by
  have hkpow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hk3 : k ^ 3 ≤ 2 ^ (3 * k) := by
    simpa only [← pow_mul, Nat.mul_comm k 3] using Nat.pow_le_pow_left hkpow 3
  have hk2 : 4 ≤ k ^ 2 := by simpa using Nat.pow_le_pow_left hk 2
  have hk5 : 8 * k ^ 2 ≤ k ^ 5 := by
    have h := Nat.mul_le_mul_right (k ^ 2) (Nat.pow_le_pow_left hk 3)
    norm_num only [Nat.reducePow] at h
    simpa only [← pow_add, show (3 : ℕ) + 2 = 5 by omega] using h
  have hkself : k ≤ k ^ 2 := Nat.le_self_pow (by omega : (2 : ℕ) ≠ 0) k
  have he : 2 + 3 * k + k ^ 2 + k ^ 5 ≤ 2 * k ^ 5 := by omega
  unfold packetCoefficient
  calc
    _ ≤ 4 * 2 ^ (3 * k) * 2 ^ (k ^ 2) * 2 ^ (k ^ 3 * k ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk3) (factorial_le_binary_square k))
    _ = 2 ^ (2 + 3 * k + k ^ 2 + k ^ 5) := by
      rw [show k ^ 3 * k ^ 2 = k ^ 5 by ring, pow_add, pow_add, pow_add]
      norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- All costs in the 7k-step actual moment bound fit in one closed
sixth-degree binary exponent; no profile-depth constant remains. -/
theorem coefficient_seven_degree_le {k : ℕ} (hk : 2 ≤ k) :
    coefficient k (7 * k) ≤ 2 ^ (18 * k ^ 6) := by
  have hk0 : 0 < k := by omega
  have horder : order k (7 * k) ≤ 8 * k ^ 2 := by unfold order; nlinarith
  have hsmall := small_allowance_le hk horder
  have hfac : k.factorial ≤ 2 ^ (4 * k ^ 6) := by
    apply (factorial_le_binary_square k).trans
    apply Nat.pow_le_pow_right (by omega)
    have h : k ^ 2 ≤ k ^ 6 := Nat.pow_le_pow_right hk0 (by omega)
    omega
  calc
    _ ≤ max k.factorial (threshold k (order k (7 * k)) ^ degreeWeight k) *
        packetCoefficient k ^ (7 * k) := coefficient_le hk0 _
    _ ≤ 2 ^ (4 * k ^ 6) * (2 ^ (2 * k ^ 5)) ^ (7 * k) :=
      Nat.mul_le_mul (max_le hfac hsmall) (Nat.pow_le_pow_left (packetCoefficient_le hk) _)
    _ = 2 ^ (18 * k ^ 6) := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- A fully explicit unconditional homogeneous moment estimate, with
relative defect k^2/256 and coefficient 2^(18*k^6), at every positive endpoint. -/
theorem explicit_relative_moment_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((7 * k + 1) * k) k P ≤ ((2 ^ (18 * k ^ 6) : ℕ) : ℝ) *
      (P : ℝ) ^ (2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256) := by
  apply (relative_moment_bound hk P hP).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg P) _)
  exact_mod_cast coefficient_seven_degree_le hk

end
end RiemannGaussian.VinogradovDiagonalCost
