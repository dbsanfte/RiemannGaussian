/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowIteration
import RiemannGaussian.VinogradovDiagonalCost

/-!
# A cubic-logarithmic coefficient for the actual moment bound

The fixed-width packet and polynomial root threshold give the closed
coefficient (2^62*k^6)^(k^3) at order (7k+1)k and defect k^2/256.
Every small endpoint and every finite iteration coefficient is paid.
The result concerns actual homogeneous moments and has no moment premise.
-/

namespace RiemannGaussian.VinogradovNarrowCost
noncomputable section
open VinogradovMeanValue VinogradovDiagonalExponent
open VinogradovNarrowThreshold VinogradovNarrowIteration
open VinogradovDiagonalIteration (order order_succ)

/-- The root threshold is monotone in moment order. -/
theorem base_mono {s t : ℕ} (hst : s ≤ t) (k : ℕ) : base k s ≤ base k t := by
  unfold base
  apply max_le_max le_rfl
  apply max_le_max le_rfl
  apply max_le_max _ le_rfl
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hst 2)

/-- The original endpoint threshold inherits this monotonicity. -/
theorem threshold_mono {s t : ℕ} (hst : s ≤ t) (k : ℕ) :
    threshold k s ≤ threshold k t := Nat.pow_le_pow_left (base_mono hst k) k

/-- The full fixed-width packet multiplier is strictly positive. -/
theorem packetCoefficient_pos {k : ℕ} (hk : 0 < k) : 0 < packetCoefficient k := by
  unfold packetCoefficient
  positivity

/-- The largest independent small-endpoint reserve pays every preceding
one, while only the genuine packet multiplier accumulates multiplicatively. -/
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

/-- All root-scale requirements are polynomial in the degree through the
entire seven-degree-block iteration. -/
theorem base_le_polynomial {k s : ℕ} (hk : 2 ≤ k) (hs : s ≤ 8 * k ^ 2) :
    base k s ≤ 8192 * k ^ 6 := by
  have hk0 : 0 < k := by omega
  have h46 : k ^ 4 ≤ k ^ 6 := Nat.pow_le_pow_right hk0 (by omega)
  have hk6 : k ≤ k ^ 6 := Nat.le_self_pow (by omega : (6 : ℕ) ≠ 0) k
  have hpos : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold base
  refine max_le (by nlinarith) (max_le (by omega) (max_le ?_ (max_le ?_ ?_)))
  · calc
      128 * s ^ 2 ≤ 128 * (8 * k ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _ = 8192 * k ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h46
  · omega
  · omega

/-- The entire independent small-endpoint reserve has a cubic degree
exponent over a polynomial base. -/
theorem small_allowance_le {k s : ℕ} (hk : 2 ≤ k) (hs : s ≤ 8 * k ^ 2) :
    threshold k s ^ degreeWeight k ≤ (8192 * k ^ 6) ^ (k ^ 3) := by
  have hk0 : 0 < k := by omega
  have hb := base_le_polynomial hk hs
  have hw := VinogradovDiagonalCost.degreeWeight_le_square (by omega : 1 ≤ k)
  unfold threshold
  calc
    _ ≤ ((8192 * k ^ 6) ^ k) ^ degreeWeight k :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left hb k) (degreeWeight k)
    _ = (8192 * k ^ 6) ^ (k * degreeWeight k) := (pow_mul _ _ _).symm
    _ ≤ (8192 * k ^ 6) ^ (k * k ^ 2) :=
      Nat.pow_le_pow_right (by positivity)
        (Nat.mul_le_mul_left _ hw)
    _ = _ := by congr 1; ring

/-- The shorter packet reduces the single-step binary exponent to a
quadratic degree cost, independently of the current moment order. -/
theorem packetCoefficient_le {k : ℕ} (hk : 2 ≤ k) : packetCoefficient k ≤ 2 ^ (7 * k ^ 2) := by
  have hkpow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hk3 : k ^ 3 ≤ 2 ^ (3 * k) := by
    simpa only [← pow_mul, Nat.mul_comm k 3] using Nat.pow_le_pow_left hkpow 3
  have hfac := VinogradovDiagonalCost.factorial_le_binary_square k
  have he : 3 + 3 * k + 4 * k ^ 2 ≤ 7 * k ^ 2 := by nlinarith
  unfold packetCoefficient
  calc
    _ ≤ 8 * 2 ^ (3 * k) * 2 ^ (k ^ 2) * 8 ^ (k ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk3) hfac)
    _ = 2 ^ (3 + 3 * k + 4 * k ^ 2) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- The complete 7k-step coefficient now grows with cubic times
logarithmic degree cost, including every small-endpoint allowance. -/
theorem coefficient_seven_degree_le {k : ℕ} (hk : 2 ≤ k) :
    coefficient k (7 * k) ≤ (2 ^ 62 * k ^ 6) ^ (k ^ 3) := by
  have hk0 : 0 < k := by omega
  have horder : order k (7 * k) ≤ 8 * k ^ 2 := by unfold order; nlinarith
  have hsmall := small_allowance_le hk horder
  have hfac : k.factorial ≤ (8192 * k ^ 6) ^ (k ^ 3) := by
    have hpos : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
    apply (VinogradovDiagonalCost.factorial_le_binary_square k).trans
    calc
      2 ^ (k ^ 2) ≤ 2 ^ (k ^ 3) :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right hk0 (by omega))
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ max k.factorial (threshold k (order k (7 * k)) ^ degreeWeight k) *
        packetCoefficient k ^ (7 * k) := coefficient_le hk0 _
    _ ≤ (8192 * k ^ 6) ^ (k ^ 3) * (2 ^ (7 * k ^ 2)) ^ (7 * k) :=
      Nat.mul_le_mul (max_le hfac hsmall) (Nat.pow_le_pow_left (packetCoefficient_le hk) _)
    _ = (8192 * k ^ 6) ^ (k ^ 3) * (2 ^ 49) ^ (k ^ 3) := by
      congr 1
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ = _ := by
      rw [← mul_pow]
      congr 1
      norm_num
      ring

/-- A binary envelope for the closed coefficient, useful when taking
the original product's high-moment root. -/
theorem explicit_coefficient_le_binary (k : ℕ) :
    (2 ^ 62 * k ^ 6) ^ (k ^ 3) ≤ 2 ^ ((62 + 6 * k) * k ^ 3) := by
  have hk6 : k ^ 6 ≤ 2 ^ (6 * k) := by
    simpa only [← pow_mul, Nat.mul_comm k 6] using
      Nat.pow_le_pow_left (show k ≤ 2 ^ k from Nat.lt_two_pow_self.le) 6
  calc
    _ ≤ (2 ^ 62 * 2 ^ (6 * k)) ^ (k ^ 3) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hk6) _
    _ = _ := by rw [← pow_add, ← pow_mul]

/-- Both actual moment coefficients and the entire quadratic Gaussian
allowance together cost at most two after the product's exact high-moment root. -/
theorem two_moments_gaussian_le {k : ℕ} (hk : 2 ≤ k) :
    ((2 ^ 62 * k ^ 6) ^ (k ^ 3)) ^ 2 * 2 ^ (9 * k ^ 2) ≤
      2 ^ (2 * ((7 * k + 1) * k) * ((7 * k + 1) * k)) := by
  have hk2 : 2 * k ≤ k ^ 2 := by
    simpa only [pow_two, Nat.mul_comm k 2] using Nat.mul_le_mul_left k hk
  have hscalar : 124 * k + 12 * k ^ 2 + 9 ≤ 2 * (7 * k + 1) ^ 2 := by nlinarith
  have he : ((62 + 6 * k) * k ^ 3) * 2 + 9 * k ^ 2 ≤
      2 * ((7 * k + 1) * k) * ((7 * k + 1) * k) := by
    calc
      _ = (124 * k + 12 * k ^ 2 + 9) * k ^ 2 := by ring
      _ ≤ (2 * (7 * k + 1) ^ 2) * k ^ 2 := Nat.mul_le_mul_right _ hscalar
      _ = _ := by ring
  calc
    _ ≤ (2 ^ ((62 + 6 * k) * k ^ 3)) ^ 2 * 2 ^ (9 * k ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (explicit_coefficient_le_binary k) 2)
    _ = 2 ^ (((62 + 6 * k) * k ^ 3) * 2 + 9 * k ^ 2) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- A fully explicit actual homogeneous moment bound with the improved
cubic-logarithmic degree cost, for every positive integer endpoint. -/
theorem explicit_relative_moment_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((7 * k + 1) * k) k P ≤ (((2 ^ 62 * k ^ 6) ^ (k ^ 3) : ℕ) : ℝ) *
      (P : ℝ) ^ (2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256) := by
  apply (relative_moment_bound hk P hP).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg P) _)
  exact_mod_cast coefficient_seven_degree_le hk

end
end RiemannGaussian.VinogradovNarrowCost
