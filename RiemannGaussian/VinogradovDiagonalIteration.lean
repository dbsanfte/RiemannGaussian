/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDiagonalThreshold

/-!
# Finite quantitative iteration of the actual homogeneous moments

Start from the proved diagonal k-th moment. Each step adds k to the
moment order and multiplies the defect by 1-1/k. The coefficient recurrence
retains the independent small-endpoint allowance as a maximum. After 7k
steps the relative defect is at most k^2/256, with every coefficient and
every positive integer endpoint specified and no moment premise remaining.
-/

namespace RiemannGaussian.VinogradovDiagonalIteration
noncomputable section
open scoped BigOperators Classical
open VinogradovMeanValue VinogradovDiagonalExponent VinogradovDiagonalThreshold

/-- The actual tuple order after n applications of the moment step. -/
def order (k n : ℕ) : ℕ := (n + 1) * k

/-- The exact remaining defect, before any numerical relaxation. -/
def defect (k n : ℕ) : ℝ := (k.choose 2 : ℝ) * (1 - 1 / (k : ℝ)) ^ n

/-- Every coefficient is specified by a finite natural-number recursion. -/
def coefficient (k : ℕ) : ℕ → ℕ
  | 0 => k.factorial
  | n + 1 => nextCoefficient k (order k n) (coefficient k n)

/-- The moment order increases by exactly k. -/
theorem order_succ (k n : ℕ) : order k (n + 1) = order k n + k := by
  unfold order
  ring

/-- The exact defect ratio is retained at every step. -/
theorem defect_succ (k n : ℕ) : defect k (n + 1) = defect k n * (1 - 1 / (k : ℝ)) := by
  unfold defect
  rw [pow_succ]
  ring

/-- The contraction factor is nonnegative. -/
theorem factor_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ 1 - 1 / (k : ℝ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hkR)

/-- The defect remains nonnegative throughout the actual iteration. -/
theorem defect_nonneg {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : 0 ≤ defect k n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (factor_nonneg hk) _)

/-- The exact initial defect bounds every subsequent defect. -/
theorem defect_le_initial {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : defect k n ≤ k.choose 2 := by
  have hfactor : 1 - 1 / (k : ℝ) ≤ 1 := by
    have h : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hp := pow_le_one₀ (n := n) (factor_nonneg hk) hfactor
  simpa only [defect, mul_one] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (k.choose 2))

/-- The full admissible defect interval is preserved, including the initial order. -/
theorem defect_le_square {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : defect k n ≤ (k : ℝ) ^ 2 := by
  apply (defect_le_initial hk n).trans
  exact_mod_cast Nat.choose_le_pow k 2

/-- At the initial order the count exponent is exactly k. -/
theorem initial_exponent (k : ℕ) : exponent k (order k 0) (defect k 0) = k := by
  simp only [exponent, order, zero_add, one_mul, defect, pow_zero, mul_one,
    degreeWeight, Nat.cast_add]
  ring

/-- The exponent needed by every quotient moment is nonnegative. -/
theorem exponent_nonneg {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    0 ≤ exponent k (order k n) (defect k n) := by
  induction n with
  | zero => rw [initial_exponent]; exact Nat.cast_nonneg k
  | succ n ih =>
    rw [order_succ, defect_succ, ← next_exponent (by omega : 0 < k)]
    exact add_nonneg (add_nonneg (Nat.cast_nonneg k) ih)
      (div_nonneg (sub_nonneg.mpr (defect_le_square hk n)) (Nat.cast_nonneg k))

/-- The finite iteration bounds actual moments at every positive integer
endpoint, with no supplied moment estimate or unevaluated coefficient. -/
theorem iterated_moment_bound {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    ∀ P : ℕ, 1 ≤ P → meanValue (order k n) k P ≤
      (coefficient k n : ℝ) * (P : ℝ) ^ exponent k (order k n) (defect k n) := by
  induction n with
  | zero =>
    intro P hP
    have h := VinogradovPowerSumRigidity.meanValue_le (r := k) (k := k) (N := P) le_rfl
    rw [initial_exponent, Real.rpow_natCast]
    simpa only [order, zero_add, one_mul, coefficient, mul_comm, Nat.mul_one] using h
  | succ n ih =>
    intro P hP
    have hs : 1 ≤ order k n := by
      unfold order
      exact Nat.mul_pos (by omega) (by omega)
    have h := all_endpoint_defect_step hk hs (defect_nonneg (by omega) n)
      (defect_le_square (by omega) n) (exponent_nonneg (by omega) n) ih P hP
    simpa only [coefficient, order_succ, defect_succ] using h

/-- A block of k actual descent steps at least halves the remaining defect. -/
theorem factor_pow_degree_le_half {k : ℕ} (hk : 1 ≤ k) :
    (1 - 1 / (k : ℝ)) ^ k ≤ 1 / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hb := one_add_mul_le_pow (a := 1 / (k : ℝ)) (by
    have h : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith : -2 ≤ 1 / (k : ℝ)) k
  rw [mul_one_div_cancel hkR.ne'] at hb
  have ha := factor_nonneg hk
  have hprod : (1 - 1 / (k : ℝ)) ^ k * (1 + 1 / (k : ℝ)) ^ k ≤ 1 := by
    rw [← mul_pow]
    calc
      _ ≤ (1 : ℝ) ^ k := pow_le_pow_left₀ (mul_nonneg ha (by positivity))
        (by nlinarith [sq_nonneg (1 / (k : ℝ))]) k
      _ = 1 := one_pow k
  have h := mul_le_mul_of_nonneg_left hb (pow_nonneg ha k)
  nlinarith

/-- Seven blocks of k steps give a fixed relative defect below 1/256. -/
theorem defect_seven_degree_le {k : ℕ} (hk : 1 ≤ k) :
    defect k (7 * k) ≤ (k : ℝ) ^ 2 / 256 := by
  have hp : (1 - 1 / (k : ℝ)) ^ (7 * k) ≤ (1 / 128 : ℝ) := by
    rw [Nat.mul_comm 7 k, pow_mul]
    have h := pow_le_pow_left₀ (pow_nonneg (factor_nonneg hk) k)
      (factor_pow_degree_le_half hk) 7
    norm_num at h ⊢
    exact h
  have hc : (k.choose 2 : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h := power_gap hk 0 (0 : ℝ)
    rw [← Nat.choose_two_right] at h
    norm_num [exponent, degreeWeight] at h
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    linarith
  have h := mul_le_mul hp hc (Nat.cast_nonneg (k.choose 2)) (by norm_num : (0 : ℝ) ≤ 1 / 128)
  unfold defect
  nlinarith

/-- The degree weight is the exact critical half-quadratic expression. -/
theorem degreeWeight_cast {k : ℕ} (hk : 1 ≤ k) :
    (degreeWeight k : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have h := power_gap hk 0 (0 : ℝ)
  rw [← Nat.choose_two_right] at h
  norm_num [exponent, degreeWeight] at h
  simp only [degreeWeight, Nat.cast_add]
  nlinarith

/-- A concrete all-endpoint relative-defect moment bound, at the actual
order (7k+1)k, with a fully specified finite coefficient and no premise. -/
theorem relative_moment_bound {k : ℕ} (hk : 2 ≤ k) (P : ℕ) (hP : 1 ≤ P) :
    meanValue ((7 * k + 1) * k) k P ≤ (coefficient k (7 * k) : ℝ) *
      (P : ℝ) ^ (2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256) := by
  have h := iterated_moment_bound hk (7 * k) P hP
  have he : exponent k (order k (7 * k)) (defect k (7 * k)) ≤
      2 * (((7 * k + 1) * k : ℕ) : ℝ) -
        (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) ^ 2 / 256 := by
    unfold exponent order
    rw [degreeWeight_cast (by omega)]
    linarith [defect_seven_degree_le (by omega : 1 ≤ k)]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP) he) (Nat.cast_nonneg _))

end
end RiemannGaussian.VinogradovDiagonalIteration
