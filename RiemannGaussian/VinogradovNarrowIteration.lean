/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNarrowThreshold
import RiemannGaussian.VinogradovDiagonalIteration

/-!
# Finite homogeneous moment iteration with the shorter prime packet

The actual moment orders and exact defects are unchanged from the diagonal
iteration. Only the fully proved packet and small-endpoint coefficients
change. Every positive integer endpoint is included, with no supplied
moment estimate and no unevaluated starting threshold.
-/

namespace RiemannGaussian.VinogradovNarrowIteration
noncomputable section
open VinogradovMeanValue VinogradovDiagonalExponent
open VinogradovDiagonalIteration VinogradovNarrowThreshold

/-- The finite coefficient recurrence pays the actual fixed-width packet. -/
def coefficient (k : ℕ) : ℕ → ℕ
  | 0 => k.factorial
  | n + 1 => nextCoefficient k (order k n) (coefficient k n)

/-- The new packet supplies the full actual moment estimate at every
stage and every positive endpoint, with the exact original defect. -/
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

/-- The fixed-width packet reaches the same relative defect at the
actual order (7k+1)k, with its own fully specified coefficient. -/
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
end RiemannGaussian.VinogradovNarrowIteration
