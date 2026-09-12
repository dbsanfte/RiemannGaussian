/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativePowerEnvelope
import RiemannGaussian.FiniteLagPowerBounds

/-!
# Uniform power control of one complete derivative step

The original triangular lag form is bounded using both finite power sums,
with every lag retaining its own scale until those estimates are applied.
The exact analytic cutoff balances the successor powers. Squared leading
and complementary terms then absorb the full step with one coefficient.
-/

namespace RiemannGaussian.DerivativePowerStep
noncomputable section
open DerivativePowerExponents AnalyticDerivativeCutoff DerivativeRecursionBudget
open DerivativePowerEnvelope
open scoped Classical

/-- The complete quantity under the square root in the finite recursion. -/
def argument (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) : ℝ :=
  let H := shiftCount κ k L ℓ A
  (((L : ℝ) + H - 1) * ((H : ℝ) * L +
    2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
      budget κ k L (((j : ℝ) + 1) * ℓ) A)) / (H : ℝ) ^ 2

/-- The full weighted budget sum is controlled by its two power sums;
no lag is replaced by an unweighted maximum. -/
theorem weighted_budget_le (κ : Cutoffs) (k L H : ℕ) {ℓ A : ℝ}
    (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hI : ∀ j ∈ Finset.range H, budget κ k L (((j : ℝ) + 1) * ℓ) A ≤
      envelope k L (((j : ℝ) + 1) * ℓ) A) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
      budget κ k L (((j : ℝ) + 1) * ℓ) A) ≤
        32 * A ^ amp k * L * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
          64 * (L : ℝ) ^ beta k * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ (-alpha k) := by
  let P := 32 * A ^ amp k * L * ℓ ^ alpha k
  let Q := 32 * (L : ℝ) ^ beta k * ℓ ^ (-alpha k)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have he (j : ℕ) : envelope k L (((j : ℝ) + 1) * ℓ) A =
      P * ((j : ℝ) + 1) ^ alpha k + Q * ((j : ℝ) + 1) ^ (-alpha k) := by
    unfold envelope mainTerm errorTerm
    rw [Real.mul_rpow (by positivity : 0 ≤ (j : ℝ) + 1) hℓ.le,
      Real.mul_rpow (by positivity : 0 ≤ (j : ℝ) + 1) hℓ.le]
    dsimp [P, Q]
    ring
  calc
    _ ≤ ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
        (P * ((j : ℝ) + 1) ^ alpha k + Q * ((j : ℝ) + 1) ^ (-alpha k)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      rw [← he]
      exact mul_le_mul_of_nonneg_left (hI j hj) (by linarith)
    _ = P * (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ alpha k) +
        Q * (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ (-alpha k)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ P * ((H : ℝ) ^ 2 * (H : ℝ) ^ alpha k) +
        Q * (2 * (H : ℝ) ^ 2 * (H : ℝ) ^ (-alpha k)) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (FiniteLagPowerBounds.weighted_positive H (alpha_pos k).le) hP)
        (mul_le_mul_of_nonneg_left
          (FiniteLagPowerBounds.weighted_negative H (alpha_pos k).le (alpha_le_half k)) hQ)
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg (α := ℝ) H) hℓ.le,
        Real.mul_rpow (Nat.cast_nonneg (α := ℝ) H) hℓ.le]
      dsimp [P, Q]
      ring

/-- The complete square-root argument has a three-term power bound
whenever the selected count lies within the original length cap. -/
theorem argument_le (κ : Cutoffs) (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (hH : shiftCount κ k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount κ k L ℓ A),
      budget κ k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    argument κ k L ℓ A ≤
      2 * (L : ℝ) ^ 2 / (shiftCount κ k L ℓ A : ℝ) +
        128 * A ^ amp k * (L : ℝ) ^ 2 * ((shiftCount κ k L ℓ A : ℝ) * ℓ) ^ alpha k +
          256 * (L : ℝ) ^ (beta k + 1) *
            ((shiftCount κ k L ℓ A : ℝ) * ℓ) ^ (-alpha k) := by
  let H := shiftCount κ k L ℓ A
  have hHp : 0 < (H : ℝ) := by exact_mod_cast shiftCount_pos κ k L ℓ A
  have hHL : (H : ℝ) ≤ L := by exact_mod_cast hH
  have hLp : 0 < (L : ℝ) := hHp.trans_le hHL
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast shiftCount_pos κ k L ℓ A
  let T := 32 * A ^ amp k * L * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
    64 * (L : ℝ) ^ beta k * (H : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ (-alpha k)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hs := weighted_budget_le κ k L H hℓ hA hI
  change argument κ k L ℓ A ≤ 2 * (L : ℝ) ^ 2 / (H : ℝ) +
    128 * A ^ amp k * (L : ℝ) ^ 2 * ((H : ℝ) * ℓ) ^ alpha k +
      256 * (L : ℝ) ^ (beta k + 1) * ((H : ℝ) * ℓ) ^ (-alpha k)
  calc
    _ ≤ (((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * T)) / (H : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ (2 * (L : ℝ) * ((H : ℝ) * L + 2 * T)) / (H : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by
      dsimp [T]
      rw [Real.rpow_add hLp, Real.rpow_one]
      field_simp
      ring

/-- The analytic cutoff controls the whole successor argument by two
exact squares, with coefficients independent of the derivative order. -/
theorem argument_le_squares (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 1 ≤ A)
    (hH : shiftCount cutoffs k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount cutoffs k L ℓ A),
      budget cutoffs k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    argument cutoffs k L ℓ A ≤
      258 * mainTerm (k + 1) L ℓ A ^ 2 + 256 * errorTerm (k + 1) L ℓ ^ 2 := by
  have hA0 : 0 ≤ A := by linarith
  have hAP := Real.one_le_rpow hA (amp_pos k).le
  have hp := count_positive_power k L hℓ hℓ1 A
  have hn := count_negative_power k L hℓ A
  have hi := inv_count_le k L hℓ A
  have hmain : 0 ≤ A ^ amp k * (L : ℝ) ^ 2 := by positivity
  have hbase : 0 ≤ (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1)) := by positivity
  have h1 : 2 * (L : ℝ) ^ 2 / (shiftCount cutoffs k L ℓ A : ℝ) ≤
      2 * (A ^ amp k * (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1))) := by
    have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * (L : ℝ) ^ 2 by positivity)
    have h' := mul_le_mul_of_nonneg_right hAP hbase
    calc
      _ = 2 * (L : ℝ) ^ 2 * (1 / (shiftCount cutoffs k L ℓ A : ℝ)) := by ring
      _ ≤ 2 * (L : ℝ) ^ 2 * ℓ ^ (2 * alpha (k + 1)) := h
      _ ≤ _ := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 128 * A ^ amp k * (L : ℝ) ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hn (show 0 ≤ 256 * (L : ℝ) ^ (beta k + 1) by positivity)
  apply (argument_le cutoffs k L hℓ hA0 hH hI).trans
  rw [main_square k _ hℓ.le hA0, error_square k (Nat.cast_nonneg _) hℓ.le]
  nlinarith

/-- One common coefficient thirty-two absorbs the complete recursive
step after the actual analytic cutoff and lag estimates are applied. -/
theorem successor_bound (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hA : 1 ≤ A)
    (hH : shiftCount cutoffs k L ℓ A ≤ L)
    (hI : ∀ j ∈ Finset.range (shiftCount cutoffs k L ℓ A),
      budget cutoffs k L (((j : ℝ) + 1) * ℓ) A ≤ envelope k L (((j : ℝ) + 1) * ℓ) A) :
    budget cutoffs (k + 1) L ℓ A ≤ envelope (k + 1) L ℓ A := by
  have hA0 : 0 ≤ A := by linarith
  have hm := main_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le hA0
  have he := error_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le
  have hq : argument cutoffs k L ℓ A ≤ envelope (k + 1) L ℓ A ^ 2 := by
    apply (argument_le_squares k L hℓ hℓ1 hA hH hI).trans
    unfold envelope
    nlinarith [sq_nonneg (mainTerm (k + 1) L ℓ A), sq_nonneg (errorTerm (k + 1) L ℓ),
      mul_nonneg hm he]
  calc
    _ ≤ Real.sqrt (argument cutoffs k L ℓ A) := min_le_right _ _
    _ ≤ Real.sqrt (envelope (k + 1) L ℓ A ^ 2) := Real.sqrt_le_sqrt hq
    _ = _ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
        (DerivativePowerEnvelope.nonneg (k + 1) (Nat.cast_nonneg _) hℓ.le hA0)]

end
end RiemannGaussian.DerivativePowerStep
