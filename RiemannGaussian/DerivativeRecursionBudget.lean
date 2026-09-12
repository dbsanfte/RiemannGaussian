/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SecondDerivativeTest

/-!
# Explicit finite budgets for every derivative order

The base budget is the proved second-derivative estimate, with the trivial
length bound as fallback outside its admissible curvature range. Every
successor is the finite van der Corput expression using all lower-order
shifted budgets. A common length cap is retained, so the same budget will
bound every original partial sum and can pass through exact Abel summation.

The cutoff rule is arbitrary and may depend on order, length, curvature
and curvature ratio. Its value plus one is the positive shift count.
No numerical choice or unproved cancellation input defines these budgets.
Their connection to real derivative families is proved downstream.
-/

namespace RiemannGaussian.DerivativeRecursionBudget
noncomputable section
open scoped Classical

/-- Any rule for the number of additional translates at each recursive
order, length cap, lower curvature and curvature ratio. -/
abbrev Cutoffs := ℕ → ℕ → ℝ → ℝ → ℕ

/-- At least the original translate is included for every cutoff rule. -/
def shiftCount (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) : ℕ := κ k L ℓ A + 1

/-- Every selected shift count is positive without restricting the rule. -/
theorem shiftCount_pos (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    0 < shiftCount κ k L ℓ A := Nat.zero_lt_succ _

/-- A finite recursive envelope, starting with second derivatives at
order zero. Every positive lag retains its own scaled curvature. -/
def budget (κ : Cutoffs) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, L, ℓ, A =>
      if 0 < ℓ ∧ ℓ ≤ 1 then
        min (L : ℝ) ((A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
          (3 + 2 * Real.pi))
      else L
  | k + 1, L, ℓ, A =>
      let H := shiftCount κ k L ℓ A
      min (L : ℝ) (Real.sqrt ((((L : ℝ) + H - 1) * ((H : ℝ) * L +
        2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
          budget κ k L (((j : ℝ) + 1) * ℓ) A)) / (H : ℝ) ^ 2))

/-- All recursive envelopes are nonnegative for nonnegative curvature
ratio; empty overlaps can therefore use the same budget. -/
theorem nonneg (κ : Cutoffs) (k L : ℕ) (ℓ : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ budget κ k L ℓ A := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs with h
    · apply le_min (Nat.cast_nonneg _)
      have hℓ := h.1
      positivity
    · positivity
  | succ k =>
    rw [budget]
    exact le_min (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

/-- No recursive choice makes the estimate worse than the trivial
length cap, even outside the square-root base regime. -/
theorem le_length (κ : Cutoffs) (k L : ℕ) (ℓ A : ℝ) :
    budget κ k L ℓ A ≤ L := by
  cases k with
  | zero =>
    rw [budget]
    split_ifs
    · exact min_le_left _ _
    · rfl
  | succ k =>
    rw [budget]
    exact min_le_left _ _

/-- For a genuine curvature ratio at least one, the square-root envelope
also dominates the trivial fallback. Thus the analytic base bound is
valid at every positive curvature, with no omitted large-curvature case. -/
theorem base_le (κ : Cutoffs) (L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget κ 0 L ℓ A ≤
      (A * L * Real.sqrt ℓ / (2 * Real.pi) + 2 / Real.sqrt ℓ) *
        (3 + 2 * Real.pi) := by
  rw [budget]
  by_cases hℓ1 : ℓ ≤ 1
  · rw [if_pos ⟨hℓ, hℓ1⟩]
    exact min_le_right _ _
  · rw [if_neg (fun h ↦ hℓ1 h.2)]
    have hs1 : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.mpr (by linarith)
    have hA0 : 0 ≤ A := by linarith
    have hL : (L : ℝ) ≤ A * L := by nlinarith [Nat.cast_nonneg (α := ℝ) L]
    have hp := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hA0 (Nat.cast_nonneg (α := ℝ) L))
    simp only [mul_one] at hp
    calc
      _ ≤ A * L * Real.sqrt ℓ := hL.trans hp
      _ = (A * L * Real.sqrt ℓ / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul
        · exact le_add_of_nonneg_right (by positivity)
        · linarith
        · positivity
        · positivity

end
end RiemannGaussian.DerivativeRecursionBudget
