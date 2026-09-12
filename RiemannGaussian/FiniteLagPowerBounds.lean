/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Uniform finite power sums for the derivative recurrence

Positive and negative powers of each actual positive lag are summed
before bounding the complete triangular form. The negative-power estimate
keeps its integrable singular scale and has a constant uniform for
exponents between zero and one half. Empty sums are included explicitly.
-/

namespace RiemannGaussian.FiniteLagPowerBounds
noncomputable section
open scoped Classical

/-- Every positive power of a lag is bounded by its endpoint value,
yielding the complete finite sum bound including the empty case. -/
theorem positive_sum (H : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ α) ≤ (H : ℝ) * (H : ℝ) ^ α := by
  calc
    _ ≤ ∑ _j ∈ Finset.range H, (H : ℝ) ^ α := by
      apply Finset.sum_le_sum
      intro j hj
      have hjH : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact Real.rpow_le_rpow (by positivity) hjH hα
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The decreasing lag power has an explicit integral bound, with the
first term and the finite endpoint accounted for. -/
theorem negative_sum_integral (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α)) ≤
      (H : ℝ) ^ (1 - α) / (1 - α) := by
  cases H with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      Real.zero_rpow (by linarith : 1 - α ≠ 0), zero_div, le_refl]
  | succ H =>
    have hm : AntitoneOn (fun x : ℝ ↦ x ^ (-α)) (Set.Icc 1 (1 + H)) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hs := hm.sum_le_integral
    rw [integral_rpow (Or.inl (by linarith : -1 < -α))] at hs
    have he : (∑ j ∈ Finset.range (H + 1), ((j : ℝ) + 1) ^ (-α)) =
        (∑ j ∈ Finset.range H, (1 + ((j + 1 : ℕ) : ℝ)) ^ (-α)) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, Real.one_rpow]
      congr 2
      funext j
      congr 1
      ring
    rw [he]
    have heq : -α + 1 = 1 - α := by ring
    rw [heq, Real.one_rpow] at hs
    have hden : 0 < 1 - α := by linarith
    calc
      _ ≤ ((1 + (H : ℝ)) ^ (1 - α) - 1) / (1 - α) + 1 := by linarith
      _ ≤ (1 + (H : ℝ)) ^ (1 - α) / (1 - α) := by
        apply (le_div_iff₀ hden).mpr
        field_simp
        nlinarith
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, add_comm (H : ℝ) 1]

/-- Exponents through one half have a uniform constant two in the
full negative-power sum, independent of the number of lags. -/
theorem negative_sum (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hαh : α ≤ 1 / 2) :
    (∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α)) ≤
      2 * (H : ℝ) * (H : ℝ) ^ (-α) := by
  by_cases hH : H = 0
  · subst H
    simp
  have hHp : 0 < (H : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hH
  apply (negative_sum_integral H hα (by linarith)).trans
  have he : (H : ℝ) ^ (1 - α) = (H : ℝ) * (H : ℝ) ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hHp, Real.rpow_one]
  rw [he]
  apply (div_le_iff₀ (by linarith : 0 < 1 - α)).mpr
  have hp : 0 ≤ (H : ℝ) * (H : ℝ) ^ (-α) := by positivity
  nlinarith [mul_nonneg hp (show 0 ≤ 1 - 2 * α by linarith)]

/-- The entire positive-power triangular lag sum keeps its scale
`H^2*H^alpha`, with the original nonnegative weights included. -/
theorem weighted_positive (H : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ α) ≤
      (H : ℝ) ^ 2 * (H : ℝ) ^ α := by
  calc
    _ ≤ ∑ j ∈ Finset.range H, (H : ℝ) * ((j : ℝ) + 1) ^ α := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) j])
        (Real.rpow_nonneg (by positivity) _)
    _ = (H : ℝ) * ∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ α := (Finset.mul_sum _ _ _).symm
    _ ≤ (H : ℝ) * ((H : ℝ) * (H : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left (positive_sum H hα) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The entire negative-power triangular lag sum has one uniform
constant two for every exponent through one half. -/
theorem weighted_negative (H : ℕ) {α : ℝ} (hα : 0 ≤ α) (hαh : α ≤ 1 / 2) :
    (∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * ((j : ℝ) + 1) ^ (-α)) ≤
      2 * (H : ℝ) ^ 2 * (H : ℝ) ^ (-α) := by
  calc
    _ ≤ ∑ j ∈ Finset.range H, (H : ℝ) * ((j : ℝ) + 1) ^ (-α) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) j])
        (Real.rpow_nonneg (by positivity) _)
    _ = (H : ℝ) * ∑ j ∈ Finset.range H, ((j : ℝ) + 1) ^ (-α) := (Finset.mul_sum _ _ _).symm
    _ ≤ (H : ℝ) * (2 * (H : ℝ) * (H : ℝ) ^ (-α)) :=
      mul_le_mul_of_nonneg_left (negative_sum H hα hαh) (Nat.cast_nonneg _)
    _ = _ := by ring

end
end RiemannGaussian.FiniteLagPowerBounds
