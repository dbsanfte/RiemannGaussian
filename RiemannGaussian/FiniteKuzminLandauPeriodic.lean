/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteKuzminLandau
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact integer winding and nonresonant finite blocks

Subtracting an integer winding from each discrete phase leaves every
original complex summand unchanged. Its increments move into the basic
nonresonant interval, so the proved Kuzmin--Landau estimate applies between
any two adjacent resonances. The interval version retains both finite
endpoints, including the phase at the auxiliary final endpoint.
-/

namespace RiemannGaussian.FiniteKuzminLandauPeriodic
noncomputable section
open PhaseIncrementInverse FiniteKuzminLandau
open scoped Classical

/-- Integer winding preserves the full complex rotation, not merely
its norm or real part. -/
theorem rotation_int_period (x : ℝ) (m : ℤ) :
    rotation (x + (m : ℝ) * (2 * Real.pi)) = rotation x := by
  rw [rotation_add]
  have he : rotation ((m : ℝ) * (2 * Real.pi)) = 1 := by
    unfold PhaseIncrementInverse.rotation
    convert Complex.exp_int_mul_two_pi_mul_I m using 1
    push_cast
    congr 1
    ring
  rw [he, mul_one]

/-- A discrete phase with the chosen integer winding removed exactly. -/
def twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) : ℝ :=
  φ n - (m : ℝ) * (2 * Real.pi) * n

/-- Every original complex term is unchanged by the integer twist. -/
theorem rotation_twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) :
    rotation (twist φ m n) = rotation (φ n) := by
  have he : twist φ m n = φ n + (((-m * (n : ℤ) : ℤ) : ℝ)) * (2 * Real.pi) := by
    unfold twist
    push_cast
    ring
  rw [he, rotation_int_period]

/-- The twist subtracts exactly one integer multiple of the period
from each original increment. -/
theorem increment_twist (φ : ℕ → ℝ) (m : ℤ) (n : ℕ) :
    increment (twist φ m) n = increment φ n - (m : ℝ) * (2 * Real.pi) := by
  unfold increment twist
  push_cast
  ring

/-- Discrete cancellation holds between any two adjacent resonances,
with the complete complex summands unchanged by phase transport. -/
theorem bound_period (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ≤ N, increment φ n ∈ Set.Icc
      ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η))
    (hm : MonotoneOn (increment φ) (Set.Icc 0 N) ∨
      AntitoneOn (increment φ) (Set.Icc 0 N)) :
    ‖∑ n ∈ Finset.range (N + 1), rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  have hdr (n : ℕ) (hn : n ≤ N) :
      increment (twist φ m) n ∈ Set.Icc η (2 * Real.pi - η) := by
    rw [increment_twist]
    constructor <;> linarith [(hd n hn).1, (hd n hn).2]
  have hmr : MonotoneOn (increment (twist φ m)) (Set.Icc 0 N) ∨
      AntitoneOn (increment (twist φ m)) (Set.Icc 0 N) := by
    rcases hm with hm | hm
    · left
      intro i hi j hj hij
      simp only [increment_twist]
      exact sub_le_sub_right (hm hi hj hij) _
    · right
      intro i hi j hj hij
      simp only [increment_twist]
      exact sub_le_sub_right (hm hi hj hij) _
  simpa only [rotation_twist] using FiniteKuzminLandau.bound (twist φ m) N hη hdr hmr

/-- The nonresonant estimate on a literal finite interval of the
original sequence. Empty intervals require no phase assumptions. -/
theorem bound_Ico (φ : ℕ → ℝ) (a b : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ n ∈ Finset.Ico a b, increment φ n ∈ Set.Icc
      ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η))
    (hm : MonotoneOn (increment φ) (Set.Ico a b) ∨
      AntitoneOn (increment φ) (Set.Ico a b)) :
    ‖∑ n ∈ Finset.Ico a b, rotation (φ n)‖ ≤ 2 * Real.pi / η := by
  by_cases hab : a < b
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, b = a + (N + 1) := ⟨b - a - 1, by omega⟩
    have hi (n : ℕ) (hn : n ≤ N) : a + n ∈ Finset.Ico a (a + (N + 1)) := by
      simp only [Finset.mem_Ico]
      omega
    have hd' (n : ℕ) (hn : n ≤ N) : increment (fun k ↦ φ (a + k)) n ∈ Set.Icc
        ((m : ℝ) * (2 * Real.pi) + η) ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η) := by
      simpa only [increment, Nat.add_assoc] using hd (a + n) (hi n hn)
    have hm' : MonotoneOn (increment (fun k ↦ φ (a + k))) (Set.Icc 0 N) ∨
        AntitoneOn (increment (fun k ↦ φ (a + k))) (Set.Icc 0 N) := by
      rcases hm with hm | hm
      · left
        intro i hi' j hj' hij
        simpa only [increment, Nat.add_assoc] using
          hm (Finset.mem_Ico.mp (hi i hi'.2)) (Finset.mem_Ico.mp (hi j hj'.2))
            (Nat.add_le_add_left hij a)
      · right
        intro i hi' j hj' hij
        simpa only [increment, Nat.add_assoc] using
          hm (Finset.mem_Ico.mp (hi i hi'.2)) (Finset.mem_Ico.mp (hi j hj'.2))
            (Nat.add_le_add_left hij a)
    have h := bound_period (fun k ↦ φ (a + k)) N m hη hd' hm'
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel_left] using h
  · rw [Finset.Ico_eq_empty hab, Finset.sum_empty, norm_zero]
    positivity

end
end RiemannGaussian.FiniteKuzminLandauPeriodic
