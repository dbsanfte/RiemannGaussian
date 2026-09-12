/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteVanDerCorputPhase
import RiemannGaussian.PhaseIncrementInverse

/-!
# Finite differencing on the original natural offsets

The integer zero-extension inequality is transported to natural offsets
without changing any overlap. A lag `h` has exactly `N-h` terms, including
the empty overlap when the lag passes the original cutoff. This form is
used by induction on the derivative order of a real phase.
-/

namespace RiemannGaussian.NatPhaseDifferencing
noncomputable section
open PhaseIncrementInverse FiniteVanDerCorputPhase
open scoped Classical

/-- A zero-based integer interval is exactly its natural-offset sum. -/
theorem sum_Ico_zero (N : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico 0 (N : ℤ), f n) = ∑ n ∈ Finset.range N, f n := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp

/-- Each literal integer overlap becomes the original truncated natural
overlap, including every empty large-lag case. -/
theorem overlap_eq (φ : ℕ → ℝ) (N h : ℕ) :
    (∑ n ∈ Finset.Ico 0 ((N : ℤ) - h),
      rotation (φ (n + h).toNat - φ n.toNat)) =
        ∑ n ∈ Finset.range (N - h), rotation (φ (n + h) - φ n) := by
  by_cases hh : h ≤ N
  · rw [show (N : ℤ) - h = ((N - h : ℕ) : ℤ) by omega, sum_Ico_zero]
    apply Finset.sum_congr rfl
    intro n _
    simp only [← Int.natCast_add, Int.toNat_natCast]
  · rw [Finset.Ico_eq_empty (by omega), Nat.sub_eq_zero_of_le (by omega),
      Finset.range_zero, Finset.sum_empty, Finset.sum_empty]

/-- The norm of every original phase sum has the trivial length bound,
available as a fallback at each derivative order. -/
theorem trivial_bound (φ : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ≤ N := by
  simpa only [norm_rotation, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    using norm_sum_le (Finset.range N) (fun n ↦ rotation (φ n))

/-- The full van der Corput inequality on natural offsets retains every
lag weight and the exact length of its original phase-difference sum. -/
theorem bound (φ : ℕ → ℝ) (N : ℕ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, rotation (φ n)‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * N +
        2 * ∑ k ∈ Finset.range H, ((H : ℝ) - k - 1) *
          ‖∑ n ∈ Finset.range (N - (k + 1)), rotation (φ (n + (k + 1)) - φ n)‖) := by
  have hv := unit_phase_bound 0 N (fun n : ℤ ↦ φ n.toNat) hH
  simp only [zero_add, sum_Ico_zero,
    Int.toNat_natCast] at hv
  have he (k : ℕ) : (∑ n ∈ Finset.Ico 0 ((N : ℤ) - ((k : ℤ) + 1)),
      rotation (φ (n + ((k : ℤ) + 1)).toNat - φ n.toNat)) =
        ∑ n ∈ Finset.range (N - (k + 1)), rotation (φ (n + (k + 1)) - φ n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using overlap_eq φ N (k + 1)
  simp only [PhaseIncrementInverse.rotation] at he
  simpa only [he, PhaseIncrementInverse.rotation] using hv

end
end RiemannGaussian.NatPhaseDifferencing
