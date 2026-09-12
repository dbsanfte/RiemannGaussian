/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteKuzminLandau

/-!
# Finite Abel transport with the exact amplitude variation

A bound on every original complex partial sum transports to arbitrary
complex weights at the explicit cost of the final weight and its total
variation. For nonnegative decreasing real weights this cost telescopes
to the initial weight. The signed endpoint identity is retained before
the estimate. No regularity of a prime or sieve weight is assumed.
-/

namespace RiemannGaussian.FiniteAbelVariation
noncomputable section
open scoped Classical

/-- Exact weighted summation through the original complex partial sums. -/
theorem weighted_sum_eq (w z : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * z n) =
      w N * (∑ n ∈ Finset.range (N + 1), z n) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), z k) := by
  have h := FiniteKuzminLandau.summation_by_parts w
    (fun n ↦ ∑ k ∈ Finset.range n, z k) N
  simpa only [Finset.sum_range_succ, add_sub_cancel_left, Finset.range_zero,
    Finset.sum_empty, mul_zero, sub_zero] using h

/-- Every complex amplitude pays its exact finite variation budget;
the original partial sums are bounded before any amplitude information
is discarded. -/
theorem weighted_bound (w z : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : ∀ n ≤ N, ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ B) :
    ‖∑ n ∈ Finset.range (N + 1), w n * z n‖ ≤
      B * (‖w N‖ + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖) := by
  rw [weighted_sum_eq]
  calc
    _ ≤ ‖w N * (∑ n ∈ Finset.range (N + 1), z n)‖ +
        ‖∑ n ∈ Finset.range N, (w n - w (n + 1)) *
          (∑ k ∈ Finset.range (n + 1), z k)‖ := norm_add_le _ _
    _ ≤ ‖w N‖ * B + ∑ n ∈ Finset.range N, ‖w n - w (n + 1)‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB n (by have := Finset.mem_range.mp hn; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- For nonnegative decreasing real weights, the complete variation
budget is exactly the initial amplitude. -/
theorem decreasing_budget (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N)) :
    ‖(w N : ℂ)‖ + (∑ n ∈ Finset.range N, ‖(w n : ℂ) - (w (n + 1) : ℂ)‖) = w 0 := by
  have hs : (∑ n ∈ Finset.range N, ‖(w n : ℂ) - (w (n + 1) : ℂ)‖) = w 0 - w N := by
    rw [← Finset.sum_range_sub' w N]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact sub_nonneg.mpr (hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N le_rfl)]
  ring

/-- A partial-sum cancellation bound survives every nonnegative
decreasing real amplitude with only its initial weight as cost. -/
theorem decreasing_bound (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N))
    (hB : ∀ n ≤ N, ‖∑ k ∈ Finset.range (n + 1), z k‖ ≤ B) :
    ‖∑ n ∈ Finset.range (N + 1), (w n : ℂ) * z n‖ ≤ B * w 0 := by
  have h := weighted_bound (fun n ↦ (w n : ℂ)) z N hB
  rwa [decreasing_budget w N hw hm] at h

end
end RiemannGaussian.FiniteAbelVariation
