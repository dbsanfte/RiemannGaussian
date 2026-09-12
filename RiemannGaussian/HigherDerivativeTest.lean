/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativeRecursionBudget
import RiemannGaussian.NatPhaseDifferencing
import RiemannGaussian.ShiftedDerivativeFamily

/-!
# Finite exponential-sum bounds at every derivative order

A genuine derivative family through order `k+2`, with positive two-sided
top derivative bounds on its original closed domain, satisfies the explicit
recursive budget for every cutoff rule. The induction uses complete
overlaps of length `N-h`, retaining the original derivative domain and the
exact scaled curvature `h*ell`. Empty large lags have zero correlation.

The length cap is independent of the particular prefix, making the same
bound available for exact downstream transport of decreasing amplitudes.
-/

namespace RiemannGaussian.HigherDerivativeTest
noncomputable section
open PhaseIncrementInverse DerivativeRecursionBudget ShiftedDerivativeFamily
open scoped Classical

/-- Every finite derivative order and every cutoff rule give a proved
bound on the actual phase sum, uniformly over all lengths below the cap. -/
theorem bound (κ : Cutoffs) (k L : ℕ) (F : ℕ → ℝ → ℝ) (a : ℝ) (N : ℕ)
    {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hNL : N ≤ L)
    (hd : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F r) (F (r + 1) x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ F (k + 2) x ∧ F (k + 2) x ≤ A * ℓ) :
    ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ≤ budget κ k L ℓ A := by
  induction k generalizing F a N ℓ with
  | zero =>
    have hNLr : (N : ℝ) ≤ L := by exact_mod_cast hNL
    have ht := (NatPhaseDifferencing.trivial_bound (fun n ↦ F 0 (a + n)) N).trans hNLr
    rw [budget]
    by_cases hℓ1 : ℓ ≤ 1
    · rw [if_pos ⟨hℓ, hℓ1⟩]
      apply le_min ht
      apply (SecondDerivativeTest.square_root_bound (F 0) (F 1) (F 2) a N hℓ hℓ1 hA
        (hd 0 (by omega)) (hd 1 (by omega)) hr).trans
      gcongr
    · rw [if_neg (fun h ↦ hℓ1 h.2)]
      exact ht
  | succ k ih =>
    have hNLr : (N : ℝ) ≤ L := by exact_mod_cast hNL
    have ht := (NatPhaseDifferencing.trivial_bound (fun n ↦ F 0 (a + n)) N).trans hNLr
    let H := shiftCount κ k L ℓ A
    have hH : 0 < H := shiftCount_pos κ k L ℓ A
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    let C (j : ℕ) := budget κ k L (((j : ℝ) + 1) * ℓ) A
    have hc (j : ℕ) :
        ‖∑ n ∈ Finset.range (N - (j + 1)),
          rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))‖ ≤ C j := by
      by_cases hj : j + 1 ≤ N
      · let G := difference F (j + 1 : ℕ)
        have hdG : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + (N - (j + 1) : ℕ)),
            HasDerivAt (G r) (G (r + 1) x) x :=
          derivative_family F a N (k + 2) (j + 1) hj (fun r hr ↦ hd r (by omega))
        have hrG := top_bounds F a N (k + 2) (j + 1) hj
          (hd (k + 2) (by omega)) hr
        have he : (∑ n ∈ Finset.range (N - (j + 1)),
            rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))) =
              ∑ n ∈ Finset.range (N - (j + 1)), rotation (G 0 (a + n)) := by
          apply Finset.sum_congr rfl
          intro n _
          simp only [G, difference, Nat.cast_add, Nat.cast_one, add_assoc]
        rw [he]
        have hi := ih G a (N - (j + 1)) (by positivity : 0 < (j + 1 : ℕ) * ℓ)
          (by omega) hdG hrG
        simpa only [C, Nat.cast_add, Nat.cast_one] using hi
      · rw [Nat.sub_eq_zero_of_le (by omega), Finset.range_zero, Finset.sum_empty, norm_zero]
        exact DerivativeRecursionBudget.nonneg κ k L _ hA
    let S := ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) * C j
    have hS : 0 ≤ S := by
      apply Finset.sum_nonneg
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact mul_nonneg (by linarith) (DerivativeRecursionBudget.nonneg κ k L _ hA)
    have hv := NatPhaseDifferencing.bound (fun n ↦ F 0 (a + n)) N hH
    have hinner : (H : ℝ) * N +
        2 * ∑ j ∈ Finset.range H, ((H : ℝ) - j - 1) *
          ‖∑ n ∈ Finset.range (N - (j + 1)),
            rotation (F 0 (a + (n + (j + 1) : ℕ)) - F 0 (a + n))‖ ≤
              (H : ℝ) * L + 2 * S := by
      apply add_le_add (mul_le_mul_of_nonneg_left hNLr (by positivity))
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro j hj
      have hjR : (j : ℝ) + 1 ≤ H := by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
      exact mul_le_mul_of_nonneg_left (hc j) (by linarith)
    have hu : (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ^ 2 ≤
        ((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * S) := by
      apply hv.trans
      exact (mul_le_mul_of_nonneg_left hinner
        (by linarith [Nat.cast_nonneg (α := ℝ) N])).trans
          (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have hHpos : 0 < (H : ℝ) ^ 2 := by positivity
    have hsq : ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ^ 2 ≤
        (((L : ℝ) + H - 1) * ((H : ℝ) * L + 2 * S)) / (H : ℝ) ^ 2 := by
      apply (le_div_iff₀ hHpos).mpr
      simpa only [mul_comm] using hu
    have hq := (sq_nonneg ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖).trans hsq
    rw [budget]
    apply le_min ht
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hq]
    exact hsq

end
end RiemannGaussian.HigherDerivativeTest
