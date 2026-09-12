/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteKuzminLandau
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A first-derivative exponential-sum test with explicit domain conditions

The mean value theorem places every discrete phase increment at a genuine
point of its original unit interval. A monotone or antitone derivative
therefore gives ordered increments, with the same nonresonance bounds.
The finite Kuzmin--Landau theorem yields `2*pi/eta` independently of the
number of terms. Both block endpoints remain in the derivative domain.

Angles are measured in radians. The derivative stays in one interval
`[eta,2*pi-eta]`; no modulo-period crossing or resonant interval is omitted.
This is the classical first-derivative estimate with a coarse constant.
-/

namespace RiemannGaussian.FirstDerivativeTest
noncomputable section
open FiniteKuzminLandau PhaseIncrementInverse
open scoped Classical

/-- Every discrete increment equals the derivative at a point in its
actual unit interval; the interval order remains available downstream. -/
theorem increment_witness (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ)
    (hd : ∀ x ∈ Set.Icc a (a + N + 1), HasDerivAt f (f' x) x)
    {n : ℕ} (hn : n ≤ N) :
    ∃ x ∈ Set.Ioo (a + n) (a + n + 1),
      f' x = increment (fun k ↦ f (a + k)) n := by
  have hsub : Set.Icc (a + n) (a + n + 1) ⊆ Set.Icc a (a + N + 1) := by
    intro x hx
    have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
    constructor <;> linarith [hx.1, hx.2, Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f'
    (show a + (n : ℝ) < a + n + 1 by linarith)
    (fun y hy ↦ (hd y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy ↦ hd y (hsub (Set.Ioo_subset_Icc_self hy)))
  refine ⟨x, hx, ?_⟩
  rw [show a + (n : ℝ) + 1 - (a + n) = 1 by ring, div_one] at he
  simpa only [increment, Nat.cast_add, Nat.cast_one, add_assoc] using he

/-- The first-derivative test on a nonempty finite block. All phase
increments inherit their order and nonresonance from the proved derivative. -/
theorem bound_succ (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ x ∈ Set.Icc a (a + N + 1), HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N + 1), f' x ∈ Set.Icc η (2 * Real.pi - η))
    (hm : MonotoneOn f' (Set.Icc a (a + N + 1)) ∨
      AntitoneOn f' (Set.Icc a (a + N + 1))) :
    ‖∑ n ∈ Finset.range (N + 1), rotation (f (a + n))‖ ≤ 2 * Real.pi / η := by
  have hsub {n : ℕ} (hn : n ≤ N) {x : ℝ}
      (hx : x ∈ Set.Ioo (a + n) (a + n + 1)) : x ∈ Set.Icc a (a + N + 1) := by
    have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
    constructor <;> linarith [hx.1, hx.2, Nat.cast_nonneg (α := ℝ) n]
  apply FiniteKuzminLandau.bound (fun n ↦ f (a + n)) N hη
  · intro n hn
    obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hn
    rw [← he]
    exact hr x (hsub hn hx)
  · have hord {i j : ℕ} (hij : i < j) {x y : ℝ}
        (hx : x ∈ Set.Ioo (a + i) (a + i + 1))
        (hy : y ∈ Set.Ioo (a + j) (a + j + 1)) : x ≤ y := by
      have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr hij
      linarith [hx.2, hy.1]
    rcases hm with hm | hm
    · left
      intro i hi j hj hij
      rcases hij.eq_or_lt with rfl | hij
      · rfl
      obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hi.2
      obtain ⟨y, hy, hf⟩ := increment_witness f f' a N hd hj.2
      rw [← he, ← hf]
      exact hm (hsub hi.2 hx) (hsub hj.2 hy) (hord hij hx hy)
    · right
      intro i hi j hj hij
      rcases hij.eq_or_lt with rfl | hij
      · rfl
      obtain ⟨x, hx, he⟩ := increment_witness f f' a N hd hi.2
      obtain ⟨y, hy, hf⟩ := increment_witness f f' a N hd hj.2
      rw [← he, ← hf]
      exact hm (hsub hi.2 hx) (hsub hj.2 hy) (hord hij hx hy)

/-- The classical first-derivative cancellation estimate on every finite
block, including the empty block, with its actual closed derivative domain. -/
theorem bound (f f' : ℝ → ℝ) (a : ℝ) (N : ℕ) {η : ℝ} (hη : 0 < η)
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), f' x ∈ Set.Icc η (2 * Real.pi - η))
    (hm : MonotoneOn f' (Set.Icc a (a + N)) ∨ AntitoneOn f' (Set.Icc a (a + N))) :
    ‖∑ n ∈ Finset.range N, rotation (f (a + n))‖ ≤ 2 * Real.pi / η := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  | succ N =>
    apply bound_succ f f' a N hη
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hd
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hr
    · simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using hm

end
end RiemannGaussian.FirstDerivativeTest
