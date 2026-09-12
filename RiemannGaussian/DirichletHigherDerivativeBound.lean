/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.HigherLogarithmicDerivativeBound
import RiemannGaussian.DirichletSecondDerivativeBound

/-!
# Complete Dirichlet bounds at every derivative order

The same recursive budget controls every partial sum, so exact Abel
summation retains the full real Dirichlet damping at every derivative
order. The terminal theorem is over the literal finite complex terms,
for every cutoff rule and every positive height and dyadic scale. Small
curvature or resonance avoidance is not assumed; the recurrence uses
its proved trivial fallback wherever its base test is inadmissible.

The budget still needs uniform analytic simplification to the estimates
used by a larger zero-free region. Additional prime, sieve and moment
weights require independent variation or correlation bounds.
-/

namespace RiemannGaussian.DirichletHigherDerivativeBound
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase LogarithmicDerivativeFamily
open DerivativeRecursionBudget
open scoped Classical

/-- The full damping preserves the every-order recursive bound for
every cutoff rule, using the same cap on all original partial sums. -/
theorem damped_bound (κ : Cutoffs) (k : ℕ) {σ t X a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N,
      (Real.exp (-σ * Real.log (a + n)) : ℂ) * rotation (phase t (a + n))‖ ≤
        budget κ k N (lowerScale t X k) (ratio k) *
          Real.exp (-σ * Real.log a) := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (DerivativeRecursionBudget.nonneg κ k 0 _ (ratio_pos k).le)
      (Real.exp_pos _).le
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ Real.exp (-σ * Real.log (a + n)) :=
      fun _ _ ↦ (Real.exp_pos _).le
    have hm : AntitoneOn (fun n : ℕ ↦ Real.exp (-σ * Real.log (a + n)))
        (Set.Icc 0 N) := by
      intro i _ j _ hij
      apply DirichletSecondDerivativeBound.damping_antitoneOn hσ
      · change 0 < a + (i : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) i]
      · change 0 < a + (j : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      · have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ Finset.range (n + 1), rotation (phase t (a + k))‖ ≤
          budget κ k (N + 1) (lowerScale t X k) (ratio k) := by
      have hb' : a + (n + 1 : ℕ) ≤ 2 * X := by
        have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
        push_cast at hb ⊢
        linarith
      exact HigherLogarithmicDerivativeBound.bound κ k (N + 1) ht hX ha (n + 1)
        (by omega) hb'
    simpa only [Nat.cast_zero, add_zero, Nat.succ_eq_add_one] using
      FiniteAbelVariation.decreasing_bound (fun n ↦ Real.exp (-σ * Real.log (a + n)))
        (fun n ↦ rotation (phase t (a + n))) N hw hm hp

/-- The original complex Dirichlet sum satisfies the proved recursive
bound at every derivative order and for every adaptive cutoff rule. -/
theorem feature_bound (κ : Cutoffs) (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ))
    (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      budget κ k N (lowerScale s.im X k) (ratio k) *
          zetaPrimeExpWeight s.re a := by
  simpa only [ZetaFiniteDifferencing.feature_polar, zetaPrimeExpWeight, Nat.cast_add,
    PhaseIncrementInverse.rotation] using damped_bound κ k hσ ht hX ha N hb

end
end RiemannGaussian.DirichletHigherDerivativeBound
