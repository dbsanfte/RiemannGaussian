/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DerivativePowerStep
import RiemannGaussian.HigherDerivativeTest

/-!
# A uniform closed power bound at every derivative order

One analytic ceiling rule bounds the full finite derivative recurrence by
two explicit real powers with coefficient thirty-two independent of order.
The empty-cap, large-scale and long-shift cases use their proved trivial
fallbacks; the remaining case uses the complete weighted lag estimates.
The resulting theorem applies directly to genuine real derivative families.
-/

namespace RiemannGaussian.UniformDerivativePowerBound
noncomputable section
open DerivativePowerExponents AnalyticDerivativeCutoff DerivativeRecursionBudget
open DerivativePowerEnvelope PhaseIncrementInverse
open scoped Classical

/-- The entire finite recurrence has one closed power envelope with
coefficient thirty-two at every order and every positive scale. -/
theorem budget_bound (k L : ℕ) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) :
    budget cutoffs k L ℓ A ≤ envelope k L ℓ A := by
  have hA0 : 0 ≤ A := by linarith
  by_cases hL : L = 0
  · subst L
    have hz := le_length cutoffs k 0 ℓ A
    simp only [Nat.cast_zero] at hz ⊢
    exact hz.trans (DerivativePowerEnvelope.nonneg k (by norm_num : (0 : ℝ) ≤ 0) hℓ.le hA0)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hL
  induction k generalizing ℓ with
  | zero => exact base_bound cutoffs L hℓ hA
  | succ k ih =>
    have hm := main_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le hA0
    have he := error_nonneg (k + 1) (Nat.cast_nonneg (α := ℝ) L) hℓ.le
    by_cases hlarge : 1 ≤ ℓ
    · have hmain := main_ge_length (k + 1) (Nat.cast_nonneg (α := ℝ) L) hlarge hA
      apply (le_length cutoffs (k + 1) L ℓ A).trans
      unfold envelope
      nlinarith
    have hsmall : ℓ ≤ 1 := le_of_lt (lt_of_not_ge hlarge)
    by_cases hH : shiftCount cutoffs k L ℓ A ≤ L
    · apply DerivativePowerStep.successor_bound k L hℓ hsmall hA hH
      intro j _
      exact ih (by positivity : 0 < ((j : ℝ) + 1) * ℓ)
    · have hLu := length_lt_ideal k L hℓ A (by omega)
      have herror := error_ge_length k hLr hℓ hLu.le
      apply (le_length cutoffs (k + 1) L ℓ A).trans
      unfold envelope
      nlinarith

/-- A real phase with a genuine derivative family through order `k+2`
has the uniform two-term power bound on every finite original block. -/
theorem phase_bound (k L : ℕ) (F : ℕ → ℝ → ℝ) (a : ℝ) (N : ℕ)
    {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A) (hNL : N ≤ L)
    (hd : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F r) (F (r + 1) x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ F (k + 2) x ∧ F (k + 2) x ≤ A * ℓ) :
    ‖∑ n ∈ Finset.range N, rotation (F 0 (a + n))‖ ≤
      32 * (A ^ amp k * L * ℓ ^ alpha k + (L : ℝ) ^ beta k * ℓ ^ (-alpha k)) :=
  (HigherDerivativeTest.bound cutoffs k L F a N hℓ (by linarith) hNL hd hr).trans
    (budget_bound k L hℓ hA)

end
end RiemannGaussian.UniformDerivativePowerBound
