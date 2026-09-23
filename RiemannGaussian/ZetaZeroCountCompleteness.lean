/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFiniteZeroCount

/-!
# Matching verified zeros against the complete count

A finite list cannot miss any zero if its distinct members lie in the
window and already exhaust the total multiplicity count. Positivity of
every actual analytic multiplicity proves the criterion without assuming
that unseen zeros are simple or lie on the critical line.
-/

namespace RiemannGaussian.ZetaZeroCountCompleteness
noncomputable section
open ZetaFiniteZeroCount

/-- Each distinct nontrivial zero contributes at least one to the actual
complete multiplicity count. -/
theorem card_window_le_count (T : ℝ) : (spectralZetaZeroWindow T).card ≤ count T := by
  calc
    _ = ∑ _ρ ∈ spectralZetaZeroWindow T, (1 : ℕ) := by simp
    _ ≤ count T := Finset.sum_le_sum fun ρ _ => analyticZetaZeroMultiplicity_positive ρ

/-- A verified finite set exhausting the complete count is the entire
zero window. The zero-list membership and cardinality comparison must both
be proved; neither is built into the criterion as numerical data. -/
theorem window_eq_of_count_le_card {T : ℝ} (hT : 0 ≤ T) (S : Finset NontrivialZetaZero)
    (hs : ∀ ρ ∈ S, |ρ.1.im| ≤ T) (hc : count T ≤ S.card) : spectralZetaZeroWindow T = S := by
  have hsub : S ⊆ spectralZetaZeroWindow T := by
    intro ρ hρ
    apply (mem_spectralZetaZeroWindow hT ρ).mpr
    simpa only [zetaSpectralCoordinate_re] using hs ρ hρ
  exact (Finset.eq_of_subset_of_card_le hsub ((card_window_le_count T).trans hc)).symm

/-- A complete count matched by verified critical-line zeros proves RH
through that finite height, including both signs of the ordinate. -/
theorem critical_line_of_count_le_card {T : ℝ} (hT : 0 ≤ T) (S : Finset NontrivialZetaZero)
    (hs : ∀ ρ ∈ S, |ρ.1.im| ≤ T) (hc : count T ≤ S.card)
    (hl : ∀ ρ ∈ S, ρ.1.re = 1 / 2) (ρ : NontrivialZetaZero) (hρ : |ρ.1.im| ≤ T) :
    ρ.1.re = 1 / 2 := by
  apply hl ρ
  rw [← window_eq_of_count_le_card hT S hs hc]
  apply (mem_spectralZetaZeroWindow hT ρ).mpr
  simpa only [zetaSpectralCoordinate_re] using hρ

end
end RiemannGaussian.ZetaZeroCountCompleteness
