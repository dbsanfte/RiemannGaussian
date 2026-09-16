/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleCore

/-!
# A quantitative saving from every successful exact cycle

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszCycleSaving
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore

/-- Every positive cycle exhausts at least one original amplitude. -/
theorem cycleScale_exhausts {z w v : ℂ} (h : positiveCycle z w v) :
    cycleScale z w v * area w v = 1 ∨
    cycleScale z w v * area v z = 1 ∨
    cycleScale z w v * area z w = 1 := by
  rw [cycleScale, if_pos h]
  rcases le_total (area w v) (max (area v z) (area z w)) with hm | hm
  · rw [max_eq_right hm]
    rcases le_total (area v z) (area z w) with ha | ha
    · rw [max_eq_right ha]
      exact Or.inr (Or.inr (inv_mul_cancel₀ h.2.2.ne'))
    · rw [max_eq_left ha]
      exact Or.inr (Or.inl (inv_mul_cancel₀ h.2.1.ne'))
  · rw [max_eq_left hm]
    exact Or.inl (inv_mul_cancel₀ h.1.ne')

/-- The norm of each exactly cancelling part is no larger than the
combined norm of the other two parts. -/
theorem twice_norm_le_zero_cycle_mass (z w v : ℂ) (h : z + w + v = 0) :
    2 * ‖z‖ ≤ ‖z‖ + ‖w‖ + ‖v‖ := by
  have he : z = -(w + v) := by linear_combination h
  have hn : ‖z‖ ≤ ‖w‖ + ‖v‖ := by rw [he, norm_neg]; exact norm_add_le _ _
  linarith

/-- The exact cycle saving is the sum of the three supported removed
norms, with all signs justified by the deterministic scale. -/
theorem cycleSaving_eq_sent_norms (z w v : ℂ) :
    cycleSaving z w v =
      ‖(cycleScale z w v * area w v) • z‖ +
      ‖(cycleScale z w v * area v z) • w‖ +
      ‖(cycleScale z w v * area z w) • v‖ := by
  obtain ⟨ha, _, hb, _, hc, _⟩ := cycleScale_bounds z w v
  rw [norm_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, Real.norm_of_nonneg hc]
  unfold cycleSaving
  ring

/-- Every successful actual cycle saves at least twice the smallest
available amplitude, independent of the phase-gap size. -/
theorem twice_min_norm_le_cycleSaving {z w v : ℂ} (h : positiveCycle z w v) :
    2 * min ‖z‖ (min ‖w‖ ‖v‖) ≤ cycleSaving z w v := by
  have hz := sent_cycle_eq_zero z w v
  have hleft := twice_norm_le_zero_cycle_mass _ _ _ hz
  have hmid := twice_norm_le_zero_cycle_mass
    ((cycleScale z w v * area v z) • w)
    ((cycleScale z w v * area w v) • z)
    ((cycleScale z w v * area z w) • v) (by linear_combination hz)
  have hright := twice_norm_le_zero_cycle_mass
    ((cycleScale z w v * area z w) • v)
    ((cycleScale z w v * area w v) • z)
    ((cycleScale z w v * area v z) • w) (by linear_combination hz)
  have hminz : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖z‖ := min_le_left _ _
  have hminw : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖w‖ := (min_le_right _ _).trans (min_le_left _ _)
  have hminv : min ‖z‖ (min ‖w‖ ‖v‖) ≤ ‖v‖ := (min_le_right _ _).trans (min_le_right _ _)
  rw [cycleSaving_eq_sent_norms]
  rcases cycleScale_exhausts h with he | he | he
  · rw [he, one_smul] at hleft ⊢
    linarith
  · rw [he, one_smul] at hmid ⊢
    linarith
  · rw [he, one_smul] at hright ⊢
    linarith


end
end RiemannGaussian.ZetaRieszCycleSaving
