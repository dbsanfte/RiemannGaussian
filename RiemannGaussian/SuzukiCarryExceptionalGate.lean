/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryRealJet
import RiemannGaussian.SuzukiCarryPhaseScaleGate

/-!
# The reduced campaign source gate

The real-exponent jet is proved positive. Quartic proportionality is escaped
by two phase contrasts at two scales. The remaining common-zero complex jet
is explicit; neither its emptiness nor an arithmetic estimate is assumed.
-/

namespace RiemannGaussian.SuzukiCarryExceptionalGate
noncomputable section
open Complex Filter
open SuzukiCarryMellinJet SuzukiCarryMellinBranches SuzukiCarryMellinRate
open SuzukiCarryExceptionalPhase SuzukiCarryRealJet SuzukiCarryPhaseScaleGate
open scoped Topology

/-- Exact classification of the quartic equation, now without any premise
on the real coefficient denominator. The first branch is a common-zero
complex jet; the second is equality to the real beta ratio. -/
theorem exceptional_iff_ratio_or_zero_jet {beta : ℝ} (hb : 15/16 ≤ beta) (y : ℝ) :
    exceptional beta y ↔
      (B (SuzukiCarryPoleCenter.poleExponent y) = 0 ∧
        C (SuzukiCarryPoleCenter.poleExponent y) = 0) ∨
      (B (SuzukiCarryPoleCenter.poleExponent y) ≠ 0 ∧
        (C (SuzukiCarryPoleCenter.poleExponent y)/
          B (SuzukiCarryPoleCenter.poleExponent y)).im = 0 ∧
        (C (SuzukiCarryPoleCenter.poleExponent y)/
          B (SuzukiCarryPoleCenter.poleExponent y)).re =
            (C (beta : ℂ)).re/(B (beta : ℂ)).re) := by
  have hb0 : 0 < beta := by linarith
  have hbb := B_ofReal_ne_zero hb
  rw [exceptional_iff_wedge_zero hb0 y]
  by_cases hp : B (SuzukiCarryPoleCenter.poleExponent y) = 0
  · simp [hp,hbb]
  · rw [wedge_zero_iff_ratio hp hbb]
    simp only [hp,false_and,false_or]
    rw [Complex.ext_iff]
    simp only [Complex.ofReal_re,Complex.ofReal_im]
    constructor
    · rintro ⟨hr,hi⟩
      exact ⟨hp,hi,hr⟩
    · rintro ⟨_,hi,hr⟩
      exact ⟨hr,hi⟩

/-- At every campaign height a nonzero complex jet suffices for a fixed
four-response code and a cofinal native source lower bound. No nonzero
wedge premise and no real-jet nonvanishing premise remain. -/
theorem exists_fixed_campaign_code {beta : ℝ} (hb : 19999/20000 ≤ beta)
    (hb1 : beta < 1) (y : ℝ)
    (hj : B (SuzukiCarryPoleCenter.poleExponent y) ≠ 0 ∨
      C (SuzukiCarryPoleCenter.poleExponent y) ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧
      scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeScaleDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖ := by
  have hb' : 15/16 ≤ beta := by linarith
  have hre : (SuzukiCarryPoleCenter.poleExponent y).re ≠ (beta : ℂ).re := by
    rw [SuzukiCarryPoleCenter.poleExponent_re,Complex.ofReal_re]
    exact ne_of_gt hb1
  simpa only [SuzukiCarryPoleCenter.poleExponent_re,Complex.ofReal_re] using
    exists_fixed_scale_code_of_nonzero_jets
      (by rw [SuzukiCarryPoleCenter.poleExponent_re]; norm_num)
      (by simp only [Complex.ofReal_re]; linarith) hre hj
      (Or.inl (B_ofReal_ne_zero hb'))

/-- This exhaustive alternative records exactly what is still unproved
by the present jet-based gate, rather than asserting universal closure. -/
theorem campaign_code_or_zero_jet {beta : ℝ} (hb : 19999/20000 ≤ beta)
    (hb1 : beta < 1) (y : ℝ) :
    (B (SuzukiCarryPoleCenter.poleExponent y) = 0 ∧
      C (SuzukiCarryPoleCenter.poleExponent y) = 0) ∨
    (∃ tau : ℝ, 0 < tau ∧
      scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeScaleDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖) := by
  by_cases hj : B (SuzukiCarryPoleCenter.poleExponent y) ≠ 0 ∨
      C (SuzukiCarryPoleCenter.poleExponent y) ≠ 0
  · exact Or.inr (exists_fixed_campaign_code hb hb1 y hj)
  · exact Or.inl (by simpa only [not_or,not_not] using hj)

end
end RiemannGaussian.SuzukiCarryExceptionalGate
