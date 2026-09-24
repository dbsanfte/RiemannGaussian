/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHalfPlaneModes

/-!
# A sharp distinction between one successor and several rightward modes

One competing mode mixed with the selected zero has a quantitative
horizontal-gain/vertical-displacement bound. Two competing rightward
modes can cancel their ordinates while each remains outside the exposed
disk, inside the local radius, and arbitrarily little to the right.
The latter are synthetic coordinates, not asserted zeta zeros.
-/

namespace RiemannGaussian.ZetaRieszRightwardModeAudit
noncomputable section
open scoped BigOperators Classical
open ZetaRieszHalfPlaneModes ZetaRieszParityMaskedPhaseAudit

/-- A single actual successor mixed with the selected zero obeys the
desired displacement estimate, with its share explicitly retained. -/
theorem selected_successor_gain (rho tau : NontrivialZetaZero) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hres : ‖mix (direct rho tau) (direct rho rho) q‖ < sourceRadius rho) :
    rho.1.re < tau.1.re ∧
      q*((tau.1.im-rho.1.im)^2+(tau.1.re-rho.1.re)^2) <
        2*sourceRadius rho*(tau.1.re-rho.1.re) := by
  have hright : rho.1.re < tau.1.re := by
    by_contra! hn
    have h₁ : sourceRadius rho ≤ (direct rho tau).re := by
      rw [direct_re]
      dsimp [sourceRadius]
      linarith
    have h₂ : sourceRadius rho ≤ (direct rho rho).re := by rw [direct_self]; rfl
    have hh := (mix_re_ge h₁ h₂ hq0.le hq1).trans (Complex.re_le_norm _)
    exact (not_lt_of_ge hh) hres
  refine ⟨hright, ?_⟩
  have hu := sourceRadius_pos rho
  have hn := norm_nonneg (mix (direct rho tau) (direct rho rho) q)
  have hsq : ‖mix (direct rho tau) (direct rho rho) q‖^2 < (sourceRadius rho)^2 := by
    nlinarith
  have he := Complex.sq_norm_sub_sq_im (mix (direct rho tau) (direct rho rho) q)
  norm_num [mix, direct] at he
  simp only [mix, direct] at hsq
  dsimp [sourceRadius] at hsq ⊢
  have hh : q*(q*((tau.1.im-rho.1.im)^2+(tau.1.re-rho.1.re)^2)) <
      q*(2*(3/2-rho.1.re)*(tau.1.re-rho.1.re)) := by nlinarith [hsq, he]
  exact (mul_lt_mul_iff_right₀ hq0).mp hh

/-- First rightward test denominator, with variable horizontal gain. -/
def gainLeft (δ : ℝ) : ℂ := ((radius-δ : ℝ) : ℂ)+Complex.I/10

/-- Second denominator balances the exact retained endpoint share. -/
def gainRight (δ : ℝ) : ℂ := ((radius-δ : ℝ) : ℂ)-43*Complex.I/370

theorem gain_mix (δ : ℝ) :
    mix (gainLeft δ) (gainRight δ) (43/80) = ((radius-δ : ℝ) : ℂ) := by
  unfold mix gainLeft gainRight
  push_cast
  ring

/-- Both competing denominators obey disk exposure and lie inside the
canonical local range, while their mixed denominator resonates. -/
theorem gain_geometry {δ : ℝ} (hδ : 0 < δ) (hδU : δ ≤ 1/40000) :
    radius < ‖gainLeft δ‖ ∧ radius < ‖gainRight δ‖ ∧
      ‖gainLeft δ‖ < 3/4 ∧ ‖gainRight δ‖ < 3/4 ∧
      ‖mix (gainLeft δ) (gainRight δ) (43/80)‖ = radius-δ := by
  have hpos : 0 < radius-δ := by norm_num [radius] at *; linarith
  have hlo : (20001/40000 : ℝ) ≤ radius-δ := by dsimp [radius]; linarith
  have hhi : radius-δ ≤ 10001/20000 := by dsimp [radius]; linarith
  have hl : ‖gainLeft δ‖^2 = (radius-δ)^2+(1/10 : ℝ)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [gainLeft, Complex.normSq_apply]
    ring
  have hr : ‖gainRight δ‖^2 = (radius-δ)^2+(43/370 : ℝ)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [gainRight, Complex.normSq_apply]
    ring
  have hsqlo : (20001/40000 : ℝ)^2 ≤ (radius-δ)^2 := by nlinarith
  have hsqhi : (radius-δ)^2 ≤ (10001/20000 : ℝ)^2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [radius] at *
    nlinarith [norm_nonneg (gainLeft δ)]
  · dsimp [radius] at *
    nlinarith [norm_nonneg (gainRight δ)]
  · nlinarith [norm_nonneg (gainLeft δ)]
  · nlinarith [norm_nonneg (gainRight δ)]
  · rw [gain_mix, Complex.norm_real, Real.norm_of_nonneg hpos.le]

/-- Their weighted ordinate is zero but their dispersion is a fixed
positive rational number, independent of the horizontal gain. -/
theorem gain_dispersion (δ : ℝ) :
    (43/80 : ℝ)*(gainLeft δ).im+(1-43/80)*(gainRight δ).im = 0 ∧
    (43/80 : ℝ)*(gainLeft δ).im^2+(1-43/80)*(gainRight δ).im^2 = 43/3700 := by
  norm_num [gainLeft, gainRight]

/-- No constant controls even the smaller individual displacement by
the rightward gain for all such exposed, local two-mode resonances.
This blocks that geometric extension of the existing chain theorem;
it is not a counterexample consisting of actual zeta zeros. -/
theorem no_uniform_successor_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/40000 ∧
      radius < ‖gainLeft δ‖ ∧ radius < ‖gainRight δ‖ ∧
      ‖gainLeft δ‖ < 3/4 ∧ ‖gainRight δ‖ < 3/4 ∧
      ‖mix (gainLeft δ) (gainRight δ) (43/80)‖ < radius ∧
      C*δ < (gainLeft δ).im^2 ∧ C*δ < (gainRight δ).im^2 := by
  let δ : ℝ := 1/(40000*(C+1))
  have hp : 0 < C+1 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδU : δ ≤ 1/40000 := by
    dsimp [δ]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hscale : (C+1)*δ = 1/40000 := by dsimp [δ]; field_simp
  obtain ⟨hl, hr, hlR, hrR, hm⟩ := gain_geometry hδ hδU
  refine ⟨δ, hδ, hδU, hl, hr, hlR, hrR, by rw [hm]; linarith, ?_, ?_⟩
  · norm_num [gainLeft]
    nlinarith
  · norm_num [gainRight]
    nlinarith

end
end RiemannGaussian.ZetaRieszRightwardModeAudit
