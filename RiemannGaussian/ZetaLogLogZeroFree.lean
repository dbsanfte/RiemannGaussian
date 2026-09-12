/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogLogExclusion
import RiemannGaussian.ZetaLogLogWidth
import RiemannGaussian.ZetaZeroFreeRegionBand

/-!
# Actual zero-free regions of log-log shape

For every `0<A<pi/(140*log(2))`, the genuine zeta zeros eventually lie
strictly between `A*log(log(abs(t)))/log(abs(t))` and the reflected right
edge. The complete growing-order budget is proved before taking the
height limit. The open coefficient range is retained under smoothing.

The theorem also covers the complete bounded-height divisor and gives
literal zeta nonvanishing on the closed right edge. Each coefficient has
its own existential, unevaluated height threshold. No optimized published
constant or RH conclusion is claimed.
-/

namespace RiemannGaussian.ZetaLogLogZeroFree
noncomputable section
open Complex Filter ZetaLogLogWidth
open scoped Topology

/-- The open coefficient range supplied by the complete proved budget.
This is not claimed to be an optimal zero-free coefficient. -/
def coefficientLimit : ℝ := Real.pi / (140 * Real.log 2)

/-- The proved coefficient range is nonempty. -/
theorem coefficientLimit_pos : 0 < coefficientLimit := by
  unfold coefficientLimit
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

/-- Every positive coefficient below the full limiting budget gives
the ordinary-logarithm right-edge exclusion, with no fixed fractional
loss in its coefficient when removing the smoothed height. -/
theorem exists_eventual_right_margin {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width A |ρ.1.im| < 1 - ρ.1.re := by
  obtain ⟨C, hAC, hClim⟩ := exists_between hAlim
  have hC := hA.trans hAC
  have hcost : 140 * C * Real.log 2 < Real.pi := by
    have hp : 0 < 140 * Real.log 2 :=
      mul_pos (by norm_num) (Real.log_pos (by norm_num))
    have h := (lt_div_iff₀ hp).mp hClim
    nlinarith
  obtain ⟨T₀, hT₀, hz⟩ := ZetaLogLogExclusion.exists_eventual_margin hC hcost
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_le_smoothed hA hAC)
  refine ⟨max T₀ T₁, hT₀.trans (le_max_left _ _), ?_⟩
  intro ρ hρ
  have h := hT₁ |ρ.1.im| ((le_max_right _ _).trans hρ)
  rw [(ZetaLogLogScale.abs_invariance 1 C ρ.1.im).2.2] at h
  exact h.trans_lt (hz ρ ((le_max_left _ _).trans hρ))

/-- Both genuine zero-strip edges have the specified log-log width
for every coefficient in the proved open range at sufficiently large
height. Reflection preserves the ordinary absolute-height coordinate. -/
theorem exists_eventual_strip {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width A |ρ.1.im| < ρ.1.re ∧ ρ.1.re < 1 - width A |ρ.1.im| := by
  obtain ⟨T, hT, hb⟩ := exists_eventual_right_margin hA hAlim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := hb ρ hρ
  have hl := hb (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

/-- The log-log width reaches every zero below the eventual height,
including the complete low divisor. Its positivity, monotonicity and
decay prerequisites are proved for the actual width function. -/
theorem exists_eventual_common_margin {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < width A H ∧ width A H < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          width A H < ρ.1.re ∧ ρ.1.re < 1 - width A H := by
  obtain ⟨T, hT, hb⟩ := exists_eventual_strip hA hAlim
  apply exists_eventual_common_margin_of_antitone (width A) (T := max T baseHeight)
    (by linarith [le_max_left T baseHeight])
    (fun H hH ↦ width_pos hA ((le_max_right _ _).trans hH))
    ((width_antitone hA.le).mono (Set.Ici_subset_Ici.mpr (le_max_right _ _)))
    (width_tendsto_zero A)
  intro ρ hρ
  exact hb ρ ((le_max_left _ _).trans hρ)

/-- Literal zeta is nonzero on the full closed right edge of the
specified log-log region above a coefficient-dependent finite threshold.
Every pole, low-zero and analytic premise has been discharged. -/
theorem exists_eventual_nonvanishing {A : ℝ} (hA : 0 < A) (hAlim : A < coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - width A |s.im| ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨H₀, _, hb⟩ := exists_eventual_common_margin hA hAlim
  refine ⟨max H₀ 2, le_max_right _ _, ?_⟩
  intro s hs hregion
  have ht2 : 2 ≤ |s.im| := (le_max_right _ _).trans hs
  obtain ⟨_, hmu, hz⟩ := hb |s.im| ((le_max_left _ _).trans hs)
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht2
  exact riemannZeta_ne_zero_of_common_margin (by linarith) (fun ρ hρ ↦ (hz ρ hρ).2)
    hs1 le_rfl hregion

end
end RiemannGaussian.ZetaLogLogZeroFree
