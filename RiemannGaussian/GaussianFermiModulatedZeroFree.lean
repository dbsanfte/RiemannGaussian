/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiModulatedProfile
import RiemannGaussian.GaussianFermiModulatedHeight
import RiemannGaussian.GaussianFermiCurvatureZeroFree

/-!
# Unconditional zero exclusion by the positive modulated Gaussian

The proved `3/16` region supplies a common margin for the whole height
divisor. Three coupled evaluations preserve prime positivity and the full
resonant multiplicity source. Exact modulated Laplace bounds dominate the
complete pole, gamma and outside-divisor costs at target `24/125`.
Every eventual premise is discharged; the final height is existential.
-/

namespace RiemannGaussian.GaussianFermiModulatedZeroFree
noncomputable section
open Complex Filter Set
open MeasureTheory hiding average
open scoped Topology
open GaussianFermiMovingAllowance GaussianFermiProfileSurplus GaussianFermiHeightBounds
open GaussianFermiModulatedBudget GaussianFermiModulatedSource GaussianFermiModulatedHeight
open GaussianModulatedLaplace GaussianFermiGaussianMixture GaussianFermiPoleFormula

/-- The full actual modulated budget excludes the larger right edge
once the complete band and original outside allowance are available. -/
theorem margin_lt_one_sub_re_of_allowance_lt_one (ρ : NontrivialZetaZero)
    (hlog : 100000 ≤ Real.log |ρ.1.im|)
    (hband : ∀ η : NontrivialZetaZero, |η.1.im| ≤ 50 * |ρ.1.im| →
      3 / (16 * Real.log (50 * |ρ.1.im|)) ≤ η.1.re ∧
        η.1.re ≤ 1 - 3 / (16 * Real.log (50 * |ρ.1.im|)))
    (hold : zetaPoleReserveZeroMargin (50 * |ρ.1.im|) ≤
      3 / (16 * Real.log (50 * |ρ.1.im|)))
    (htail : allowance (1 / (9 * (Real.log |ρ.1.im|) ^ 2)) (50 * |ρ.1.im|) < 1) :
    24 / (125 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  classical
  by_contra hnot
  have hd : 1 - ρ.1.re ≤ 24 / (125 * Real.log |ρ.1.im|) := le_of_not_gt hnot
  let t := |ρ.1.im|
  let L := Real.log t
  let H := 50 * t
  let m := 3 / (16 * Real.log H)
  let B := 1 / (9 * L ^ 2)
  let δ := 1 / (2 * L)
  have hγ : ρ.1.im ≠ 0 := by intro h; simp [h] at hlog; norm_num at hlog
  have ht : 0 < t := abs_pos.mpr hγ
  have hL : 0 < L := by dsimp [L, t]; linarith
  have hL1 : 1 ≤ L := by dsimp [L, t]; linarith
  have ht1 : 1 ≤ t := by
    have h := Real.log_le_sub_one_of_pos ht
    change L ≤ t - 1 at h
    linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hμ : 937 / 5000 ≤ L * m ∧ L * m ≤ 3 / 16 :=
    GaussianFermiModulatedProfile.normalized_margin_bounds ht hlog
  have hmpos : 0 < m := pos_of_mul_pos_left (show 0 < m * L by nlinarith [hμ.1]) hL.le
  have hmu : m < 1 / 4 := by
    have h := mul_le_mul_of_nonneg_right hL1 hmpos.le
    nlinarith [hμ.2]
  have hscale := GaussianFermiModulatedProfile.scale_admissible hL1 hmpos.le (by linarith [hμ.2])
  have hB : 0 < B := by dsimp [B]; positivity
  have heB : B / 2 + B / 2 = B := by ring
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδ : |δ| ≤ 1 := by
    rw [abs_of_pos hδpos]
    apply (div_le_one (by positivity : 0 < 2 * L)).mpr
    linarith
  have hrho : 1 / 2 < ρ.1.re := by
    have hsmall : 24 / (125 * Real.log |ρ.1.im|) < (1 / 2 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith
    linarith
  have hfreq : ∀ j ∈ (Finset.univ : Finset (Fin 9)),
      2 * (|(phaseContactFrequency j : ℝ) * ρ.1.im| + |δ|) ≤ H := by
    intro j _
    have hj : (phaseContactFrequency j : ℝ) ≤ 24 := by exact_mod_cast exact_frequency_le j
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ phaseContactFrequency j)]
    change 2 * ((phaseContactFrequency j : ℝ) * t + |δ|) ≤ 50 * t
    nlinarith
  have hphase : ∀ x : ℝ, 0 ≤ ∑ j : Fin 9,
      phaseContactExactCoefficients j * Real.cos ((phaseContactFrequency j : ℝ) * x) := by
    intro x
    have h := phaseContactExactFamily_kernel_nonneg x
    rwa [phaseContactExactFamily, phaseContactFrequencyFamily_kernel] at h
  have hbudget := resonant_pair_phase_bound Finset.univ phaseContactExactCoefficients
    (fun j ↦ (phaseContactFrequency j : ℝ)) (fun j _ ↦ (phaseContactExactCoefficients_pos j).le)
    hphase hH (show 0 < B / 2 by positivity) (show 0 < B / 2 by positivity) hold hmu.le
    (show m ^ 2 ≤ B / 2 + B / 2 by simpa only [heB] using hscale.1) hband ρ hrho
    (show |ρ.1.im| ≤ H by dsimp [H]; change t ≤ 50 * t; linarith)
    hfreq (1 : Fin 9) (Finset.mem_univ _) (by norm_num [phaseContactFrequency])
  simp only [heB] at hbudget
  change phaseContactExactCoefficients 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
    halfModulated B δ ((1 - m) - ρ.1.re) ≤
      (∑ j : Fin 9, phaseContactExactCoefficients j * average δ
        (fun v ↦ polePair B (1 - m) v - Real.log Real.pi / 4 +
          digammaAverage (1 - 2 * m) (B / 2) (B / 2) v) ((phaseContactFrequency j : ℝ) * ρ.1.im)) +
        (∑ j : Fin 9, phaseContactExactCoefficients j) * allowance B H at hbudget
  have hmult : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast (Nat.succ_le_of_lt (analyticZetaZeroMultiplicity_positive ρ))
  have hsource : phaseContactExactCoefficients 1 * halfModulated B δ ((1 - m) - ρ.1.re) ≤
      phaseContactExactCoefficients 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
        halfModulated B δ ((1 - m) - ρ.1.re) := by
    apply mul_le_mul_of_nonneg_right _ (halfModulated_nonneg _ _ _)
    nlinarith [phaseContactExactCoefficients_pos (1 : Fin 9)]
  have hsurplus := GaussianFermiModulatedProfile.exact_scaled_profile_surplus hL hμ.1 hμ.2 hd
  rw [show 1 - ρ.1.re - m = (1 - m) - ρ.1.re by ring] at hsurplus
  have hcost := exact_average_phase_cost_le hγ hlog hmpos hmu.le
    (show 0 < B / 2 by positivity) (show 0 < B / 2 by positivity)
    (show B / 2 + B / 2 ≤ 1 by simpa only [heB] using hscale.2)
    (show m ^ 2 ≤ B / 2 + B / 2 by simpa only [heB] using hscale.1)
    (show 1 / 10 ≤ Real.log |ρ.1.im| * m by change 1 / 10 ≤ L * m; linarith [hμ.1]) hδ
  simp only [heB] at hcost
  have htailcost : (∑ j : Fin 9, phaseContactExactCoefficients j) * allowance B H ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul exact_total_mass_upper htail.le
        (allowance_nonneg hB H) (by norm_num)
      _ = _ := by ring
  change phaseContactExactCoefficients 0 * halfModulated B δ (-m) +
    (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
      3 * L / 20000 ≤ _ at hsurplus
  have hhigh : 100000 ≤ L := hlog
  linarith

/-- Every common-band, comparison-margin and complete-tail premise is
discharged for the actual `24/125` right-edge exclusion. -/
theorem exists_eventual_right_margin :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      24 / (125 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_allowance_lt (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T₁, hT₁, hband⟩ := GaussianFermiCurvatureZeroFree.exists_eventual_common_margin
  obtain ⟨T₂, hT₂, hformula⟩ := exists_eventual_fermiZeroMargin_eq
  refine ⟨max (max T₀ T₁) (max T₂ (Real.exp 100000)),
    hT₁.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro ρ hρ
  have ht0 : T₀ ≤ |ρ.1.im| := (le_max_left _ _).trans ((le_max_left _ _).trans hρ)
  have ht1 : T₁ ≤ |ρ.1.im| := (le_max_right _ _).trans ((le_max_left _ _).trans hρ)
  have ht2 : T₂ ≤ |ρ.1.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hρ)
  have htpos : 0 < |ρ.1.im| := by linarith
  have htone : 1 ≤ |ρ.1.im| := hT₁.trans ht1
  have hlog : 100000 ≤ Real.log |ρ.1.im| := by
    have h := Real.log_le_log (Real.exp_pos 100000)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hρ))
    simpa only [Real.log_exp] using h
  have h50 : 0 < 50 * |ρ.1.im| := by positivity
  have hcommon := hband (50 * |ρ.1.im|) (by linarith)
  have he := (hformula (50 * |ρ.1.im|) (by rw [abs_of_pos h50]; linarith)).1
  rw [abs_of_pos h50] at he
  have hμ := GaussianFermiModulatedProfile.normalized_margin_bounds htpos hlog
  have hscale := GaussianFermiModulatedProfile.scale_admissible
    (by linarith : 1 ≤ Real.log |ρ.1.im|) hcommon.1.le (by linarith [hμ.2])
  have hlogH : 0 < Real.log (50 * |ρ.1.im|) := by
    have h := Real.log_le_log htpos (show |ρ.1.im| ≤ 50 * |ρ.1.im| by linarith)
    linarith
  have hold : zetaPoleReserveZeroMargin (50 * |ρ.1.im|) ≤
      3 / (16 * Real.log (50 * |ρ.1.im|)) := by
    apply (zetaPoleReserve_margin_le_fermi _).trans
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have holdscale : zetaPoleReserveZeroMargin (50 * |ρ.1.im|) ^ 2 ≤
      1 / (9 * Real.log |ρ.1.im| ^ 2) :=
    (pow_le_pow_left₀ (zetaPoleReserveZeroMargin_bounds _).1.le hold 2).trans hscale.1
  exact margin_lt_one_sub_re_of_allowance_lt_one ρ hlog
    (fun η hη ↦ ⟨(hcommon.2.2 η hη).1.le, (hcommon.2.2 η hη).2.le⟩) hold
    (hT₀ (50 * |ρ.1.im|) (by linarith) _ holdscale hscale.2)

/-- Both edges of the genuine nontrivial zero strip have the eventual
`24/125` logarithmic margin. -/
theorem exists_eventual_strip :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      24 / (125 * Real.log |ρ.1.im|) < ρ.1.re ∧
        ρ.1.re < 1 - 24 / (125 * Real.log |ρ.1.im|) := by
  obtain ⟨T, hT, h⟩ := exists_eventual_right_margin
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := h ρ hρ
  have hl := h (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re, Complex.conj_re] at hl
  constructor <;> linarith

/-- The enlarged region feeds back into the complete bounded-height
divisor, including every low zero needed by a subsequent common-margin budget. -/
theorem exists_eventual_common_margin :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < 24 / (125 * Real.log H) ∧ 24 / (125 * Real.log H) < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          24 / (125 * Real.log H) < ρ.1.re ∧ ρ.1.re < 1 - 24 / (125 * Real.log H) := by
  have hregion : ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      (24 / 125 : ℝ) / Real.log |ρ.1.im| < ρ.1.re ∧
        ρ.1.re < 1 - (24 / 125 : ℝ) / Real.log |ρ.1.im| := by
    simpa only [div_div] using exists_eventual_strip
  simpa only [div_div] using exists_eventual_common_log_margin (by norm_num : (0 : ℝ) < 24 / 125) hregion

/-- Literal zeta nonvanishing on the larger closed right edge. The finite
height threshold is existential rather than numerically evaluated. -/
theorem exists_eventual_nonvanishing :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - 24 / (125 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_eventual_right_margin
  refine ⟨max T₀ (Real.exp 100000), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight hregion hz
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht1 : 1 ≤ |s.im| := hT₀.trans ht0
  have hlog : 100000 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos 100000) ((le_max_right _ _).trans hheight)
    simpa only [Real.log_exp] using h
  have hsmall : 24 / (125 * Real.log |s.im|) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; simp [he] at ht1; norm_num at ht1
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := hzero ρ ht0
  change 24 / (125 * Real.log |s.im|) < 1 - s.re at h
  linarith

end
end RiemannGaussian.GaussianFermiModulatedZeroFree
