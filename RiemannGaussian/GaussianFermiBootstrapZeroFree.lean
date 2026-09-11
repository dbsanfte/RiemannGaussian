/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiMarginBudget
import RiemannGaussian.GaussianFermiBootstrapProfile

/-!
# A second unconditional Fermi zero-free improvement

Feeding the already proved global `3/20` margin back into the genuine
Fermi budget gives the stronger eventual width `4/(25*log(abs(t)))`.
The larger shift does not increase the outside allowance. Exact Gaussian
enclosures pay every remaining pole and gamma term, and the original
uniform tail theorem discharges the last condition. The resulting height
threshold is existential, not numerically evaluated.
-/

namespace RiemannGaussian.GaussianFermiBootstrapZeroFree
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiLaplaceOrder GaussianFermiMovingAllowance GaussianFermiMarginBudget
open GaussianFermiProfileSurplus GaussianFermiHeightBounds

/-- At the proved larger interior margin, the second Gaussian surplus
excludes an actual right-edge zero once the original allowance is below
one. The eventual theorem below discharges both auxiliary conditions. -/
theorem margin_lt_one_sub_re_of_allowance_lt_one (ρ : NontrivialZetaZero)
    (hlog : 100000 ≤ Real.log |ρ.1.im|)
    (hmargin : zetaFermiZeroMargin (48 * |ρ.1.im|) =
      3 / (20 * Real.log (48 * |ρ.1.im|)))
    (htail : allowance (1 / (9 * (Real.log |ρ.1.im|) ^ 2)) (48 * |ρ.1.im|) < 1) :
    4 / (25 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  classical
  by_contra hnot
  have hd : 1 - ρ.1.re ≤ 4 / (25 * Real.log |ρ.1.im|) := le_of_not_gt hnot
  let t := |ρ.1.im|
  let L := Real.log t
  let H := 48 * t
  let m := zetaFermiZeroMargin H
  let B := 1 / (9 * L ^ 2)
  have hγ : ρ.1.im ≠ 0 := by
    intro h
    simp [h] at hlog
    norm_num at hlog
  have ht : 0 < t := abs_pos.mpr hγ
  have hL : 0 < L := by dsimp [L, t]; linarith
  have ht1 : 1 ≤ t := by
    have h := Real.log_le_sub_one_of_pos ht
    change L ≤ t - 1 at h
    dsimp [L, t] at h
    dsimp [t]
    linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hm := zetaFermiZeroMargin_bounds H
  have hμ := GaussianFermiBootstrapProfile.normalized_margin_bounds_of_eq ht hlog hmargin
  have hscale := GaussianFermiBootstrapProfile.scale_admissible
    (show 1 ≤ L by dsimp [L, t]; linarith) hm.1.le
    (show L * m ≤ 1 / 3 by change Real.log t * zetaFermiZeroMargin (48 * t) ≤ 1 / 3; linarith [hμ.2])
  have hB : 0 < B := by dsimp [B]; positivity
  have heB : B / 2 + B / 2 = B := by ring
  have hrho : 1 / 2 < ρ.1.re := by
    have hsmall : 4 / (25 * Real.log |ρ.1.im|) < (1 / 2 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith
    linarith
  have hfreq : ∀ j ∈ (Finset.univ : Finset (Fin 9)),
      2 * |(phaseContactFrequency j : ℝ) * ρ.1.im| ≤ H := by
    intro j _
    have hj : (phaseContactFrequency j : ℝ) ≤ 24 := by exact_mod_cast exact_frequency_le j
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ phaseContactFrequency j)]
    change 2 * ((phaseContactFrequency j : ℝ) * t) ≤ 48 * t
    nlinarith
  have hphase : ∀ x : ℝ, 0 ≤ ∑ j : Fin 9,
      phaseContactExactCoefficients j * Real.cos ((phaseContactFrequency j : ℝ) * x) := by
    intro x
    have h := phaseContactExactFamily_kernel_nonneg x
    rwa [phaseContactExactFamily, phaseContactFrequencyFamily_kernel] at h
  have hbudget := fermi_resonant_pair_phase_bound Finset.univ phaseContactExactCoefficients
    (fun j => (phaseContactFrequency j : ℝ)) (fun j _ => (phaseContactExactCoefficients_pos j).le)
    hphase hH (show 0 < B / 2 by positivity) (show 0 < B / 2 by positivity)
    (show zetaFermiZeroMargin H ^ 2 ≤ B / 2 + B / 2 by simpa only [heB] using hscale.1)
    (show B / 2 + B / 2 ≤ 1 by simpa only [heB] using hscale.2) ρ hrho
    (show |ρ.1.im| ≤ H by dsimp [H]; change t ≤ 48 * t; linarith)
    hfreq (1 : Fin 9) (Finset.mem_univ _) (by norm_num [phaseContactFrequency])
  simp only [heB] at hbudget
  have hbudget' : phaseContactExactCoefficients 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      halfGaussian B ((1 - m) - ρ.1.re) ≤
      (∑ j : Fin 9, phaseContactExactCoefficients j *
        (poleUpper B (1 - m) ((phaseContactFrequency j : ℝ) * ρ.1.im) +
          gammaUpper ((phaseContactFrequency j : ℝ) * ρ.1.im))) +
            (∑ j : Fin 9, phaseContactExactCoefficients j) * allowance B H := by
    simpa only [gammaUpper, add_assoc] using hbudget
  have hmult : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast (Nat.succ_le_of_lt (analyticZetaZeroMultiplicity_positive ρ))
  have hsource : phaseContactExactCoefficients 1 * halfGaussian B ((1 - m) - ρ.1.re) ≤
      phaseContactExactCoefficients 1 * (analyticZetaZeroMultiplicity ρ : ℝ) *
        halfGaussian B ((1 - m) - ρ.1.re) := by
    apply mul_le_mul_of_nonneg_right _ (halfGaussian_nonneg _ _)
    nlinarith [phaseContactExactCoefficients_pos (1 : Fin 9)]
  have hsurplus := GaussianFermiBootstrapProfile.exact_scaled_profile_surplus hL hμ.1 hμ.2 hd
  rw [show 1 - ρ.1.re - m = (1 - m) - ρ.1.re by ring] at hsurplus
  have hcost := exact_phase_cost_le hγ (by linarith : 4000 ≤ Real.log |ρ.1.im|)
    hm.1 hm.2.le hscale.2 hscale.1
    (show 1 / 10 ≤ Real.log |ρ.1.im| * m by change 1 / 10 ≤ Real.log t * zetaFermiZeroMargin (48 * t); linarith [hμ.1])
  have htailcost : (∑ j : Fin 9, phaseContactExactCoefficients j) * allowance B H ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul exact_total_mass_upper htail.le
        (allowance_nonneg hB H) (by norm_num)
      _ = _ := by ring
  change phaseContactExactCoefficients 0 * halfGaussian B (-m) +
    (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
      3 * L / 20000 ≤ _ at hsurplus
  change (∑ j : Fin 9, phaseContactExactCoefficients j *
      (poleUpper B (1 - m) ((phaseContactFrequency j : ℝ) * ρ.1.im) +
        gammaUpper ((phaseContactFrequency j : ℝ) * ρ.1.im))) ≤
    phaseContactExactCoefficients 0 * halfGaussian B (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 + 8 at hcost
  have hhigh : 100000 ≤ L := hlog
  linarith

/-- Feeding back the first Fermi region proves the strictly stronger
eventual right-edge coefficient `4/25`. The margin formula and original
uniform divisor-tail condition are both discharged. -/
theorem exists_eventual_right_margin :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      4 / (25 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_allowance_lt (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T₁, hT₁, hformula⟩ := exists_eventual_fermiZeroMargin_eq
  refine ⟨max (max T₀ T₁) (Real.exp 100000),
    hT₁.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro ρ hρ
  have ht0 : T₀ ≤ |ρ.1.im| := (le_max_left _ _).trans ((le_max_left _ _).trans hρ)
  have ht1 : T₁ ≤ |ρ.1.im| := (le_max_right _ _).trans ((le_max_left _ _).trans hρ)
  have htpos : 0 < |ρ.1.im| := by linarith
  have htone : 1 ≤ |ρ.1.im| := hT₁.trans ht1
  have hlog : 100000 ≤ Real.log |ρ.1.im| := by
    have h := Real.log_le_log (Real.exp_pos 100000) ((le_max_right _ _).trans hρ)
    simpa only [Real.log_exp] using h
  have h48 : 0 < 48 * |ρ.1.im| := by positivity
  have hheight : T₁ ≤ |(48 * |ρ.1.im|)| := by rw [abs_of_pos h48]; linarith
  have he := (hformula (48 * |ρ.1.im|) hheight).1
  rw [abs_of_pos h48] at he
  have hμ := GaussianFermiBootstrapProfile.normalized_margin_bounds_of_eq htpos hlog he
  have hm := zetaFermiZeroMargin_bounds (48 * |ρ.1.im|)
  have hscale := GaussianFermiBootstrapProfile.scale_admissible
    (by linarith : 1 ≤ Real.log |ρ.1.im|) hm.1.le (by linarith [hμ.2])
  have holdscale : zetaPoleReserveZeroMargin (48 * |ρ.1.im|) ^ 2 ≤
      1 / (9 * Real.log |ρ.1.im| ^ 2) :=
    (pow_le_pow_left₀ (zetaPoleReserveZeroMargin_bounds _).1.le
      (zetaPoleReserve_margin_le_fermi _) 2).trans hscale.1
  exact margin_lt_one_sub_re_of_allowance_lt_one ρ hlog he
    (hT₀ (48 * |ρ.1.im|) (by linarith) _ holdscale hscale.2)

/-- Both sides of the actual nontrivial zero strip have the improved
eventual `4/25` margin, by genuine horizontal reflection. -/
theorem exists_eventual_strip :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      4 / (25 * Real.log |ρ.1.im|) < ρ.1.re ∧
        ρ.1.re < 1 - 4 / (25 * Real.log |ρ.1.im|) := by
  obtain ⟨T, hT, h⟩ := exists_eventual_right_margin
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := h ρ hρ
  have hl := h (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

/-- Literal zeta nonvanishing on the improved closed right edge. The
positive height excludes the actual pole without an extra hypothesis. -/
theorem exists_eventual_nonvanishing :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - 4 / (25 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_eventual_right_margin
  refine ⟨max T₀ (Real.exp 100000), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight hregion hz
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht1 : 1 ≤ |s.im| := hT₀.trans ht0
  have hlog : 100000 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos 100000) ((le_max_right _ _).trans hheight)
    simpa only [Real.log_exp] using h
  have hsmall : 4 / (25 * Real.log |s.im|) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro he
    simp [he] at ht1
    norm_num at ht1
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := hzero ρ ht0
  change 4 / (25 * Real.log |s.im|) < 1 - s.re at h
  linarith

/-- The new literal region is strictly wider than the preceding global
Fermi margin at the same sufficiently large ordinates. -/
theorem exists_eventual_improved_region :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      zetaFermiZeroMargin s.im < 4 / (25 * Real.log |s.im|) ∧
        (1 - 4 / (25 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0) := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_eventual_nonvanishing
  obtain ⟨T₁, _, hformula⟩ := exists_eventual_fermiZeroMargin_eq
  refine ⟨max T₀ (max T₁ (Real.exp 100000)), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht1 : T₁ ≤ |s.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hheight)
  have hlog : 100000 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos 100000)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hheight))
    simpa only [Real.log_exp] using h
  refine ⟨?_, hzero s ht0⟩
  rw [(hformula s.im ht1).1]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

end
end RiemannGaussian.GaussianFermiBootstrapZeroFree
