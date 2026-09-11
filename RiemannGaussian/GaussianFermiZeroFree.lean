/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiHeightBounds

/-!
# A stronger eventual zero-free region from the ideal Fermi phase budget

The genuine reflected zero pair has a Gaussian source surplus proportional
to logarithmic height. The full remaining pole and gamma costs are bounded,
and the whole-divisor allowance tends uniformly to zero. This proves an
unconditional eventual edge margin `3/(20*log(abs(t)))`. The threshold is
proved to exist; no numerical evaluation of that threshold is asserted.
-/

namespace RiemannGaussian.GaussianFermiZeroFree

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiLaplaceOrder GaussianFermiMovingAllowance GaussianFermiResonantBudget
open GaussianFermiProfileSurplus GaussianFermiHeightBounds

/-- Once the already proved whole-divisor allowance is below one, the
Gaussian surplus excludes every actual zero in the proposed right edge.
The remaining height hypotheses are explicit elementary inequalities. -/
theorem margin_lt_one_sub_re_of_allowance_lt_one (ρ : NontrivialZetaZero)
    (hlog : 4000 ≤ Real.log |ρ.1.im|)
    (htail : allowance (1 / (9 * (Real.log |ρ.1.im|) ^ 2)) (48 * |ρ.1.im|) < 1) :
    3 / (20 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  classical
  by_contra hnot
  have hd : 1 - ρ.1.re ≤ 3 / (20 * Real.log |ρ.1.im|) := le_of_not_gt hnot
  let t := |ρ.1.im|
  let L := Real.log t
  let H := 48 * t
  let m := zetaPoleReserveZeroMargin H
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
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hμ := normalized_margin_bounds ht (by dsimp [t]; linarith)
  have hscale := scale_admissible (show 1 ≤ L by dsimp [L, t]; linarith) hm.1.le hμ.2
  have hB : 0 < B := by dsimp [B]; positivity
  have heB : B / 2 + B / 2 = B := by ring
  have hrho : 1 / 2 < ρ.1.re := by
    have hsmall : 3 / (20 * Real.log |ρ.1.im|) < (1 / 2 : ℝ) := by
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
  have hbudget := resonant_pair_phase_bound Finset.univ phaseContactExactCoefficients
    (fun j => (phaseContactFrequency j : ℝ)) (fun j _ => (phaseContactExactCoefficients_pos j).le)
    hphase hH (show 0 < B / 2 by positivity) (show 0 < B / 2 by positivity)
    (show zetaPoleReserveZeroMargin H ^ 2 ≤ B / 2 + B / 2 by simpa only [heB] using hscale.1)
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
  have hsurplus := exact_scaled_profile_surplus hL hμ.1 hμ.2 hd
  rw [show 1 - ρ.1.re - m = (1 - m) - ρ.1.re by ring] at hsurplus
  have hcost := exact_phase_cost_le hγ hlog hm.1 hm.2.le hscale.2 hscale.1 hμ.1
  have htailcost : (∑ j : Fin 9, phaseContactExactCoefficients j) * allowance B H ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul exact_total_mass_upper htail.le
        (allowance_nonneg hB H) (by norm_num)
      _ = _ := by ring
  change phaseContactExactCoefficients 0 * halfGaussian B (-m) +
    (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 +
      3 * L / 400 ≤ _ at hsurplus
  change (∑ j : Fin 9, phaseContactExactCoefficients j *
      (poleUpper B (1 - m) ((phaseContactFrequency j : ℝ) * ρ.1.im) +
        gammaUpper ((phaseContactFrequency j : ℝ) * ρ.1.im))) ≤
    phaseContactExactCoefficients 0 * halfGaussian B (-m) +
      (∑ j : Fin 9, if j = 0 then 0 else phaseContactExactCoefficients j) * L / 4 + 8 at hcost
  have hhigh : 4000 ≤ L := hlog
  linarith

/-- An unconditional eventual right-edge margin with exact coefficient
`3/20`. The tail hypothesis is discharged by the actual uniform allowance
theorem; the height threshold is existential, not numerically certified. -/
theorem exists_eventual_right_margin :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      3 / (20 * Real.log |ρ.1.im|) < 1 - ρ.1.re := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (eventually_allowance_lt (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually_ge_atTop (4000 : ℝ))
  refine ⟨max 1 (max T₀ T₁), le_max_left _ _, ?_⟩
  intro ρ hρ
  have ht1 : 1 ≤ |ρ.1.im| := (le_max_left _ _).trans hρ
  have ht0 : T₀ ≤ |ρ.1.im| := (le_max_left T₀ T₁).trans ((le_max_right _ _).trans hρ)
  have htlog : T₁ ≤ |ρ.1.im| := (le_max_right T₀ T₁).trans ((le_max_right _ _).trans hρ)
  have hlog := hT₁ |ρ.1.im| htlog
  have hμ := normalized_margin_bounds (by linarith : 0 < |ρ.1.im|) (by linarith : 2000 ≤ Real.log |ρ.1.im|)
  have hm := zetaPoleReserveZeroMargin_bounds (48 * |ρ.1.im|)
  have hscale := scale_admissible (by linarith : 1 ≤ Real.log |ρ.1.im|) hm.1.le hμ.2
  exact margin_lt_one_sub_re_of_allowance_lt_one ρ hlog
    (hT₀ (48 * |ρ.1.im|) (by linarith) _ hscale.1 hscale.2)

/-- Both edges of the actual critical strip have the stronger eventual
margin. The same genuine height threshold works for both horizontal partners. -/
theorem exists_eventual_strip :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      3 / (20 * Real.log |ρ.1.im|) < ρ.1.re ∧
        ρ.1.re < 1 - 3 / (20 * Real.log |ρ.1.im|) := by
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

/-- At sufficiently large logarithmic height the new width is strictly
larger than the previous all-height reserve margin, as an exact inequality. -/
theorem old_margin_lt_fermi_width {t : ℝ} (ht : 0 < t) (hlog : 4000 ≤ Real.log t) :
    zetaPoleReserveZeroMargin t < 3 / (20 * Real.log t) := by
  have h48 : Real.log (48 : ℝ) ≤ 47 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 48)]
  have he : Real.log (t / 48) = Real.log t - Real.log 48 :=
    Real.log_div ht.ne' (by norm_num)
  have hsmall : 2000 ≤ Real.log (t / 48) := by rw [he]; linarith
  have h := (normalized_margin_bounds (by positivity : 0 < t / 48) hsmall).2
  rw [show (48 : ℝ) * (t / 48) = t by ring] at h
  have hl : (3 / 4 : ℝ) * Real.log t ≤ Real.log (t / 48) := by rw [he]; linarith
  have hm := (zetaPoleReserveZeroMargin_bounds t).1.le
  have hbound := (mul_le_mul_of_nonneg_right hl hm).trans h
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith

/-- Literal zeta nonvanishing on the stronger eventual closed right edge.
The actual pole is excluded automatically by the positive ordinate bound. -/
theorem exists_eventual_nonvanishing :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - 3 / (20 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_eventual_right_margin
  refine ⟨max T₀ (Real.exp 4000), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight hregion hz
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht1 : 1 ≤ |s.im| := hT₀.trans ht0
  have hlog : 4000 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos 4000) ((le_max_right _ _).trans hheight)
    simpa only [Real.log_exp] using h
  have hsmall : 3 / (20 * Real.log |s.im|) < (1 / 2 : ℝ) := by
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
  change 3 / (20 * Real.log |s.im|) < 1 - s.re at h
  linarith

/-- The literal eventual nonvanishing region is proved strictly wider than
the preceding all-height region at the same sufficiently large ordinates. -/
theorem exists_eventual_improved_region :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      zetaPoleReserveZeroMargin s.im < 3 / (20 * Real.log |s.im|) ∧
        (1 - 3 / (20 * Real.log |s.im|) ≤ s.re → riemannZeta s ≠ 0) := by
  obtain ⟨T₀, hT₀, hzero⟩ := exists_eventual_nonvanishing
  refine ⟨max T₀ (Real.exp 4000), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht1 : 1 ≤ |s.im| := hT₀.trans ht0
  have hlog : 4000 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos 4000) ((le_max_right _ _).trans hheight)
    simpa only [Real.log_exp] using h
  have hmargin := old_margin_lt_fermi_width (by linarith : 0 < |s.im|) hlog
  have he : zetaPoleReserveZeroMargin |s.im| = zetaPoleReserveZeroMargin s.im := by
    apply le_antisymm
    · exact zetaPoleReserveZeroMargin_antitone_abs (by simp)
    · exact zetaPoleReserveZeroMargin_antitone_abs (by simp)
  rw [he] at hmargin
  exact ⟨hmargin, hzero s ht0⟩

end
end RiemannGaussian.GaussianFermiZeroFree
