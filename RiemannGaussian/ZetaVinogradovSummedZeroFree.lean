/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovSummedCost
import RiemannGaussian.ZetaVinogradovCubicZeroFree

/-!
# A wider VK zero-free family from the summed cubic block profile

The summed cubic block saving reaches actual zeta zeros through the
complete signed angular budget. Every 0<C<3*pi/10640 is admissible,
including C=1/1150, with a finite unevaluated starting height. The
coefficient ceiling is exactly 20/19 times the previous cubic-profile ceiling.
All previous explicit and eventual shapes remain in the proved family
and union. Published benchmark constants are not claimed.
-/

namespace RiemannGaussian.ZetaVinogradovSummedZeroFree
noncomputable section
open Filter ZetaVinogradovCubicScale
open ZetaVinogradovBalancedScale (width level level_atTop width_pos)
open VinogradovSharperBudget (delta delta_pos)
open VinogradovScaleSelection (heightThreshold)
open ZetaVinogradovAngularZeroFree (unionWidth)
open scoped Topology

/-- The open coefficient ceiling paid by the exact signed cost. -/
def coefficientLimit : ℝ := 3 * Real.pi / 10640

/-- A concrete member of the proved coefficient interval. -/
theorem rational_coefficient_lt : (1 / 1150 : ℝ) < coefficientLimit := by
  unfold coefficientLimit
  linarith [Real.pi_gt_d2]

/-- The complete actual cost is strictly paid eventually for every
coefficient below the displayed ceiling. -/
theorem eventually_parameters {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∀ᶠ t : ℝ in atTop, 48 ≤ order t ∧
      (heightThreshold (8 * order t) : ℝ) + 1 ≤ t ∧
      0 < width C t ∧ width C t < delta (order t) / 28 ∧
      ZetaVinogradovSummedCost.cost C t < 1 := by
  have hlim : 10640 * C / (3 * Real.pi) < 1 := by
    apply (div_lt_one (by positivity : 0 < 3 * Real.pi)).mpr
    unfold coefficientLimit at hClim
    linarith
  filter_upwards [ZetaVinogradovCubicScale.eventually_parameters,
    level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    (width_div_delta_tendsto C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 28)),
    (ZetaVinogradovSummedCost.cost_tendsto hC).eventually (gt_mem_nhds hlim)]
    with t ht hl hs hcost
  refine ⟨ht.1, ht.2, width_pos hC hl, ?_, hcost⟩
  have h := (div_lt_iff₀ (delta_pos (order t))).mp hs
  linarith

/-- The actual budget is unchanged by replacing height with absolute height. -/
theorem cost_abs (C t : ℝ) :
    ZetaVinogradovSummedCost.cost C |t| = ZetaVinogradovSummedCost.cost C t := by
  simp [ZetaVinogradovSummedCost.cost, (abs_invariance C t).1,
    (abs_invariance C t).2.2, ZetaVinogradovSummedCost.budget,
    ZetaAngularDiscBudget.budget, ZetaVinogradovSummedDisc.profile,
    ZetaNearOneLogProfile.height, abs_mul]

/-- Every positive coefficient below the signed ceiling excludes actual
right-edge zeros above a finite height, with no unpaid bound as a premise. -/
theorem exists_eventual_right_margin {C : ℝ} (hC : 0 < C)
    (hClim : C < coefficientLimit) : ∃ T : ℝ, 4 ≤ T ∧
      ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| → width C ρ.1.im < 1 - ρ.1.re := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_parameters hC hClim)
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨hn, ht, hw, hs, hcost⟩ := hT |ρ.1.im| ((le_max_left _ _).trans hρ)
  rw [(abs_invariance C ρ.1.im).1] at hn ht hs
  rw [(abs_invariance C ρ.1.im).2.2] at hw hs
  rw [cost_abs] at hcost
  exact ZetaVinogradovSummedCost.margin_of_budget (order ρ.1.im) hn ρ ht hw hs hcost

/-- Both edges of the genuine zero strip have the wider VK margin. -/
theorem exists_eventual_strip {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - width C ρ.1.im := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_right_margin hC hClim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := hz ρ hρ
  have hl := hz (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

/-- Literal zeta is nonzero on the full closed right edge. The
coefficient-dependent starting height is finite and unevaluated. -/
theorem exists_eventual_nonvanishing {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - width C s.im ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_right_margin hC hClim
  refine ⟨T, hT, ?_⟩
  intro s ht hσ hzero
  have ht4 := hT.trans ht
  have htriv : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, rfl⟩
    norm_num at ht4
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht4
  let ρ : NontrivialZetaZero := ⟨s, hzero, htriv, hs1⟩
  have h := hz ρ ht
  change width C s.im < 1 - s.re at h
  linarith

/-- The complete admissible coefficient range increases by exactly
20/19, after the actual moment and analytic costs have been paid. -/
theorem coefficient_gain :
    coefficientLimit = (20 / 19 : ℝ) * ZetaVinogradovCubicZeroFree.coefficientLimit := by
  unfold coefficientLimit ZetaVinogradovCubicZeroFree.coefficientLimit
  ring

/-- The displayed rational member contains every previous cubic-profile VK
coefficient; its starting threshold is still stated explicitly as unevaluated. -/
theorem previous_limit_lt_rational :
    ZetaVinogradovCubicZeroFree.coefficientLimit < (1 / 1150 : ℝ) := by
  unfold ZetaVinogradovCubicZeroFree.coefficientLimit
  linarith [Real.pi_lt_d2]

/-- The complete union has no unproved analytic or arithmetic premise. -/
theorem exists_eventual_union {C A : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit)
    (hA : 0 < A) (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      unionWidth C A ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - unionWidth C A ρ.1.im := by
  obtain ⟨T₁, hT₁, h₁⟩ := exists_eventual_strip hC hClim
  obtain ⟨T₂, _, h₂⟩ := ZetaVinogradovZeroFree.exists_eventual_union hA hAlim
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro ρ ht
  obtain ⟨ha, hb⟩ := h₁ ρ ((le_max_left _ _).trans ht)
  obtain ⟨hc, hd⟩ := h₂ ρ ((le_max_right _ _).trans ht)
  refine ⟨max_lt ha hc, ?_⟩
  have h := max_lt (by linarith : width C ρ.1.im < 1 - ρ.1.re)
    (by linarith : max (ZetaVinogradovScheduledMargin.width ρ.1.im)
      (max (ZetaLogLogWidth.width A |ρ.1.im|) (ZetaUnifiedZeroFree.width ρ.1.im)) < 1 - ρ.1.re)
  change ρ.1.re < 1 - max _ _
  linarith

/-- Actual nonvanishing on the closed edge of the complete proved union. -/
theorem exists_eventual_union_nonvanishing {C A : ℝ} (hC : 0 < C)
    (hClim : C < coefficientLimit) (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - unionWidth C A s.im ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_union hC hClim hA hAlim
  refine ⟨T, hT, ?_⟩
  intro s ht hσ hzero
  have ht4 := hT.trans ht
  have htriv : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, rfl⟩
    norm_num at ht4
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht4
  let ρ : NontrivialZetaZero := ⟨s, hzero, htriv, hs1⟩
  have h := (hz ρ ht).2
  change s.re < 1 - unionWidth C A s.im at h
  linarith

/-- The compact displayed union follows at every coefficient at least
1/1150. Absorbing the older VK component loses none of its coverage. -/
theorem exists_eventual_union_compact {C A : ℝ} (hC : 1 / 1150 ≤ C)
    (hClim : C < coefficientLimit) (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      max (width C ρ.1.im)
        (max (ZetaLogLogWidth.width A |ρ.1.im|) (ZetaUnifiedZeroFree.width ρ.1.im)) < ρ.1.re ∧
      ρ.1.re < 1 - max (width C ρ.1.im)
        (max (ZetaLogLogWidth.width A |ρ.1.im|) (ZetaUnifiedZeroFree.width ρ.1.im)) := by
  obtain ⟨T₁, hT₁, hz⟩ := exists_eventual_union (by linarith : 0 < C) hClim hA hAlim
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (level_atTop.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro ρ ht
  have hl := hT₂ |ρ.1.im| ((le_max_right _ _).trans ht)
  rw [(abs_invariance C ρ.1.im).2.1] at hl
  have hC' : 1 / 11000 ≤ C := by linarith
  simpa only [ZetaVinogradovAngularZeroFree.unionWidth_eq hC' hl A] using hz ρ ((le_max_left _ _).trans ht)

end
end RiemannGaussian.ZetaVinogradovSummedZeroFree
