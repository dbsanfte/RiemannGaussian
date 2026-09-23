/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovBalancedBudget
import RiemannGaussian.ZetaVinogradovZeroFree

/-!
# The signed angular Vinogradov--Korobov zero-free family

The full analytic radius, signed boundary moment and coefficient-aware
natural degree give actual zero exclusion for every C < 3*pi/98560.
All costs are proved for the original zeta function. The finite starting
height exists but is not numerically evaluated. The union retains every
previous explicit and eventual component, including the older VK width.
-/

namespace RiemannGaussian.ZetaVinogradovAngularZeroFree
noncomputable section
open Filter ZetaVinogradovBalancedScale
open VinogradovNearOneBudget (delta delta_pos)
open VinogradovScaleSelection (heightThreshold)
open scoped Topology

/-- The open coefficient ceiling paid by the exact signed cost. -/
def coefficientLimit : ℝ := 3 * Real.pi / 98560

/-- A concrete member of the proved coefficient interval. -/
theorem rational_coefficient_lt : (1 / 11000 : ℝ) < coefficientLimit := by
  unfold coefficientLimit
  linarith [Real.pi_gt_three]

/-- The complete actual cost is strictly paid eventually for every
coefficient below the displayed ceiling. -/
theorem eventually_parameters {C : ℝ} (hC : 0 < C) (hClim : C < coefficientLimit) :
    ∀ᶠ t : ℝ in atTop, 12 ≤ order t ∧
      (heightThreshold (order t) : ℝ) + 1 ≤ t ∧
      0 < width C t ∧ width C t < delta (order t) / 28 ∧
      ZetaVinogradovBalancedBudget.cost C t < 1 := by
  have hlim : 98560 * C / (3 * Real.pi) < 1 := by
    apply (div_lt_one (by positivity : 0 < 3 * Real.pi)).mpr
    unfold coefficientLimit at hClim
    linarith
  filter_upwards [ZetaVinogradovBalancedScale.eventually_parameters,
    level_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    (width_div_delta_tendsto C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 28)),
    (ZetaVinogradovBalancedBudget.cost_tendsto hC).eventually (gt_mem_nhds hlim)]
    with t ht hl hs hcost
  refine ⟨ht.1, ht.2, width_pos hC hl, ?_, hcost⟩
  have h := (div_lt_iff₀ (delta_pos (order t))).mp hs
  linarith

/-- The actual budget is unchanged by replacing height with absolute height. -/
theorem cost_abs (C t : ℝ) :
    ZetaVinogradovBalancedBudget.cost C |t| = ZetaVinogradovBalancedBudget.cost C t := by
  simp [ZetaVinogradovBalancedBudget.cost, (abs_invariance C t).1,
    (abs_invariance C t).2.2, ZetaVinogradovAngularBudget.budget,
    ZetaVinogradovCanonical.allowance, ZetaVinogradovLocalDisc.profile,
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
  exact ZetaVinogradovAngularBudget.margin_of_budget (order ρ.1.im) hn ρ ht hw hs hcost

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

/-- The exact comparison with the earlier proved VK width. -/
theorem width_eq_previous (C t : ℝ) :
    width C t = (19327352832 * C) * ZetaVinogradovScheduledMargin.width t := by
  unfold width level ZetaVinogradovScheduledMargin.width
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Even the concrete rational coefficient improves the earlier VK
width by more than a million at every positive-second-log height. -/
theorem millionfold_improvement {t : ℝ} (ht : 0 < level t) :
    1000000 * ZetaVinogradovScheduledMargin.width t < width (1 / 11000) t := by
  rw [width_eq_previous]
  have hpos : 0 < ZetaVinogradovScheduledMargin.width t := by
    unfold ZetaVinogradovScheduledMargin.width
    positivity [ZetaNearOneBudgetLimit.scale_pos t]
  exact mul_lt_mul_of_pos_right (by norm_num) hpos

/-- Every positive member of the new family eventually improves every
fixed positive ordinary-logarithm coefficient. No crossover is evaluated. -/
theorem eventually_dominates_previous_loglog {C A : ℝ} (hC : 0 < C) (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ZetaLogLogWidth.width A t < width C t := by
  have h := ZetaVinogradovScheduledMargin.loglog_relative_tendsto (A + 1)
  filter_upwards [ZetaLogLogWidth.eventually_le_smoothed hA (lt_add_one A),
    h.eventually (gt_mem_nhds (by positivity : 0 < 19327352832 * C)),
    ZetaNearOneBudgetLimit.scale_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with t hsm hr hL
  rw [width_eq_previous]
  exact hsm.trans_lt ((div_lt_iff₀ (ZetaVinogradovScheduledMargin.width_pos hL)).mp hr)

/-- The union retains all previous regions even if the new coefficient
is chosen smaller than the old fixed VK coefficient. -/
def unionWidth (C A t : ℝ) : ℝ :=
  max (width C t) (max (ZetaVinogradovScheduledMargin.width t)
    (max (ZetaLogLogWidth.width A |t|) (ZetaUnifiedZeroFree.width t)))

/-- At coefficients at least 1/11000 the older fixed VK width is
already contained, so the full union has a compact three-component formula. -/
theorem unionWidth_eq {C t : ℝ} (hC : 1 / 11000 ≤ C) (ht : 0 < level t) (A : ℝ) :
    unionWidth C A t = max (width C t)
      (max (ZetaLogLogWidth.width A |t|) (ZetaUnifiedZeroFree.width t)) := by
  have hpos : 0 < ZetaVinogradovScheduledMargin.width t := by
    unfold ZetaVinogradovScheduledMargin.width
    positivity [ZetaNearOneBudgetLimit.scale_pos t]
  have hold : ZetaVinogradovScheduledMargin.width t ≤ width C t := by
    rw [width_eq_previous]
    nlinarith
  unfold unionWidth
  rw [← max_assoc, max_eq_left hold]

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
1/11000. Absorbing the older VK component loses none of its coverage. -/
theorem exists_eventual_union_compact {C A : ℝ} (hC : 1 / 11000 ≤ C)
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
  simpa only [unionWidth_eq hC hl A] using hz ρ ((le_max_left _ _).trans ht)

end
end RiemannGaussian.ZetaVinogradovAngularZeroFree
