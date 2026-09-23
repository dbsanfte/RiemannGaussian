/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovScheduledMargin
import RiemannGaussian.ZetaUnifiedZeroFree

/-!
# An actual Vinogradov--Korobov zero-free region and its proved union

The complete scheduled bound excludes genuine zeta zeros with width
1/(19327352832*log(|t|+2)^(2/3)*log(log(|t|+2))^(1/3)). Its finite
starting height is proved to exist, but is not numerically evaluated.
Reflection and literal nonvanishing retain the closed right edge.
The union keeps every earlier explicit and eventual proved component.
The coefficient is conservative; no published-record claim is made.
-/

namespace RiemannGaussian.ZetaVinogradovZeroFree
noncomputable section
open Filter ZetaVinogradovScheduledMargin
open scoped Topology

/-- Every positive coefficient in the earlier ordinary-logarithm family
is eventually strictly narrower than the new width. The crossover is
existential, independently of the zero-free starting thresholds. -/
theorem eventually_dominates_previous_loglog {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ZetaLogLogWidth.width A t < width t := by
  filter_upwards [ZetaLogLogWidth.eventually_le_smoothed hA (lt_add_one A),
    eventually_dominates_loglog (A + 1)] with t h₁ h₂
  exact h₁.trans_lt h₂

/-- The entire classical-power right-edge exclusion holds above one
finite height, with no analytic or arithmetic bound left as a premise. -/
theorem exists_eventual_right_margin : ∃ T : ℝ, 4 ≤ T ∧
    ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| → width ρ.1.im < 1 - ρ.1.re := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp eventually_parameters
  refine ⟨max T 4, le_max_right _ _, ?_⟩
  intro ρ hρ
  obtain ⟨hn, ht, _, hw⟩ := hT |ρ.1.im| ((le_max_left _ _).trans hρ)
  have hz := ZetaVinogradovMargin.exact_margin (order |ρ.1.im|) hn ρ ht
  have he : ZetaVinogradovMargin.width (order |ρ.1.im|) |ρ.1.im| =
      ZetaVinogradovMargin.width (order |ρ.1.im|) ρ.1.im := by
    simp [ZetaVinogradovMargin.width, ZetaVinogradovMargin.reserve,
      ZetaVinogradovLocalDisc.profile, ZetaNearOneLogProfile.height, abs_mul]
  rw [he, (abs_invariance ρ.1.im).2] at hw
  exact hw.trans_lt hz

/-- Both genuine zero-strip edges have the new classical-power width
above the same existential height. -/
theorem exists_eventual_strip : ∃ T : ℝ, 4 ≤ T ∧
    ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - width ρ.1.im := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_right_margin
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := hz ρ hρ
  have hl := hz (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

/-- Literal zeta is nonzero on the full closed right edge of the actual
Vinogradov--Korobov region. The starting height is unevaluated. -/
theorem exists_eventual_nonvanishing : ∃ T : ℝ, 4 ≤ T ∧
    ∀ s : ℂ, T ≤ |s.im| → 1 - width s.im ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_right_margin
  refine ⟨T, hT, ?_⟩
  intro s ht hσ hzero
  have ht4 := hT.trans ht
  have htriv : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, rfl⟩
    norm_num at ht4
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht4
  let ρ : NontrivialZetaZero := ⟨s, hzero, htriv, hs1⟩
  have h := hz ρ ht
  change width s.im < 1 - s.re at h
  linarith

/-- The complete eventual union preserves the new classical-power
region, every earlier logarithmic family and all explicit-height bounds. -/
theorem exists_eventual_union {A : ℝ} (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      max (width ρ.1.im)
        (max (ZetaLogLogWidth.width A |ρ.1.im|) (ZetaUnifiedZeroFree.width ρ.1.im)) < ρ.1.re ∧
      ρ.1.re < 1 - max (width ρ.1.im)
        (max (ZetaLogLogWidth.width A |ρ.1.im|) (ZetaUnifiedZeroFree.width ρ.1.im)) := by
  obtain ⟨T₁, hT₁, h₁⟩ := exists_eventual_strip
  obtain ⟨T₂, _, h₂⟩ := ZetaUnifiedZeroFree.union_with_eventual hA hAlim
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro ρ ht
  obtain ⟨ha, hb⟩ := h₁ ρ ((le_max_left _ _).trans ht)
  obtain ⟨hc, hd⟩ := h₂ ρ ((le_max_right _ _).trans ht)
  refine ⟨max_lt ha hc, ?_⟩
  have h := max_lt (by linarith : width ρ.1.im < 1 - ρ.1.re)
    (by linarith : max (ZetaLogLogWidth.width A |ρ.1.im|)
      (ZetaUnifiedZeroFree.width ρ.1.im) < 1 - ρ.1.re)
  linarith

/-- The complete proved union also gives literal nonvanishing on its
closed right edge, without dropping any earlier component. -/
theorem exists_eventual_union_nonvanishing {A : ℝ} (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - max (width s.im)
        (max (ZetaLogLogWidth.width A |s.im|) (ZetaUnifiedZeroFree.width s.im)) ≤ s.re →
      riemannZeta s ≠ 0 := by
  obtain ⟨T, hT, hz⟩ := exists_eventual_union hA hAlim
  refine ⟨T, hT, ?_⟩
  intro s ht hσ hzero
  have ht4 := hT.trans ht
  have htriv : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, rfl⟩
    norm_num at ht4
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht4
  let ρ : NontrivialZetaZero := ⟨s, hzero, htriv, hs1⟩
  have h := (hz ρ ht).2
  change s.re < 1 - max (width s.im)
    (max (ZetaLogLogWidth.width A |s.im|) (ZetaUnifiedZeroFree.width s.im)) at h
  linarith

end
end RiemannGaussian.ZetaVinogradovZeroFree
