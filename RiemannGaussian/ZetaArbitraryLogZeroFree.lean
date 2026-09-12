/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneExclusion
import RiemannGaussian.ZetaLogRegionBand

/-!
# Zero-free logarithmic regions for every fixed positive coefficient

For every fixed `A > 0`, there is a finite height threshold beyond which
every nontrivial zero lies strictly between `A / log(abs t)` and its
reflection across the critical line. The threshold depends on `A` and
is not numerically evaluated. The theorem also gives literal zeta
nonvanishing on the closed right edge and a complete bounded-height
divisor margin. No common threshold over all coefficients is asserted.
-/

namespace RiemannGaussian.ZetaArbitraryLogZeroFree
noncomputable section
open Complex ZetaNearOneExclusion ZetaNearOneBudgetLimit ZetaNearOneLogProfile

/-- At height at least two the smoothed logarithmic height is bounded
by twice the ordinary logarithm, with no asymptotic premise. -/
theorem scale_le_two_log_abs {t : ℝ} (ht : 2 ≤ |t|) :
    scale t ≤ 2 * Real.log |t| := by
  have hpoly : |t| + 2 ≤ |t| ^ 2 := by nlinarith
  have h := Real.log_le_log (by positivity : 0 < |t| + 2) hpoly
  rw [Real.log_pow] at h
  exact h

/-- Every fixed positive coefficient gives an eventual actual
right-edge exclusion with the ordinary logarithmic denominator. -/
theorem exists_eventual_right_margin {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      A / Real.log |ρ.1.im| < 1 - ρ.1.re := by
  obtain ⟨T, hT, hb⟩ := exists_eventual_margin (C := 2 * A) (by positivity)
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have ht := hT.trans hρ
  have hl : 0 < Real.log |ρ.1.im| := Real.log_pos (by linarith)
  have hs := scale_le_two_log_abs ht
  have hbound : A / Real.log |ρ.1.im| ≤ 2 * A / scale ρ.1.im := by
    apply (div_le_div_iff₀ hl (scale_pos ρ.1.im)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hA.le]
  exact hbound.trans_lt (hb ρ hρ)

/-- Every fixed positive logarithmic coefficient is valid at both genuine
strip edges above a coefficient-dependent finite height threshold. -/
theorem exists_eventual_strip {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      A / Real.log |ρ.1.im| < ρ.1.re ∧ ρ.1.re < 1 - A / Real.log |ρ.1.im| := by
  obtain ⟨T, hT, hb⟩ := exists_eventual_right_margin hA
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  have hr := hb ρ hρ
  have hl := hb (NontrivialZetaZero.conjugatePartner ρ) (by
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im, Complex.one_im,
    Complex.conj_im, sub_neg_eq_add, zero_add, Complex.sub_re, Complex.one_re,
    Complex.conj_re] at hl
  constructor <;> linarith

/-- Each arbitrary coefficient reaches the entire bounded-height
divisor, including every zero below the original asymptotic threshold. -/
theorem exists_eventual_common_margin {A : ℝ} (hA : 0 < A) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < A / Real.log H ∧ A / Real.log H < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          A / Real.log H < ρ.1.re ∧ ρ.1.re < 1 - A / Real.log H := by
  apply exists_eventual_common_log_margin hA
  obtain ⟨T, hT, hb⟩ := exists_eventual_strip hA
  exact ⟨T, by linarith, hb⟩

/-- Literal zeta is nonzero on the corresponding closed right edge
for every fixed positive logarithmic coefficient at sufficiently large
height. The threshold is existential and depends on that coefficient. -/
theorem exists_eventual_nonvanishing {A : ℝ} (hA : 0 < A) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - A / Real.log |s.im| ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨T₀, hT₀, hb⟩ := exists_eventual_right_margin hA
  refine ⟨max T₀ (Real.exp (2 * A + 1)), hT₀.trans (le_max_left _ _), ?_⟩
  intro s hheight hregion hz
  have ht0 : T₀ ≤ |s.im| := (le_max_left _ _).trans hheight
  have ht2 : 2 ≤ |s.im| := hT₀.trans ht0
  have hlog : 2 * A + 1 ≤ Real.log |s.im| := by
    have h := Real.log_le_log (Real.exp_pos (2 * A + 1))
      ((le_max_right _ _).trans hheight)
    simpa only [Real.log_exp] using h
  have hsmall : A / Real.log |s.im| < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < Real.log |s.im|)).mpr
    linarith
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at ht2
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := hb ρ ht0
  change A / Real.log |s.im| < 1 - s.re at h
  linarith

end
end RiemannGaussian.ZetaArbitraryLogZeroFree
