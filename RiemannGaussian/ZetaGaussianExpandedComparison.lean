/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaUnifiedZeroFree
import RiemannGaussian.ZetaGaussianLiteratureComparison

/-!
# Extend benchmark coverage using the complete proved region

A discharged lower bound for the expanded Gaussian width extends strict
comparison to logarithmic height 480000. The plus-two height correction,
both endpoints and all benchmark parameters are retained. Joining the old
exact crossover interval gives actual zeta nonvanishing and the comparison
on one larger interval. Its upper endpoint is certified, not asserted maximal;
external zero-free proofs are not assumed or imported by these comparisons.
-/

namespace RiemannGaussian.ZetaGaussianExpandedComparison
noncomputable section
open ZetaNearOneBudgetLimit (scale)
open ZetaGaussianBandFrontier

private theorem log_bounds {L : ℝ} (hL : 300000 ≤ L) (hLu : L ≤ 480001) :
    12 ≤ Real.log L ∧ Real.log L ≤ 14 := by
  have hpos : 0 < L := by linarith
  constructor
  · apply (Real.le_log_iff_exp_le hpos).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (show Real.exp 1 ≤ (11 / 4 : ℝ) by linarith [Real.exp_one_lt_d9]) 12
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  · apply (Real.log_le_iff_le_exp hpos).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
      (show (27 / 10 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 14
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith

/-- Keep the plus-two height correction throughout the enlarged comparison. -/
theorem scale_bounds {L t : ℝ} (hL : 300000 ≤ L) (ht : |t| = Real.exp L) :
    L ≤ scale t ∧ scale t ≤ L + 1 := by
  have he : 2 ≤ Real.exp L := by
    have hm := Real.exp_le_exp.mpr (show (1 : ℝ) ≤ L by linarith)
    linarith [Real.exp_one_gt_d9]
  have hshift : Real.exp L + 2 ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  change L ≤ Real.log (|t| + 2) ∧ Real.log (|t| + 2) ≤ L + 1
  rw [ht]
  exact ⟨by simpa only [Real.log_exp] using
    Real.log_le_log (Real.exp_pos L) (show Real.exp L ≤ Real.exp L + 2 by linarith),
    (Real.log_le_iff_le_exp (by positivity)).mpr hshift⟩

/-- A discharged lower bound for the already-proved complete analytic width. -/
theorem width_lower {L t : ℝ} (hL : 300000 ≤ L) (hLu : L ≤ 480000)
    (ht : |t| = Real.exp L) : (18 / 25 : ℝ) / L ≤ ZetaUnifiedZeroFree.width t := by
  have hpos : 0 < L := by linarith
  obtain ⟨hs₀, hs₁⟩ := scale_bounds hL ht
  have hs : 1 ≤ scale t := by linarith
  have hlog := (log_bounds (show 300000 ≤ scale t by linarith)
    (show scale t ≤ 480001 by linarith)).2
  have hcost : ZetaGaussianExpandedRegion.heightCost (scale t) ≤ L + 57331 := by
    unfold ZetaGaussianExpandedRegion.heightCost
    linarith
  have hcpos := ZetaGaussianExpandedRegion.heightCost_pos hs
  apply le_trans _ ((ZetaGaussianRegionUnion.expanded_width_le t).trans
    (ZetaUnifiedZeroFree.gaussian_width_le t))
  rw [ZetaGaussianExpandedRegion.explicitWidth_eq_min hs]
  apply le_min
  · rw [div_le_iff₀ hpos]
    linarith
  · rw [div_le_div_iff₀ hpos (by positivity :
      0 < 1800 * ZetaGaussianExpandedRegion.heightCost (scale t))]
    nlinarith

/-- Every classical denominator at least two is below the new comparison floor. -/
theorem classical_lt_floor {C L : ℝ} (hC : 2 ≤ C) (hL : 300000 ≤ L) :
    classicalWidth C L < (18 / 25 : ℝ) / L := by
  have hpos : 0 < L := by linarith
  unfold classicalWidth
  rw [div_lt_div_iff₀ (by positivity : 0 < C * L) hpos]
  nlinarith [mul_pos hpos (show 0 < C - 25 / 18 by linarith)]

/-- The complete Littlewood family is smaller on the enlarged interval. -/
theorem littlewood_lt_floor {C L : ℝ} (hC : 981 / 50 ≤ C)
    (hL : 300000 ≤ L) (hLu : L ≤ 480000) :
    littlewoodWidth C L < (18 / 25 : ℝ) / L := by
  have hpos : 0 < L := by linarith
  have hlog := (log_bounds hL (by linarith)).2
  unfold littlewoodWidth
  rw [div_lt_div_iff₀ (by positivity : 0 < C * L) hpos]
  have hg : Real.log L < (18 / 25 : ℝ) * C := by linarith
  nlinarith [mul_lt_mul_of_pos_right hg hpos]

/-- Cubing the complete VK denominator retains both fractional powers
and proves the comparison uniformly for every denominator at least 48. -/
theorem vk_lt_floor {C L : ℝ} (hC : 48 ≤ C)
    (hL : 300000 ≤ L) (hLu : L ≤ 480000) :
    vkWidth C L < (18 / 25 : ℝ) / L := by
  have hpos : 0 < L := by linarith
  have hlog := (log_bounds hL (by linarith)).1
  have hlogpos : 0 < Real.log L := by linarith
  let D := 48 * L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hp : (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hq : ((Real.log L) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
    norm_num
  have hD : D ^ 3 = 48 ^ 3 * L ^ 2 * Real.log L := by
    dsimp only [D]
    rw [mul_pow, mul_pow, hp, hq]
  have hg : 0 < (48 : ℝ) ^ 3 * Real.log L - (25 / 18 : ℝ) ^ 3 * L := by
    norm_num
    linarith
  have hcube : ((25 / 18 : ℝ) * L) ^ 3 < D ^ 3 := by
    rw [hD]
    nlinarith [mul_pos (sq_pos_of_pos hpos) hg]
  have hden : (25 / 18 : ℝ) * L < D :=
    (pow_lt_pow_iff_left₀ (by positivity) hDpos.le (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
  have hCden : D ≤ C * L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlogpos.le _)
    exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hpos.le _)
  unfold vkWidth
  calc
    _ < 1 / ((25 / 18 : ℝ) * L) :=
      one_div_lt_one_div_of_lt (by positivity) (hden.trans_le hCden)
    _ = _ := by ring

/-- All three headline families lie strictly within the complete actual width. -/
theorem benchmark_lt_width {L t : ℝ} (hL : 300000 ≤ L) (hLu : L ≤ 480000)
    (ht : |t| = Real.exp L) : benchmarkWidth L < ZetaUnifiedZeroFree.width t := by
  apply lt_of_lt_of_le _ (width_lower hL hLu ht)
  exact max_lt (classical_lt_floor (by norm_num) hL)
    (max_lt (littlewood_lt_floor (by norm_num) hL hLu) (vk_lt_floor (by norm_num) hL hLu))

/-- The intermediate expression retains its negative correction while
lying below the same complete-region comparison floor. -/
theorem intermediate_lt_floor {L : ℝ} (hL : 300000 ≤ L) :
    ZetaGaussianLiteratureComparison.intermediateWidth L < (18 / 25 : ℝ) / L := by
  have hpos : 0 < L := by linarith
  have hden : 0 < (27 / 164 : ℝ) * L + 887 / 125 := by linarith
  have hmain : (1007 / 20000 : ℝ) / ((27 / 164) * L + 887 / 125) < (18 / 25) / L := by
    rw [div_lt_div_iff₀ hden hpos]
    linarith
  have hc : 0 ≤ (349 / 10000 : ℝ) / ((27 / 164) * L + 887 / 125) ^ 2 := by positivity
  unfold ZetaGaussianLiteratureComparison.intermediateWidth
  linarith

/-- The complete Ford expression is below the floor uniformly in its
leading constant, with both secondary denominator terms retained. -/
theorem ford_lt_floor {c L : ℝ} (hc : 1 / 2 ≤ c) (hL : 300000 ≤ L) :
    ZetaGaussianLiteratureComparison.fordWidth c L < (18 / 25 : ℝ) / L := by
  have hpos : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := by
    apply (Real.le_log_iff_exp_le hpos).mpr
    linarith [Real.exp_one_lt_d9]
  have hlogc : -1 ≤ Real.log c := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hc
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    linarith [Real.log_two_lt_d9]
  have hJ : L / 6 ≤ ZetaGaussianLiteratureComparison.fordJ c L := by
    unfold ZetaGaussianLiteratureComparison.fordJ
    linarith
  have hnum : 0 ≤ (49 / 2500 : ℝ) /
      (ZetaGaussianLiteratureComparison.fordJ c L + 23 / 20) :=
    div_nonneg (by norm_num) (by linarith)
  have hden : 0 < ZetaGaussianLiteratureComparison.fordJ c L +
      137 / 200 + (31 / 200) * Real.log L := by linarith
  unfold ZetaGaussianLiteratureComparison.fordWidth
  rw [div_lt_div_iff₀ hden hpos]
  nlinarith [mul_nonneg hnum hpos.le]

/-- The complete proved edge and strict headline comparison extend from
the earlier exact crossover through logarithmic height 480000. This is
a certified interval, not a claim that its new endpoint is maximal. -/
theorem nonvanishing_and_comparison (s : ℂ) {L : ℝ}
    (hL : crossover < L) (hLu : L ≤ 480000) (ht : |s.im| = Real.exp L)
    (hσ : 1 - ZetaUnifiedZeroFree.width s.im ≤ s.re) :
    riemannZeta s ≠ 0 ∧ benchmarkWidth L < ZetaUnifiedZeroFree.width s.im := by
  by_cases hold : L ≤ ceiling
  · exact ZetaUnifiedZeroFree.nonvanishing_and_comparison s hL hold ht hσ
  · have hlower : 300000 ≤ L := by linarith [ceiling_bounds.1, lt_of_not_ge hold]
    have hs1 : s ≠ 1 := by
      intro h
      simp only [h, Complex.one_im, abs_zero] at ht
      exact (Real.exp_ne_zero L) ht.symm
    exact ⟨ZetaUnifiedZeroFree.nonvanishing s hs1 hσ, benchmark_lt_width hlower hLu ht⟩

end
end RiemannGaussian.ZetaGaussianExpandedComparison
