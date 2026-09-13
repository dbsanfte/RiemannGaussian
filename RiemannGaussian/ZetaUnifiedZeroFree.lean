/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianRegionUnion
import RiemannGaussian.ZetaPoleReserveBootstrap
import RiemannGaussian.ZetaGaussianBandFrontier

/-!
# Preserve the complete explicit zero-free coverage

The two Gaussian budgets improve the large-height coefficient. The older
signed-pole and iterated-reserve bounds are stronger at smaller heights.
Their maximum preserves all three analytic proofs. Below the Gaussian
starting height its physical cap is smaller than the signed-pole width,
so the same elementary maximum is valid at every ordinate, without a
discontinuity or an unevaluated transition height. External benchmark
nonvanishing is not assumed.
-/

namespace RiemannGaussian.ZetaUnifiedZeroFree
noncomputable section
open Complex

/-- The complete explicit width keeps both Gaussian components and the
earlier signed-pole/reserve proof at every height. -/
def width (t : ℝ) : ℝ := max (zetaPoleReserveZeroMargin t) (ZetaGaussianRegionUnion.width t)

/-- The displayed region cannot discard the existing Gaussian coverage. -/
theorem gaussian_width_le (t : ℝ) : ZetaGaussianRegionUnion.width t ≤ width t :=
  le_max_right _ _

/-- The displayed region cannot discard the earlier all-height reserve. -/
theorem reserve_width_le (t : ℝ) : zetaPoleReserveZeroMargin t ≤ width t :=
  le_max_left _ _

/-- All complete high-height windows retain the monotonicity required
for analytic discs. The reserve term uses its global absolute-height law. -/
theorem width_antitone_abs {a b : ℝ} (ha : 1 ≤ ZetaNearOneBudgetLimit.scale a)
    (hab : |a| ≤ |b|) : width b ≤ width a := by
  apply max_le_max (zetaPoleReserveZeroMargin_antitone_abs hab)
  apply ZetaGaussianRegionUnion.width_antitone ha
  change Real.log (|a| + 2) ≤ Real.log (|b| + 2)
  exact Real.log_le_log (by positivity : 0 < |a| + 2) (by linarith)

/-- A uniform positive width below one quarter keeps the literal right
edge in the positive half-plane, including at zero height. -/
theorem width_bounds (t : ℝ) : 0 < width t ∧ width t < 1 / 4 := by
  refine ⟨(zetaPoleReserveZeroMargin_bounds t).1.trans_le (reserve_width_le t), ?_⟩
  exact max_lt (zetaPoleReserveZeroMargin_bounds t).2
    ((ZetaGaussianRegionUnion.width_bounds t).2.trans_lt (by norm_num))

/-- Below the Gaussian threshold its entire physical cap lies inside the
older signed-pole exclusion. No Gaussian analytic estimate is used there. -/
theorem gaussian_cap_lt_reserve_of_low_height {t : ℝ} (ht : |t| ≤ 1000000) :
    (1 / 40500 : ℝ) < zetaPoleReserveZeroMargin t := by
  have hlog : Real.log (|t| + 2) ≤ 20 := by
    have hm := Real.log_le_log (by positivity : 0 < |t| + 2)
      (show |t| + 2 ≤ (2 : ℝ) ^ 20 by norm_num; linarith)
    rw [Real.log_pow] at hm
    have htwo : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num at hm
    linarith
  have hsmall : (1 / 40500 : ℝ) < zetaSignedPoleZeroMargin t := by
    unfold zetaSignedPoleZeroMargin
    apply (lt_div_iff₀ (zetaSignedPole_denominator_pos t)).mpr
    linarith
  exact hsmall.trans_le (zetaSignedPole_margin_le_poleReserve t)

/-- The whole Gaussian width is strictly smaller than the existing reserve
below its starting height. -/
theorem gaussian_lt_reserve_of_low_height {t : ℝ} (ht : |t| ≤ 1000000) :
    ZetaGaussianRegionUnion.width t < zetaPoleReserveZeroMargin t :=
  (ZetaGaussianRegionUnion.width_bounds t).2.trans_lt
    (gaussian_cap_lt_reserve_of_low_height ht)

/-- The combined width equals the reserve width throughout the entire
range below the Gaussian starting height, including the endpoint. -/
theorem width_eq_reserve_of_low_height {t : ℝ} (ht : |t| ≤ 1000000) :
    width t = zetaPoleReserveZeroMargin t :=
  max_eq_left (gaussian_lt_reserve_of_low_height ht).le

/-- Literal nontrivial zeros obey the complete explicit right-edge
exclusion at every height. All analytic inputs have been discharged. -/
theorem exact_margin (ρ : NontrivialZetaZero) : width ρ.1.im < 1 - ρ.1.re := by
  by_cases ht : |ρ.1.im| ≤ 1000000
  · rw [width_eq_reserve_of_low_height ht]
    exact zetaPoleReserve_margin_lt_one_sub_re ρ
  · exact max_lt (zetaPoleReserve_margin_lt_one_sub_re ρ)
      (ZetaGaussianRegionUnion.exact_margin ρ (le_of_lt (lt_of_not_ge ht)))

/-- Both strip edges retain all explicit coverage, with no height premise. -/
theorem exact_strip (ρ : NontrivialZetaZero) :
    width ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - width ρ.1.im := by
  by_cases ht : |ρ.1.im| ≤ 1000000
  · rw [width_eq_reserve_of_low_height ht]
    exact nontrivialZetaZero_mem_poleReserve_strip ρ
  · have hG := ZetaGaussianRegionUnion.exact_strip ρ (le_of_lt (lt_of_not_ge ht))
    refine ⟨max_lt (zetaPoleReserve_margin_lt_re ρ) hG.1, ?_⟩
    linarith [exact_margin ρ]

/-- Literal zeta is nonzero on the complete closed right edge at every
ordinate. The pole at one is excluded explicitly. -/
theorem nonvanishing (s : ℂ) (hs1 : s ≠ 1)
    (hσ : 1 - width s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [(width_bounds s.im).2]
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let ρ : NontrivialZetaZero := ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have h := exact_margin ρ
  change width s.im < 1 - s.re at h
  linarith

/-- An exact elementary formula exposes every existing reserve and
Gaussian branch without inserting a literature width as an assumption. -/
theorem width_eq_max (t : ℝ) :
    width t = max
      (max (792 / (7625 * Real.log (|t| + 2) - 2000))
        (min (4 / 39) (4752 / (45750 * max (13 / 10) (Real.log (|t| + 2)) - 35725))))
      (max
        (min (1 / 450000) (221 / (250 * ZetaGaussianRetainedRegion.heightCost
          (ZetaNearOneBudgetLimit.scale t))))
        (min (1 / 40500) (1547 / (1800 * ZetaGaussianExpandedRegion.heightCost
          (ZetaNearOneBudgetLimit.scale t))))) := by
  by_cases hL : 1 ≤ ZetaNearOneBudgetLimit.scale t
  · rw [width, zetaPoleReserveZeroMargin, zetaSignedPoleZeroMargin,
      zetaPoleReserveFixedMargin_eq, ZetaGaussianRegionUnion.width_eq_max_min hL]
  · have hlog : Real.log (|t| + 2) < 1 := lt_of_not_ge hL
    have habs := (Real.log_lt_iff_lt_exp (by positivity : 0 < |t| + 2)).mp hlog
    have ht : |t| ≤ 1000000 := by linarith [Real.exp_one_lt_d9]
    have hR : max (792 / (7625 * Real.log (|t| + 2) - 2000))
        (min (4 / 39) (4752 / (45750 * max (13 / 10) (Real.log (|t| + 2)) - 35725))) =
        zetaPoleReserveZeroMargin t := by
      rw [zetaPoleReserveZeroMargin, zetaSignedPoleZeroMargin, zetaPoleReserveFixedMargin_eq]
    rw [width_eq_reserve_of_low_height ht, hR]
    symm
    apply max_eq_left
    apply le_trans (max_le ((min_le_left _ _).trans (by norm_num : (1 / 450000 : ℝ) ≤ 1 / 40500))
      (min_le_left _ _))
    exact (gaussian_cap_lt_reserve_of_low_height ht).le

/-- The certified comparison interval transfers to the complete displayed
width, and literal nonvanishing uses that entire larger closed edge. -/
theorem nonvanishing_and_comparison (s : ℂ) {L : ℝ}
    (hL : ZetaGaussianBandFrontier.crossover < L)
    (hLu : L ≤ ZetaGaussianBandFrontier.ceiling)
    (ht : |s.im| = Real.exp L) (hσ : 1 - width s.im ≤ s.re) :
    riemannZeta s ≠ 0 ∧ ZetaGaussianBandFrontier.benchmarkWidth L < width s.im := by
  obtain ⟨hh, hscale⟩ := ZetaGaussianBandFrontier.exp_height_mem_band hL.le hLu
  have hh' : 1000000 ≤ |s.im| := by simpa only [ht, abs_of_pos (Real.exp_pos L)] using hh
  have he : ZetaNearOneBudgetLimit.scale s.im =
      ZetaNearOneBudgetLimit.scale (Real.exp L) := by
    simp only [ZetaNearOneBudgetLimit.scale, ZetaNearOneLogProfile.height,
      ht, abs_of_pos (Real.exp_pos L)]
  have hp : ZetaGaussianRetainedRegion.explicitWidth s.im = 1 / 450000 :=
    ZetaGaussianRetainedRegion.explicitWidth_eq_plateau
      (ZetaGaussianBandBudget.scale_lower hh') (by rw [he]; linarith)
  have hm : (1 / 450000 : ℝ) ≤ width s.im := by
    rw [← hp]
    exact (ZetaGaussianRegionUnion.previous_width_le s.im).trans (gaussian_width_le s.im)
  refine ⟨nonvanishing s (by intro hs; norm_num [hs] at hh') hσ, ?_⟩
  exact ((ZetaGaussianBandFrontier.benchmarkWidth_lt_iff
    (ZetaGaussianBandFrontier.crossover_spec.1.trans hL.le)).mpr hL).trans_le hm

/-- The entire logarithmic eventual family is retained with its original
coefficient-dependent threshold; the explicit component needs no threshold. -/
theorem union_with_eventual {A : ℝ} (hA : 0 < A)
    (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) < ρ.1.re ∧
        ρ.1.re < 1 - max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) := by
  obtain ⟨T, hT, hz⟩ := ZetaLogLogZeroFree.exists_eventual_strip hA hAlim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ
  obtain ⟨ha, hb⟩ := hz ρ hρ
  obtain ⟨hc, hd⟩ := exact_strip ρ
  refine ⟨max_lt ha hc, ?_⟩
  have hm : max (ZetaLogLogWidth.width A |ρ.1.im|) (width ρ.1.im) <
      1 - ρ.1.re := max_lt (by linarith) (by linarith)
  linarith

end
end RiemannGaussian.ZetaUnifiedZeroFree
