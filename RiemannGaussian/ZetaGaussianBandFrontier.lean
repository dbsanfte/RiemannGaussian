/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandComparison

/-!
# Exact crossover and ceiling for the Gaussian band comparison

The crossover is the unique large solution of
`(981/50)*L = 450000*log L`. The ceiling in ordinary logarithmic height is
exactly `log (exp 320000 - 2)`. The comparison keeps both endpoints and
distinguishes equality at the crossover from strict improvement above it.
All comparison functions are mathematical expressions; no external
zero-free theorem is assumed by this module.
-/

namespace RiemannGaussian.ZetaGaussianBandFrontier
noncomputable section
open ZetaGaussianBandExclusion
open ZetaNearOneBudgetLimit (scale)

/-- Exact signed difference deciding the Littlewood width comparison. -/
def crossoverGap (L : ℝ) : ℝ := (981 / 50) * L - 450000 * Real.log L

private theorem log_lower {L : ℝ} (hL : 250000 ≤ L) : 12 ≤ Real.log L := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < L)).mpr
  have h := pow_le_pow_left₀ (Real.exp_pos 1).le
    (show Real.exp 1 ≤ (11 / 4 : ℝ) by linarith [Real.exp_one_lt_d9]) 12
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

private theorem log_upper {L : ℝ} (hL : 0 < L) (hL' : L ≤ 320000) :
    Real.log L ≤ 13 := by
  apply (Real.log_le_iff_le_exp hL).mpr
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10)
    (show (27 / 10 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 13
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

/-- The comparison gap is strictly increasing on the complete large-height
branch, so a root specifies an exact crossover rather than a sample. -/
theorem crossoverGap_strictMonoOn : StrictMonoOn crossoverGap (Set.Ici 250000) := by
  intro x hx y _ hxy
  have hxp : 0 < x := by change 250000 ≤ x at hx; linarith
  have hyp : 0 < y := hxp.trans hxy
  have hlog := Real.log_le_sub_one_of_pos (div_pos hyp hxp)
  rw [Real.log_div hyp.ne' hxp.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_right hlog hxp.le
  simp only [sub_mul, div_mul_cancel₀ _ hxp.ne', one_mul] at hm
  have hprod := mul_pos (sub_pos.mpr hxy)
    (show (0 : ℝ) < (981 / 50) * x - 450000 by change 250000 ≤ x at hx; linarith)
  unfold crossoverGap
  apply (mul_lt_mul_iff_right₀ hxp).mp
  nlinarith only [hm, hprod]

private theorem gap_left : crossoverGap 250000 < 0 := by
  have h := log_lower (L := 250000) (by norm_num)
  unfold crossoverGap
  linarith

private theorem gap_right : 0 < crossoverGap 300000 := by
  have h := log_upper (L := 300000) (by norm_num) (by norm_num)
  unfold crossoverGap
  linarith

/-- There is exactly one zero of the comparison gap on the large branch;
existence is proved by continuity, with exact rational bracketing. -/
theorem existsUnique_crossover : ∃! L : ℝ, 250000 ≤ L ∧ crossoverGap L = 0 := by
  have hc : ContinuousOn crossoverGap (Set.Icc 250000 300000) :=
    (continuous_const.mul continuous_id).continuousOn.sub
      (continuousOn_const.mul (Real.continuousOn_log.mono (by
        intro x hx
        exact ne_of_gt (by have := hx.1; linarith))))
  obtain ⟨L, hL, heq⟩ := intermediate_value_Icc (by norm_num : (250000 : ℝ) ≤ 300000)
    hc (show (0 : ℝ) ∈ Set.Icc (crossoverGap 250000) (crossoverGap 300000) from
      ⟨gap_left.le, gap_right.le⟩)
  refine ⟨L, ⟨hL.1, heq⟩, ?_⟩
  intro y hy
  exact crossoverGap_strictMonoOn.injOn hy.1 hL.1 (hy.2.trans heq.symm)

/-- The exact large Littlewood crossover, selected from its proved unique
existence. Its defining equation, rather than a decimal, fixes the endpoint. -/
def crossover : ℝ := Classical.choose existsUnique_crossover.exists

/-- The selected crossover lies on the monotone branch and has zero gap. -/
theorem crossover_spec : 250000 ≤ crossover ∧ crossoverGap crossover = 0 :=
  Classical.choose_spec existsUnique_crossover.exists

/-- Exact equation defining the crossover for the denominator `981/50`. -/
theorem crossover_equation : (981 / 50 : ℝ) * crossover = 450000 * Real.log crossover :=
  sub_eq_zero.mp crossover_spec.2

/-- Exact rational bracketing; neither endpoint is itself the crossover. -/
theorem crossover_bounds : 250000 < crossover ∧ crossover < 300000 := by
  constructor
  · by_contra h
    have heq : crossover = 250000 := le_antisymm (not_lt.mp h) crossover_spec.1
    have hz := crossover_spec.2
    rw [heq] at hz
    linarith [gap_left]
  · by_contra h
    have hg := crossoverGap_strictMonoOn.monotoneOn
      (show (300000 : ℝ) ∈ Set.Ici 250000 by norm_num) crossover_spec.1 (not_lt.mp h)
    rw [crossover_spec.2] at hg
    linarith [gap_right]

/-- A narrower exact enclosure from elementary logarithm inequalities.
The displayed decimal approximation is not used anywhere in the proof. -/
theorem crossover_refined_bounds : 288000 < crossover ∧ crossover < 289000 := by
  have htwo : Real.log (262144 : ℝ) = 18 * Real.log 2 := by
    rw [show (262144 : ℝ) = (2 : ℝ) ^ (18 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hleft : crossoverGap 288000 < 0 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 262144 / 288000)
    rw [Real.log_div (by norm_num) (by norm_num), htwo] at h
    unfold crossoverGap
    linarith [Real.log_two_gt_d9]
  have hright : 0 < crossoverGap 289000 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 289000 / 262144)
    rw [Real.log_div (by norm_num) (by norm_num), htwo] at h
    unfold crossoverGap
    linarith [Real.log_two_lt_d9]
  constructor
  · by_contra h
    have hg := crossoverGap_strictMonoOn.monotoneOn crossover_spec.1
      (show (288000 : ℝ) ∈ Set.Ici 250000 by norm_num) (not_lt.mp h)
    rw [crossover_spec.2] at hg
    linarith
  · by_contra h
    have hg := crossoverGap_strictMonoOn.monotoneOn
      (show (289000 : ℝ) ∈ Set.Ici 250000 by norm_num) crossover_spec.1 (not_lt.mp h)
    rw [crossover_spec.2] at hg
    linarith

/-- A nonnegative gap is equivalent to being at or beyond the exact
crossover, for every ordinate on the large branch. -/
theorem crossoverGap_nonneg_iff {L : ℝ} (hL : 250000 ≤ L) :
    0 ≤ crossoverGap L ↔ crossover ≤ L := by
  rw [← crossover_spec.2]
  exact crossoverGap_strictMonoOn.le_iff_le crossover_spec.1 hL

/-- A positive gap is equivalent to being strictly past the crossover. -/
theorem crossoverGap_pos_iff {L : ℝ} (hL : 250000 ≤ L) :
    0 < crossoverGap L ↔ crossover < L := by
  rw [← crossover_spec.2]
  exact crossoverGap_strictMonoOn.lt_iff_lt crossover_spec.1 hL

/-- Exact ceiling in `L = log |t|`, including the original height's `+2`. -/
def ceiling : ℝ := Real.log (Real.exp 320000 - 2)

private theorem exp_ceiling_pos : 0 < Real.exp 320000 - 2 := by
  linarith [Real.add_one_le_exp (320000 : ℝ)]

/-- The ordinary exponential height at the ceiling retains exactly the
two-unit difference from the enlarged exponential height. -/
theorem exp_ceiling : Real.exp ceiling + 2 = Real.exp 320000 := by
  rw [ceiling, Real.exp_log exp_ceiling_pos]
  ring

/-- The ceiling is above the old comparison interval and strictly below
`320000`; the latter cannot be substituted for it as a closed endpoint. -/
theorem ceiling_bounds : 310000 < ceiling ∧ ceiling < 320000 := by
  constructor
  · apply (Real.lt_log_iff_exp_lt exp_ceiling_pos).mpr
    have hshift : Real.exp 310000 + 2 < Real.exp (310000 + 1) := by
      rw [Real.exp_add]
      nlinarith [Real.add_one_le_exp (310000 : ℝ), Real.exp_one_gt_d9]
    have hm := Real.exp_le_exp.mpr (show (310000 + 1 : ℝ) ≤ 320000 by norm_num)
    linarith
  · apply (Real.log_lt_iff_lt_exp exp_ceiling_pos).mpr
    linarith

/-- The Gaussian theorem's upper height condition is exactly equivalent
to this ceiling in ordinary logarithmic height, with no rounding. -/
theorem scale_exp_le_iff (L : ℝ) : scale (Real.exp L) ≤ 320000 ↔ L ≤ ceiling := by
  unfold scale ZetaNearOneLogProfile.height ceiling
  rw [abs_of_pos (Real.exp_pos L), Real.log_le_iff_le_exp (by positivity),
    Real.le_log_iff_exp_le exp_ceiling_pos]
  constructor <;> intro h <;> linarith

/-- Every height from the exact crossover through the exact ceiling is
in the actual proved zero-free band, including both endpoints. -/
theorem exp_height_mem_band {L : ℝ} (hL : crossover ≤ L) (hL' : L ≤ ceiling) :
    1000000 ≤ |Real.exp L| ∧ scale (Real.exp L) ≤ 320000 := by
  refine ⟨?_, (scale_exp_le_iff L).mpr hL'⟩
  rw [abs_of_pos (Real.exp_pos L)]
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 20
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have hm := Real.exp_le_exp.mpr (show (20 : ℝ) ≤ L by linarith [crossover_bounds.1])
  linarith

/-- Literal zeta nonvanishing over the full closed crossover-to-ceiling
interval, for either sign of the imaginary part. -/
theorem nonvanishing_at_exp (s : ℂ) {L : ℝ} (hL : crossover ≤ L) (hL' : L ≤ ceiling)
    (ht : |s.im| = Real.exp L) (hσ : 1 - 1 / 450000 ≤ s.re) : riemannZeta s ≠ 0 := by
  obtain ⟨hh, hs⟩ := exp_height_mem_band hL hL'
  apply nonvanishing s (by simpa [ht, abs_of_pos (Real.exp_pos L)] using hh) ?_ hσ
  simpa only [scale, ZetaNearOneLogProfile.height, ht, abs_of_pos (Real.exp_pos L)] using hs

/-- Classical width with its full denominator parameter retained. -/
def classicalWidth (C L : ℝ) : ℝ := 1 / (C * L)

/-- Littlewood width in ordinary logarithmic height. -/
def littlewoodWidth (C L : ℝ) : ℝ := Real.log L / (C * L)

/-- Vinogradov--Korobov width with its denominator retained. -/
def vkWidth (C L : ℝ) : ℝ := 1 / (C * L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ))

/-- Every classical denominator at least two is strictly beaten across
the entire large branch. This includes the listed classical benchmarks. -/
theorem classicalWidth_lt {C L : ℝ} (hC : 2 ≤ C) (hL : 250000 ≤ L) :
    classicalWidth C L < (1 / 450000 : ℝ) := by
  unfold classicalWidth
  apply one_div_lt_one_div_of_lt (by norm_num)
  have h := mul_le_mul hC hL (by norm_num : (0 : ℝ) ≤ 250000) (by linarith : 0 ≤ C)
  linarith

/-- The exact Littlewood comparison has a closed crossover endpoint. -/
theorem littlewoodWidth_le_iff {L : ℝ} (hL : 250000 ≤ L) :
    littlewoodWidth (981 / 50) L ≤ (1 / 450000 : ℝ) ↔ crossover ≤ L := by
  rw [← crossoverGap_nonneg_iff hL]
  unfold littlewoodWidth crossoverGap
  rw [div_le_iff₀ (by positivity : 0 < (981 / 50 : ℝ) * L)]
  constructor <;> intro h <;> linarith

/-- Strict improvement holds precisely above the exact crossover. -/
theorem littlewoodWidth_lt_iff {L : ℝ} (hL : 250000 ≤ L) :
    littlewoodWidth (981 / 50) L < (1 / 450000 : ℝ) ↔ crossover < L := by
  rw [← crossoverGap_pos_iff hL]
  unfold littlewoodWidth crossoverGap
  rw [div_lt_iff₀ (by positivity : 0 < (981 / 50 : ℝ) * L)]
  constructor <;> intro h <;> linarith

/-- The two widths are equal at the exact crossover. -/
theorem littlewoodWidth_crossover : littlewoodWidth (981 / 50) crossover = 1 / 450000 := by
  apply le_antisymm ((littlewoodWidth_le_iff crossover_spec.1).mpr le_rfl)
  exact le_of_not_gt (by rw [littlewoodWidth_lt_iff crossover_spec.1]; exact lt_irrefl _)

/-- Every larger Littlewood denominator is dominated by the same exact
comparison, without selecting another family or rounding the endpoint. -/
theorem littlewoodWidth_le {C L : ℝ} (hC : 981 / 50 ≤ C) (hL : crossover ≤ L) :
    littlewoodWidth C L ≤ (1 / 450000 : ℝ) := by
  have hLp : 0 < L := by linarith [crossover_bounds.1]
  apply le_trans ?_ ((littlewoodWidth_le_iff (crossover_spec.1.trans hL)).mpr hL)
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith [crossover_bounds.1]))
    (by positivity : 0 < (981 / 50 : ℝ) * L) (mul_le_mul_of_nonneg_right hC hLp.le)

/-- Above the exact crossover every larger Littlewood denominator gives
strict improvement too. -/
theorem littlewoodWidth_lt {C L : ℝ} (hC : 981 / 50 ≤ C) (hL : crossover < L) :
    littlewoodWidth C L < (1 / 450000 : ℝ) := by
  have hLp : 0 < L := by linarith [crossover_bounds.1]
  apply lt_of_le_of_lt ?_ ((littlewoodWidth_lt_iff (crossover_spec.1.trans hL.le)).mpr hL)
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith [crossover_bounds.1]))
    (by positivity : 0 < (981 / 50 : ℝ) * L) (mul_le_mul_of_nonneg_right hC hLp.le)

/-- All listed explicit Vinogradov--Korobov denominators are strictly
beaten even before the Littlewood crossover, on the whole large branch. -/
theorem vkWidth_lt {C L : ℝ} (hC : 2567 / 50 ≤ C) (hL : 250000 ≤ L) :
    vkWidth C L < (1 / 450000 : ℝ) := by
  have hpos : 0 < L := by linarith
  have hlog := log_lower hL
  have hlogpos : 0 < Real.log L := by linarith
  have hp : (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hq : ((Real.log L) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
    norm_num
  have hlower : (3900 : ℝ) ≤ L ^ (2 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3900)
      (Real.rpow_nonneg hpos.le _) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hp]
    nlinarith
  have hllower : (9 / 4 : ℝ) ≤ (Real.log L) ^ (1 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 4)
      (Real.rpow_nonneg hlogpos.le _) (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hq]
    norm_num
    linarith
  have hm := mul_le_mul hlower hllower (by norm_num : (0 : ℝ) ≤ 9 / 4)
    (Real.rpow_nonneg hpos.le _)
  have hc := mul_le_mul_of_nonneg_left hm (show 0 ≤ C by linarith)
  unfold vkWidth
  apply one_div_lt_one_div_of_lt (by norm_num)
  nlinarith only [hc, hC]

/-- Pointwise union of the three advertised comparison functions.
This definition is a width envelope, not an external zero-free axiom. -/
def benchmarkWidth (L : ℝ) : ℝ :=
  max (classicalWidth (24297 / 5000) L)
    (max (littlewoodWidth (981 / 50) L) (vkWidth (2567 / 50) L))

/-- The complete benchmark envelope is at most the Gaussian width if
and only if the exact crossover has been reached. -/
theorem benchmarkWidth_le_iff {L : ℝ} (hL : 250000 ≤ L) :
    benchmarkWidth L ≤ (1 / 450000 : ℝ) ↔ crossover ≤ L := by
  simp only [benchmarkWidth, max_le_iff]
  constructor
  · exact fun h ↦ (littlewoodWidth_le_iff hL).mp h.2.1
  · exact fun h ↦ ⟨(classicalWidth_lt (by norm_num) hL).le,
      (littlewoodWidth_le_iff hL).mpr h, (vkWidth_lt (by norm_num) hL).le⟩

/-- Strict domination of the whole advertised envelope holds exactly
past the crossover, not at it. -/
theorem benchmarkWidth_lt_iff {L : ℝ} (hL : 250000 ≤ L) :
    benchmarkWidth L < (1 / 450000 : ℝ) ↔ crossover < L := by
  simp only [benchmarkWidth, max_lt_iff]
  constructor
  · exact fun h ↦ (littlewoodWidth_lt_iff hL).mp h.2.1
  · exact fun h ↦ ⟨classicalWidth_lt (by norm_num) hL,
      (littlewoodWidth_lt_iff hL).mpr h, vkWidth_lt (by norm_num) hL⟩

/-- Exact crossover-to-ceiling interval for simultaneous band eligibility
and weak domination of the advertised literature envelope. -/
theorem comparison_interval_iff {L : ℝ} (hL : 250000 ≤ L) :
    (scale (Real.exp L) ≤ 320000 ∧ benchmarkWidth L ≤ 1 / 450000) ↔
      L ∈ Set.Icc crossover ceiling := by
  rw [scale_exp_le_iff, benchmarkWidth_le_iff hL]
  exact and_comm

/-- The strict improvement interval is open at the crossover and closed
at the true ceiling. -/
theorem strict_comparison_interval_iff {L : ℝ} (hL : 250000 ≤ L) :
    (scale (Real.exp L) ≤ 320000 ∧ benchmarkWidth L < 1 / 450000) ↔
      L ∈ Set.Ioc crossover ceiling := by
  rw [scale_exp_le_iff, benchmarkWidth_lt_iff hL]
  exact and_comm

/-- Actual zero exclusion and strict benchmark improvement together over
the entire exact interval; every height hypothesis is discharged. -/
theorem nonvanishing_and_comparison (s : ℂ) {L : ℝ} (hL : crossover < L) (hL' : L ≤ ceiling)
    (ht : |s.im| = Real.exp L) (hσ : 1 - 1 / 450000 ≤ s.re) :
    riemannZeta s ≠ 0 ∧ benchmarkWidth L < 1 / 450000 :=
  ⟨nonvanishing_at_exp s hL.le hL' ht hσ,
    (benchmarkWidth_lt_iff (crossover_spec.1.trans hL.le)).mpr hL⟩

end
end RiemannGaussian.ZetaGaussianBandFrontier
