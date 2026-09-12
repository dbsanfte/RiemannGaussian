/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandExclusion
import RiemannGaussian.ZetaLogLogZeroFree

/-!
# Explicit height overlap and comparisons of zero-free widths

The Gaussian band contains every height exp(L) for 300000 <= L <= 310000.
On this same interval its width strictly exceeds three stated comparison
functions, with denominators 4.8594, 19.62 and 51.34. These are inequalities
between explicit functions, not imported proofs of published regions or a
claim that every result in the literature has been compared. The existing
proved eventual region and the new band retain their union on overlaps.
-/

namespace RiemannGaussian.ZetaGaussianBandComparison
noncomputable section
open ZetaGaussianBandExclusion
open ZetaNearOneBudgetLimit (scale)

private theorem log_bounds {L : ℝ} (hL : 300000 ≤ L) (hL' : L ≤ 310000) :
    12 ≤ Real.log L ∧ Real.log L ≤ 13 := by
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
      (show (27 / 10 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 13
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith

/-- The comparison interval is wholly inside the actual proved band;
the enlarged logarithmic height is bounded without dropping its plus two. -/
theorem exp_height_mem_band {L : ℝ} (hL : 300000 ≤ L) (hL' : L ≤ 310000) :
    1000000 ≤ |Real.exp L| ∧ scale (Real.exp L) ≤ 320000 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
    (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 20
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have hexp : 1000000 ≤ Real.exp L := by
    have hm := Real.exp_le_exp.mpr (show (20 : ℝ) ≤ L by linarith)
    linarith
  have hshift : Real.exp L + 2 ≤ Real.exp (L + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.exp_one_gt_d9]
  have hs : scale (Real.exp L) ≤ L + 1 := by
    unfold scale ZetaNearOneLogProfile.height
    rw [abs_of_pos (Real.exp_pos L)]
    exact (Real.log_le_iff_le_exp (by positivity)).mpr hshift
  constructor
  · simpa only [abs_of_pos (Real.exp_pos L)] using hexp
  · linarith

/-- Literal zeta nonvanishing throughout the explicit comparison
interval, at both signs of height through the absolute-value premise. -/
theorem nonvanishing_at_exp (s : ℂ) {L : ℝ} (hL : 300000 ≤ L) (hL' : L ≤ 310000)
    (ht : |s.im| = Real.exp L) (hσ : 1 - 1 / 450000 ≤ s.re) : riemannZeta s ≠ 0 := by
  obtain ⟨hh, hs⟩ := exp_height_mem_band hL hL'
  apply nonvanishing s (by simpa [ht, abs_of_pos (Real.exp_pos L)] using hh) ?_ hσ
  simpa only [scale, ZetaNearOneLogProfile.height, ht, abs_of_pos (Real.exp_pos L)] using hs

/-- The width exceeds the classical comparison with exact denominator
24297/5000 throughout the matching height interval. -/
theorem classical_width_lt {L : ℝ} (hL : 300000 ≤ L) :
    1 / ((24297 / 5000 : ℝ) * L) < (1 / 450000 : ℝ) := by
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith

/-- The width exceeds the stronger reported Littlewood comparison,
with exact denominator 981/50, on the entire matching interval. -/
theorem littlewood_width_lt {L : ℝ} (hL : 300000 ≤ L) (hL' : L ≤ 310000) :
    Real.log L / ((981 / 50 : ℝ) * L) < (1 / 450000 : ℝ) := by
  have hl := (log_bounds hL hL').2
  apply (div_lt_iff₀ (by positivity : 0 < (981 / 50 : ℝ) * L)).mpr
  linarith

/-- The width exceeds the stronger reported Vinogradov--Korobov
comparison, with exact denominator 2567/50, at the same heights. -/
theorem vinogradov_korobov_width_lt {L : ℝ} (hL : 300000 ≤ L) (hL' : L ≤ 310000) :
    1 / ((2567 / 50 : ℝ) * L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ)) <
      (1 / 450000 : ℝ) := by
  have hpos : 0 < L := by linarith
  have hlog := (log_bounds hL hL').1
  have hlogpos : 0 < Real.log L := by linarith
  have hp : (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hq : ((Real.log L) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
    norm_num
  have hlower : (4400 : ℝ) ≤ L ^ (2 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 4400)
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
  apply one_div_lt_one_div_of_lt (by norm_num)
  nlinarith only [hm]

/-- On every overlap, the new band and the existing eventual theorem
give their larger width, preserving both original height hypotheses. -/
theorem union_with_eventual {A : ℝ} (hA : 0 < A) (hAlim : A < ZetaLogLogZeroFree.coefficientLimit) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      1000000 ≤ |ρ.1.im| → scale ρ.1.im ≤ 320000 →
      max (ZetaLogLogWidth.width A |ρ.1.im|) (1 / 450000) < ρ.1.re ∧
        ρ.1.re < 1 - max (ZetaLogLogWidth.width A |ρ.1.im|) (1 / 450000) := by
  obtain ⟨T, hT, hz⟩ := ZetaLogLogZeroFree.exists_eventual_strip hA hAlim
  refine ⟨T, hT, ?_⟩
  intro ρ hρ ht hL
  obtain ⟨ha, hb⟩ := hz ρ hρ
  obtain ⟨hc, hd⟩ := exact_strip ρ ht hL
  refine ⟨max_lt ha hc, ?_⟩
  have hm : max (ZetaLogLogWidth.width A |ρ.1.im|) (1 / 450000) < 1 - ρ.1.re :=
    max_lt (by linarith) (by linarith)
  linarith

end
end RiemannGaussian.ZetaGaussianBandComparison
