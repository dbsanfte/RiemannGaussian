/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianBandFrontier

/-!
# Supplementary literature-width comparisons at the actual crossover

The intermediate Mossinghoff--Trudgian--Yang and Ford width expressions
are bounded on the complete comparison interval. The Ford leading
constant remains a parameter. Even the stated eventual VK expressions
with denominator at least 48 are smaller here, although a comparison of
functions does not evaluate the starting height of an eventual theorem.
Sources, endpoint conventions and audit limitations are recorded in
`docs/zero-free-literature-frontier.md`; no literature theorem is an axiom.
-/

namespace RiemannGaussian.ZetaGaussianLiteratureComparison
noncomputable section
open ZetaGaussianBandFrontier

/-- The published intermediate width, with its negative correction intact. -/
def intermediateWidth (L : ℝ) : ℝ :=
  (1007 / 20000) / ((27 / 164) * L + 887 / 125) -
    (349 / 10000) / ((27 / 164) * L + 887 / 125) ^ 2

/-- The Ford denominator input; `c` is the leading subconvexity constant. -/
def fordJ (c L : ℝ) : ℝ := L / 6 + Real.log L + Real.log c

/-- The Ford width with its full rational secondary terms and the
subconvexity constant retained. -/
def fordWidth (c L : ℝ) : ℝ :=
  ((2481 / 50000) - (49 / 2500) / (fordJ c L + 23 / 20)) /
    (fordJ c L + 137 / 200 + (31 / 200) * Real.log L)

/-- The entire intermediate expression is strictly smaller on the large
branch, not just at sampled points or after dropping its height dependence. -/
theorem intermediateWidth_lt {L : ℝ} (hL : 250000 ≤ L) :
    intermediateWidth L < (1 / 450000 : ℝ) := by
  have hh : 0 < (27 / 164 : ℝ) * L + 887 / 125 := by linarith
  have hmain : (1007 / 20000 : ℝ) / ((27 / 164) * L + 887 / 125) < 1 / 450000 := by
    rw [div_lt_iff₀ hh]
    linarith
  have hc : (0 : ℝ) ≤ (349 / 10000) / ((27 / 164) * L + 887 / 125) ^ 2 := by positivity
  unfold intermediateWidth
  linarith

/-- Uniform comparison for every Ford constant at least `1/2`, including
both `3` and the sharper `309/500 = 0.618`; the secondary terms remain in
the original expression. -/
theorem fordWidth_lt {c L : ℝ} (hc : 1 / 2 ≤ c) (hL : 250000 ≤ L) :
    fordWidth c L < (1 / 450000 : ℝ) := by
  have hLp : 0 < L := by linarith
  have hcp : 0 < c := by linarith
  have hlog : 1 ≤ Real.log L := by
    apply (Real.le_log_iff_exp_le hLp).mpr
    linarith [Real.exp_one_lt_d9]
  have hlogc : -1 ≤ Real.log c := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hc
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
    linarith [Real.log_two_lt_d9]
  have hJ : L / 6 ≤ fordJ c L := by unfold fordJ; linarith
  have hnum : 0 ≤ (49 / 2500 : ℝ) / (fordJ c L + 23 / 20) :=
    div_nonneg (by norm_num) (by linarith)
  have hden : 0 < fordJ c L + 137 / 200 + (31 / 200) * Real.log L := by linarith
  unfold fordWidth
  rw [div_lt_iff₀ hden]
  linarith

/-- Even VK denominators at least `48` are strictly beaten from the
crossover onward. This includes the listed eventual formulas, without
claiming that their unevaluated height thresholds lie in this band. -/
theorem eventual_vkWidth_lt {C L : ℝ} (hC : 48 ≤ C) (hL : crossover ≤ L) :
    vkWidth C L < (1 / 450000 : ℝ) := by
  have hlowerL : 288000 ≤ L := crossover_refined_bounds.1.le.trans hL
  have hpos : 0 < L := by linarith
  have hlog : 12 ≤ Real.log L := by
    apply (Real.le_log_iff_exp_le hpos).mpr
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le
      (show Real.exp 1 ≤ (11 / 4 : ℝ) by linarith [Real.exp_one_lt_d9]) 12
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith
  have hlogpos : 0 < Real.log L := by linarith
  have hp : (L ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  have hq : ((Real.log L) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = Real.log L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
    norm_num
  have hlower : (4200 : ℝ) ≤ L ^ (2 / 3 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 4200)
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

end
end RiemannGaussian.ZetaGaussianLiteratureComparison
