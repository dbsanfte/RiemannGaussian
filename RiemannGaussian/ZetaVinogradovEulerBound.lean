/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovBound
import RiemannGaussian.ZetaEulerLineBound

/-!
# Removing the eta cost from the complete Vinogradov zeta bound

The existing uniform Euler remainder reconstructs zeta from the same
original dyadic prefix. It removes the reciprocal line displacement,
improves the numerical coefficient, and includes the line Re(s)=1.
Every block is still bounded by the unconditional actual moment chain.
The explicit band-dependent starting height remains a hypothesis.
-/

namespace RiemannGaussian.ZetaVinogradovEulerBound
noncomputable section
open DirichletDyadicBlocks ZetaDyadicTruncation
open VinogradovNearOneBudget VinogradovScaleSelection
open scoped ComplexConjugate

/-- Direct Euler reconstruction gives a uniform near-one bound with no
eta denominator, including the whole one-line at admissible height. -/
theorem bound_strip (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : (heightThreshold n : ℝ) ≤ s.im) :
    ‖riemannZeta s‖ ≤ 8192 * s.im ^ growth n * Real.log s.im := by
  have hσ : 0 < s.re := by linarith [(line_bounds n).1]
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht2 : 2 ≤ s.im := by linarith
  have hprefix : ‖positivePrefix s (2 ^ (depth s + 1))‖ ≤
      ((depth s + 1 : ℕ) : ℝ) * (512 * s.im ^ growth n) := by
    rw [prefix_pow_two]
    calc
      _ ≤ ∑ j ∈ Finset.range (depth s + 1), ‖block s j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (depth s + 1), (512 * s.im ^ growth n) := by
        apply Finset.sum_le_sum
        intro j hj
        exact canonical_block_bound n hn hline hσ1 ht
          (by have hh := Finset.mem_range.mp hj; omega)
      _ = _ := by simp
  have hc := ZetaNearOneLineBudget.canonical_count_le hσ.le hσ1 ht2
  have hp : 1 ≤ s.im ^ growth n :=
    Real.one_le_rpow (by linarith) (growth_pos (by omega : 1 ≤ n)).le
  have hlog : (1 / 2 : ℝ) ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 512 * s.im ^ growth n)
  have hprod : (1 / 2 : ℝ) ≤ s.im ^ growth n * Real.log s.im := by nlinarith
  have h := ZetaEulerLineBound.norm_le_prefix_add_six hσ hσ1 ht2
  nlinarith

/-- Zeta conjugation preserves the full closed-strip bound and its
explicit starting height, without a reciprocal-displacement cost. -/
theorem bound_strip_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re ≤ 1)
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ growth n * Real.log |s.im| := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound_strip n hn hline hσ1 ht
  · have hsneg : s.im < 0 := lt_of_not_ge hs
    have hline' : line n ≤ (conj s).re := by simpa using hline
    have hσ1' : (conj s).re ≤ 1 := by simpa using hσ1
    have ht' : (heightThreshold n : ℝ) ≤ (conj s).im := by simpa [abs_of_neg hsneg] using ht
    have h := bound_strip n hn hline' hσ1' ht'
    simpa [abs_of_neg hsneg] using h

/-- The selected line has the complete cubic-index growth bound with
one coefficient independent of its distance from one. -/
theorem bound_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ} (hline : s.re = line n)
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ growth n * Real.log |s.im| :=
  bound_strip_abs n hn hline.ge (by rw [hline]; exact (line_bounds n).2.le) ht

/-- On every continuous adjacent band the actual zeta bound has an
explicit three-halves displacement exponent and no eta division. -/
theorem bound_band_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hlo : line n ≤ s.re) (hhi : s.re ≤ line (n + 1))
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 8192 * |s.im| ^ (12288 * (1 - s.re) ^ (3 / 2 : ℝ)) *
      Real.log |s.im| := by
  have hn1 : 1 ≤ n := by omega
  have hσ1 : s.re < 1 := hhi.trans_lt (line_bounds (n + 1)).2
  have hd : 0 < 1 - s.re := by linarith
  have hsucc : delta (n + 1) ≤ 1 - s.re := by dsimp only [line] at hhi; linarith
  have hdelta : delta n ≤ 4 * (1 - s.re) :=
    (delta_le_four_succ hn1).trans (mul_le_mul_of_nonneg_left hsucc (by norm_num))
  have hp := Real.rpow_le_rpow (delta_pos n).le hdelta (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hfour : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 4),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    norm_num
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hd.le, hfour] at hp
  have he : growth n ≤ 12288 * (1 - s.re) ^ (3 / 2 : ℝ) := by
    have h := growth_le_displacement_power hn1
    nlinarith
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold hn1
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht1 : 1 ≤ |s.im| := by linarith
  have hlog : 0 ≤ Real.log |s.im| := Real.log_nonneg ht1
  have hpow := Real.rpow_le_rpow_of_exponent_le ht1 he
  apply (bound_strip_abs n hn hlo hσ1.le ht).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 8192)) hlog

end
end RiemannGaussian.ZetaVinogradovEulerBound
