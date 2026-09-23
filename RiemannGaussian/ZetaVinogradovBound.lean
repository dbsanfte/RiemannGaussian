/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNearOneBudget
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Complete near-one zeta bounds from the actual Vinogradov moments

Every dyadic scale is covered by an unconditional arithmetic estimate.
The complete eta reconstruction pays both prefixes, the endpoint, the
tail and the division factor. At the explicit height threshold, zeta
therefore has a cubic-index height exponent on a quadratic-index line.
Conjugation supplies both signs of height. This is an actual zeta growth
bound, not a zero-free theorem or a numerical benchmark comparison.
-/

namespace RiemannGaussian.ZetaVinogradovBound
noncomputable section
open DirichletDyadicBlocks ZetaDyadicTruncation
open VinogradovNearOneBudget VinogradovScaleSelection
open scoped ComplexConjugate

/-- A uniform bound on every actual canonical block pays the complete
zeta reconstruction, with its exact count and line displacement. -/
theorem of_block_bound {s : ℂ} (hσ : 0 < s.re) (hσ1 : s.re < 1)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ j ≤ depth s, ‖block s j‖ ≤ B) :
    ‖riemannZeta s‖ ≤ 6 * (((depth s + 1 : ℕ) : ℝ) * B + 1) / (1 - s.re) := by
  let C : ℝ := ((depth s + 1 : ℕ) : ℝ) * B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsums : ∀ J ≤ depth s + 1, ‖∑ j ∈ Finset.range J, block s j‖ ≤ C := by
    intro J hJ
    calc
      _ ≤ ∑ j ∈ Finset.range J, ‖block s j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range J, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact hb j (by have hh := Finset.mem_range.mp hj; omega)
      _ = (J : ℝ) * B := by simp
      _ ≤ C := mul_le_mul_of_nonneg_right (by exact_mod_cast hJ) hB
  have htwo : (2 : ℝ) ^ (1 - s.re) ≤ 2 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - s.re ≤ 1)).trans_eq
    exact Real.rpow_one _
  have he : ‖zetaPrimeFeature s (2 ^ (depth s + 1))‖ ≤ 1 := by
    rw [norm_zetaPrimeFeature, weight_eq_rpow _ (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))) (by linarith)
  have hweighted : ‖2 * zetaPrimeFeature s 2 *
      (∑ j ∈ Finset.range (depth s), block s j)‖ ≤ 2 * C := by
    rw [norm_mul, feature_eq_cpow s (by norm_num), Nat.cast_ofNat,
      norm_two_mul_two_cpow_neg]
    exact (mul_le_mul_of_nonneg_left (hsums (depth s) (by omega)) (by positivity)).trans
      (mul_le_mul_of_nonneg_right htwo hC)
  have hfinite : ‖(∑ j ∈ Finset.range (depth s + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range (depth s), block s j) -
          zetaPrimeFeature s (2 ^ (depth s + 1))‖ ≤ 3 * C + 1 := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add ((norm_sub_le _ _).trans (add_le_add
      (hsums (depth s + 1) le_rfl) hweighted)) he).trans
    linarith
  have htail : (((2 * 2 ^ depth s + 1 : ℕ) : ℝ) ^ (-s.re)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by linarith)
  have h := (le_div_iff₀ (factor_lower_pos hσ1)).mp
    (zeta_norm_le hσ hσ1 (depth s) (depth_scale s))
  have hgap : (1 - s.re) / 2 ≤ (2 : ℝ) ^ (1 - s.re) - 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hg := Real.add_one_le_exp (Real.log 2 * (1 - s.re))
    nlinarith [Real.log_two_gt_d9]
  have hg := mul_le_mul_of_nonneg_right hgap (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (by linarith : 0 < 1 - s.re)).mpr
  change ‖riemannZeta s‖ * (1 - s.re) ≤ 6 * (C + 1)
  nlinarith

/-- The full zeta function has an unconditional cubic-index height
exponent throughout the strip from the selected line to one. -/
theorem bound_strip (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re < 1)
    (ht : (heightThreshold n : ℝ) ≤ s.im) :
    ‖riemannZeta s‖ ≤ 32768 * s.im ^ growth n * Real.log s.im / (1 - s.re) := by
  have hσ : 0 < s.re := by linarith [(line_bounds n).1]
  have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have ht2 : 2 ≤ s.im := by linarith
  have h := of_block_bound hσ hσ1 (by positivity : 0 ≤ 512 * s.im ^ growth n)
    (fun j hj => canonical_block_bound n hn hline hσ1.le ht hj)
  have hc := ZetaNearOneLineBudget.canonical_count_le hσ.le hσ1.le ht2
  have hp : 1 ≤ s.im ^ growth n :=
    Real.one_le_rpow (by linarith) (growth_pos (by omega : 1 ≤ n)).le
  have hd : 1 ≤ ((depth s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hone : 1 ≤ ((depth s + 1 : ℕ) : ℝ) * s.im ^ growth n := by
    have hh := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ ((depth s + 1 : ℕ) : ℝ) by positivity)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ s.im ^ growth n)
  have hlog : 0 ≤ Real.log s.im := (Real.log_pos (by linarith : 1 < s.im)).le
  have hprod : 0 ≤ s.im ^ growth n * Real.log s.im := mul_nonneg (by linarith) hlog
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 1 - s.re)
  nlinarith

/-- On the selected line the denominator is its explicit quadratic-index
displacement, and every other factor is already paid. -/
theorem bound (n : ℕ) (hn : 12 ≤ n) {s : ℂ} (hline : s.re = line n)
    (ht : (heightThreshold n : ℝ) ≤ s.im) :
    ‖riemannZeta s‖ ≤ 32768 * s.im ^ growth n * Real.log s.im / delta n := by
  have h := bound_strip n hn hline.ge (by rw [hline]; exact (line_bounds n).2) ht
  have hdelta : 1 - s.re = delta n := by rw [hline, line]; ring
  simpa only [hdelta] using h

/-- The complete near-one strip estimate is symmetric in the height. -/
theorem bound_strip_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ1 : s.re < 1)
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 32768 * |s.im| ^ growth n * Real.log |s.im| / (1 - s.re) := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound_strip n hn hline hσ1 ht
  · have hsneg : s.im < 0 := lt_of_not_ge hs
    have hline' : line n ≤ (conj s).re := by simpa using hline
    have hσ1' : (conj s).re < 1 := by simpa using hσ1
    have ht' : (heightThreshold n : ℝ) ≤ (conj s).im := by simpa [abs_of_neg hsneg] using ht
    have h := bound_strip n hn hline' hσ1' ht'
    simpa [abs_of_neg hsneg] using h

/-- The actual bound holds at both signs of height by the zeta
conjugation theorem, with the same explicit threshold and constants. -/
theorem bound_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ} (hline : s.re = line n)
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 32768 * |s.im| ^ growth n * Real.log |s.im| / delta n := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound n hn hline ht
  · have hsneg : s.im < 0 := lt_of_not_ge hs
    have hline' : (conj s).re = line n := by simpa using hline
    have ht' : (heightThreshold n : ℝ) ≤ (conj s).im := by simpa [abs_of_neg hsneg] using ht
    have h := bound n hn hline' ht'
    simpa [abs_of_neg hsneg] using h

/-- Throughout every interval between adjacent selected lines, the full
zeta exponent is bounded by an explicit displacement-to-three-halves
power. The threshold and eta division cost remain displayed. -/
theorem bound_band_abs (n : ℕ) (hn : 12 ≤ n) {s : ℂ}
    (hlo : line n ≤ s.re) (hhi : s.re ≤ line (n + 1))
    (ht : (heightThreshold n : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 32768 * |s.im| ^ (12288 * (1 - s.re) ^ (3 / 2 : ℝ)) *
      Real.log |s.im| / (1 - s.re) := by
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
  apply (bound_strip_abs n hn hlo hσ1 ht).trans
  apply div_le_div_of_nonneg_right _ hd.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 32768)) hlog

end
end RiemannGaussian.ZetaVinogradovBound
