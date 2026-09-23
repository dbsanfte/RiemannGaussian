/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCubicDecay
import RiemannGaussian.VinogradovCubicSummation
import RiemannGaussian.ZetaEulerLineBound

/-!
# Actual VK growth with the two-thirds logarithmic factor

Summing the retained cubic profile pays the complete original Euler
prefix by log(t)^(2/3), including every small and long block. The actual
closed strip extends through Re(s)=3/2, so the entire zero-detection disc
uses the same sharper profile. The explicit starting height remains
T_(8n); no exponential-sum or moment estimate is assumed.
-/

namespace RiemannGaussian.ZetaVinogradovSummedBound
noncomputable section
open DirichletDyadicBlocks ZetaDyadicTruncation VinogradovScaleSelection
open VinogradovCubicBudget (growth growth_pos)
open VinogradovSharperBudget (delta line line_bounds)
open scoped ComplexConjugate

/-- The original canonical blocks stay below four times the height on
the entire enlarged strip through three halves. -/
theorem canonical_scale_le {s : ℂ} (hσ : 0 ≤ s.re) (hσ' : s.re ≤ 3 / 2)
    (ht : 2 ≤ s.im) {j : ℕ} (hj : j ≤ depth s) :
    ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im := by
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hσ, abs_of_nonneg (by linarith : 0 ≤ s.im)] at hn
  have hd := depth_length_lt s
  have hp : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ depth s : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hj
  linarith

/-- Euler reconstruction has a uniform remainder on the enlarged strip,
including the right-hand portion of every detection disc. -/
theorem norm_le_prefix_add_six {s : ℂ} (hσ : 0 < s.re)
    (ht : 2 ≤ s.im) :
    ‖riemannZeta s‖ ≤ ‖positivePrefix s (2 ^ (depth s + 1))‖ + 6 := by
  by_cases hs : s.re ≤ 1
  · exact ZetaEulerLineBound.norm_le_prefix_add_six hσ hs ht
  · let M : ℕ := 2 ^ (depth s + 1)
    have hM : 2 ≤ M := by dsimp only [M]; rw [pow_succ]; nlinarith [Nat.one_le_pow (depth s) 2 (by omega)]
    have hMN : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
    have hcast : ((M - 1 : ℕ) : ℝ) + 1 = M := by exact_mod_cast hMN
    have hN : (0 : ℝ) < (M - 1 : ℕ) := by exact_mod_cast (show 0 < M - 1 by omega)
    have hnorm : ‖s‖ ≤ 2 * ((M - 1 : ℕ) : ℝ) := by
      have h := ZetaEulerLineBound.norm_lt_endpoint s
      change ‖s‖ < (M : ℝ) at h
      have hN1 : (1 : ℝ) ≤ (M - 1 : ℕ) := by exact_mod_cast (show 1 ≤ M - 1 by omega)
      linarith
    have hne : s ≠ 1 := by intro he; norm_num [he] at ht
    have h := ZetaEulerTruncation.norm_zeta_sub_partialSum_le hσ hne (show 1 ≤ M - 1 by omega)
    rw [ZetaEulerLineBound.partialSum_eq_positivePrefix, hMN] at h
    have hp : ((M - 1 : ℕ) : ℝ) ^ (-s.re) ≤ ((M - 1 : ℕ) : ℝ)⁻¹ := by
      have hh := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (M - 1 : ℕ) by exact_mod_cast (show 1 ≤ M - 1 by omega))
        (show -s.re ≤ (-1 : ℝ) by linarith)
      simpa only [Real.rpow_neg_one] using hh
    have hr : ‖s‖ / s.re * ((M - 1 : ℕ) : ℝ) ^ (-s.re) ≤ 2 := by
      calc
        _ ≤ ‖s‖ * ((M - 1 : ℕ) : ℝ)⁻¹ :=
          mul_le_mul (div_le_self (norm_nonneg s) (by linarith)) hp (by positivity) (norm_nonneg s)
        _ ≤ (2 * ((M - 1 : ℕ) : ℝ)) * ((M - 1 : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hnorm (by positivity)
        _ = 2 := by field_simp
    have hd : s.im ≤ ‖s - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.im_le_norm (s - 1)
    have he : (((M - 1 : ℕ) : ℝ) + 1) ^ (1 - s.re) / ‖s - 1‖ ≤ 1 := by
      have hp' := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) + 1 by linarith)
        (show 1 - s.re ≤ 0 by linarith)
      exact (div_le_self (by positivity) (by linarith : 1 ≤ ‖s - 1‖)).trans hp'
    have htri := norm_add_le (riemannZeta s - positivePrefix s M) (positivePrefix s M)
    simp only [sub_add_cancel] at htri
    change ‖riemannZeta s‖ ≤ ‖positivePrefix s M‖ + 6
    linarith

/-- Every original prefix block is paid at its own scale. The complete
sum has a two-thirds logarithmic factor, uniformly in the strip index. -/
theorem prefix_bound (n : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ' : s.re ≤ 3 / 2)
    (ht : (heightThreshold (8 * n) : ℝ) ≤ s.im) :
    ‖positivePrefix s (2 ^ (depth s + 1))‖ ≤
      524288 * s.im ^ growth n * (Real.log s.im) ^ (2 / 3 : ℝ) := by
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
  have ht2 : 2 ≤ s.im := by linarith
  have ht1 : 1 < s.im := by linarith
  have hσ : 0 ≤ s.re := by linarith [(line_bounds n).1]
  have hlog : 1 ≤ Real.log s.im := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ s.im)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [he] at h
    linarith [Real.log_two_gt_d9]
  have hp : 0 ≤ s.im ^ growth n := Real.rpow_nonneg (by linarith) _
  rw [prefix_pow_two]
  calc
    _ ≤ ∑ j ∈ Finset.range (depth s + 1), ‖block s j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (depth s + 1),
        (512 * s.im ^ growth n) * Real.exp
          (-((j : ℝ) * Real.log 2) ^ 3 / (2097152 * (Real.log s.im) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := VinogradovCubicDecay.block_bound n j hn hline ht
        (canonical_scale_le hσ hσ' ht2 (by have hh := Finset.mem_range.mp hj; omega))
      rw [VinogradovCubicDecay.envelope_eq n ht1] at hb
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_assoc] using hb
    _ = (512 * s.im ^ growth n) *
        ∑ j ∈ Finset.range (depth s + 1), Real.exp
          (-((j : ℝ) * Real.log 2) ^ 3 / (2097152 * (Real.log s.im) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (512 * s.im ^ growth n) * (1024 * (Real.log s.im) ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (VinogradovCubicSummation.sum_le hlog _) (by positivity)
    _ = _ := by ring

/-- Actual zeta has the classical two-thirds logarithmic factor on the
full closed strip, with every block and Euler remainder discharged. -/
theorem bound_strip (n : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ' : s.re ≤ 3 / 2)
    (ht : (heightThreshold (8 * n) : ℝ) ≤ s.im) :
    ‖riemannZeta s‖ ≤ 1048576 * s.im ^ growth n * (Real.log s.im) ^ (2 / 3 : ℝ) := by
  have hbT : (rootBase (8 * n) : ℝ) ≤ heightThreshold (8 * n) := by
    exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ rootBase (8 * n) := by exact_mod_cast rootBase_ge_sixteen (8 * n)
  have hσ : 0 < s.re := by linarith [(line_bounds n).1]
  have hz := norm_le_prefix_add_six hσ (by linarith : 2 ≤ s.im)
  have hp := prefix_bound n hn hline hσ' ht
  have hg : 1 ≤ s.im ^ growth n := Real.one_le_rpow (by linarith) (growth_pos n).le
  have hlog : 1 / 2 ≤ Real.log s.im := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ s.im)
    linarith [Real.log_two_gt_d9]
  have hl : 1 / 2 ≤ (Real.log s.im) ^ (2 / 3 : ℝ) := by
    have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hlog (by norm_num : (0 : ℝ) ≤ 2 / 3)
    have hh' : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (by norm_num : (2 / 3 : ℝ) ≤ 1)
    exact hh'.trans hh
  nlinarith

/-- Conjugation gives the same complete growth bound at both signs of
height, still above the unchanged explicit T_(8n). -/
theorem bound_strip_abs (n : ℕ) (hn : 48 ≤ n) {s : ℂ}
    (hline : line n ≤ s.re) (hσ' : s.re ≤ 3 / 2)
    (ht : (heightThreshold (8 * n) : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 1048576 * |s.im| ^ growth n * (Real.log |s.im|) ^ (2 / 3 : ℝ) := by
  by_cases hs : 0 ≤ s.im
  · rw [abs_of_nonneg hs] at ht ⊢
    exact bound_strip n hn hline hσ' ht
  · have hh := bound_strip n hn (s := conj s) (by simpa using hline)
      (by simpa using hσ') (by simpa [abs_of_neg (lt_of_not_ge hs)] using ht)
    simpa [abs_of_neg (lt_of_not_ge hs)] using hh

end
end RiemannGaussian.ZetaVinogradovSummedBound
