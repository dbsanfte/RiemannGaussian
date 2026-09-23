/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovCanonical
import RiemannGaussian.ZetaNearOneSignedBound
import RiemannGaussian.ZetaSignedExactPole

/-!
# The actual signed zero source with a Vinogradov budget

All canonical divisor terms keep their favorable sign. The selected zero
retains its full multiplicity and radial correction, and the actual
three-height prime inequality supplies the contradiction mechanism.
The only costs are the proved local zeta profile and genuine Euler-center
allowance. No arithmetic estimate is supplied as a premise.
-/

namespace RiemannGaussian.ZetaVinogradovSignedBudget
noncomputable section
open Complex Metric Set
open VinogradovNearOneBudget VinogradovScaleSelection ZetaVinogradovCanonical
open ZetaNearOneLocalDisc (center)
open ZetaNearOneCanonical (translated)
open ZetaNearOneSignedBound (coupledSum coupledSum_nonneg source_le_sum)

/-- The complete real-axis and two nonzero-height costs of the original
three-height prime inequality, using the new actual growth profile. -/
def budget (n : ℕ) (x t : ℝ) : ℝ :=
  1344 * localZetaLogHeight 0 + (32 * allowance n x t + 8 * allowance n x (2 * t)) / delta n

/-- The actual logarithmic derivative at the Euler-side center has the
new residual allowance; the complete zero sum has favorable sign. -/
theorem neg_logDeriv_re_le (n : ℕ) (hn : 12 ≤ n) {t x : ℝ}
    (ht : (heightThreshold n : ℝ) + 1 ≤ |t|) (hx : 0 < x) (hx' : x ≤ delta n / 4) :
    (-logDeriv riemannZeta (center x t)).re ≤ 8 * allowance n x t / delta n := by
  obtain ⟨r, hrlo, hrhi, g, _, _, hb, he⟩ := exists_controlled_decomp n hn ht hx hx'
  have hδ := delta_pos n
  have hr : 0 < r := by linarith
  have hf := (analyticOnNhd_translated n hn ht hx hx').mono
    (closedBall_subset_closedBall (by linarith : r ≤ delta n / 2))
  have hs := coupledSum_nonneg hx hr hf
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  change logDeriv riemannZeta (center x t) = logDeriv g 0 + coupledSum x t r at he
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg hs ⊢
  linarith

/-- A genuine selected zero supplies its complete multiplicity source,
with the same explicit radius correction and no simple-zero premise. -/
theorem neg_logDeriv_re_le_sub_zero (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta n / 4) (hnear : x + 1 - ρ.1.re < delta n / 4) :
    (-logDeriv riemannZeta (center x ρ.1.im)).re ≤ 8 * allowance n x ρ.1.im / delta n -
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (1 / (x + 1 - ρ.1.re) - 16 * (x + 1 - ρ.1.re) / (delta n) ^ 2) := by
  obtain ⟨r, hrlo, hrhi, g, _, _, hb, he⟩ := exists_controlled_decomp n hn ht hx hx'
  have hδ := delta_pos n
  have hr : 0 < r := by linarith
  have hd : 0 < x + 1 - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have hf := (analyticOnNhd_translated n hn ht hx hx').mono
    (closedBall_subset_closedBall (by linarith : r ≤ delta n / 2))
  have hs := source_le_sum ρ hx hr hf (hnear.trans hrlo)
  have hcorrect : (x + 1 - ρ.1.re) / r ^ 2 ≤
      16 * (x + 1 - ρ.1.re) / (delta n) ^ 2 := by
    have hh := div_le_div_of_nonneg_left hd.le
      (by positivity : 0 < (delta n) ^ 2 / 16)
      (by nlinarith : (delta n) ^ 2 / 16 ≤ r ^ 2)
    exact hh.trans_eq (by ring)
  have hmul := mul_le_mul_of_nonneg_left hcorrect
    (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
  have hg : (-logDeriv g 0).re ≤ ‖logDeriv g 0‖ := by
    simpa only [norm_neg] using Complex.re_le_norm (-logDeriv g 0)
  change logDeriv riemannZeta (center x ρ.1.im) = logDeriv g 0 + coupledSum x ρ.1.im r at he
  rw [he, neg_add, Complex.add_re]
  simp only [Complex.neg_re] at hg ⊢
  nlinarith

/-- The full actual prime phase inequality bounds the selected zero
source by the independently proved Vinogradov allowances. -/
theorem source_le_budget (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    {x : ℝ} (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|)
    (hx : 0 < x) (hx' : x ≤ delta n / 4) (hnear : x + 1 - ρ.1.re < delta n / 4) :
    4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / (x + 1 - ρ.1.re) - 16 * (x + 1 - ρ.1.re) / (delta n) ^ 2) ≤
      3 / x + budget n x ρ.1.im := by
  have hsmall : x ≤ 1 / 4 := by linarith [delta_le n]
  have hprime := neg_logDeriv_riemannZeta_three_height_nonneg
    (a := 1 + x) (by linarith) ρ.1.im
  have hreal := neg_logDeriv_riemannZeta_real_le_local hx hsmall
  have hzero := neg_logDeriv_re_le_sub_zero n hn ρ ht hx hx' hnear
  have ht2 : (heightThreshold n : ℝ) + 1 ≤ |2 * ρ.1.im| := by
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg ρ.1.im]
  have hdouble := neg_logDeriv_re_le n hn ht2 hx hx'
  change 0 ≤ 3 * (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re +
    4 * (-logDeriv riemannZeta (center x ρ.1.im)).re +
    (-logDeriv riemannZeta (center x (2 * ρ.1.im))).re at hprime
  unfold budget
  simp only [div_eq_mul_inv] at hreal hzero hdouble ⊢
  nlinarith

/-- A numerical payment of the displayed budget gives a strict actual
zero gap. The horizontal shift is fixed by the proposed margin, not by
an unknown smaller gap of the selected zero. -/
theorem margin_of_budget (n : ℕ) (hn : 12 ≤ n) (ρ : NontrivialZetaZero)
    (ht : (heightThreshold n : ℝ) + 1 ≤ |ρ.1.im|) {d : ℝ} (hd : 0 < d)
    (hdsmall : d < delta n / 28)
    (hpay : 14 * d * budget n (6 * d) ρ.1.im + 6272 * d ^ 2 / (delta n) ^ 2 < 1) :
    d < 1 - ρ.1.re := by
  by_contra! hgap
  have hδ := delta_pos n
  let v := 6 * d + 1 - ρ.1.re
  have hv : 0 < v := by dsimp only [v]; linarith [NontrivialZetaZero.re_lt_one ρ]
  have hvup : v ≤ 7 * d := by dsimp only [v]; linarith
  have hsource := source_le_budget n hn ρ ht (by positivity : 0 < 6 * d)
    (by linarith : 6 * d ≤ delta n / 4)
    (by linarith : 6 * d + 1 - ρ.1.re < delta n / 4)
  have hinv : 1 / (7 * d) ≤ 1 / v := one_div_le_one_div_of_le hv hvup
  have hcorr : 16 * v / (delta n) ^ 2 ≤ 112 * d / (delta n) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hbase : 0 ≤ 1 / (7 * d) - 112 * d / (delta n) ^ 2 := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < (delta n) ^ 2)
      (by positivity : 0 < 7 * d)).mpr
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 28 * d) hδ.le).mpr
      (by linarith : 28 * d ≤ delta n)
    nlinarith
  have hmult : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hlower : 1 / (7 * d) - 112 * d / (delta n) ^ 2 ≤
      (analyticZetaZeroMultiplicity ρ : ℝ) * (1 / v - 16 * v / (delta n) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hmult hbase
    have h' := mul_le_mul_of_nonneg_left (show 1 / (7 * d) - 112 * d / (delta n) ^ 2 ≤
      1 / v - 16 * v / (delta n) ^ 2 by linarith)
      (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
    linarith
  have hs : 4 * (1 / (7 * d) - 112 * d / (delta n) ^ 2) ≤
      3 / (6 * d) + budget n (6 * d) ρ.1.im := by
    change 4 * (analyticZetaZeroMultiplicity ρ : ℝ) *
      (1 / v - 16 * v / (delta n) ^ 2) ≤ _ at hsource
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 14 * d)
  have hleft : 14 * d * (4 * (1 / (7 * d) - 112 * d / (delta n) ^ 2)) =
      8 - 6272 * d ^ 2 / (delta n) ^ 2 := by field_simp; ring
  have hright : 14 * d * (3 / (6 * d) + budget n (6 * d) ρ.1.im) =
      7 + 14 * d * budget n (6 * d) ρ.1.im := by field_simp; ring
  rw [hleft, hright] at hm
  linarith

end
end RiemannGaussian.ZetaVinogradovSignedBudget
