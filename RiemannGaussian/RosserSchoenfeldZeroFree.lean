/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSignedPoleZeroFree

/-!
# The exact zero-free input to Rosser--Schoenfeld's prime estimates

Theorem 26 of Rosser and Schoenfeld (1962) uses the constant defined in
their Theorem 11 and the starting height `exp(9.99)`. The repository's
proved signed-pole region implies this whole input with the exact radical
constant, including the original starting height. This does not supply
the separate finite verification that low zeros lie on the critical line,
or the source's estimates for theta and psi.
-/

namespace RiemannGaussian.RosserSchoenfeldZeroFree
noncomputable section
open Real

/-- The exact source constant, not its displayed decimal approximation. -/
def sourceConstant : ℝ := 515 / (sqrt 546 - sqrt 322) ^ 2

/-- The source's verified-low-height cutoff, used here only as a height value. -/
def sourceHeight : ℝ := exp (999 / 100)

/-- A rational enclosure pays the comparison without rounding the source constant. -/
theorem sourceConstant_ge_sixteen : (16 : ℝ) ≤ sourceConstant := by
  have ha := sqrt_nonneg (546 : ℝ)
  have hb := sqrt_nonneg (322 : ℝ)
  have ha2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 546)
  have hb2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 322)
  have hd : 0 < sqrt (546 : ℝ) - sqrt 322 := by
    have hh := sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 322)
      (by norm_num : (322 : ℝ) < 546)
    linarith
  have hupper : sqrt (546 : ℝ) ≤ 117 / 5 := by nlinarith
  have hlower : (179 / 10 : ℝ) ≤ sqrt 322 := by nlinarith
  have hsq : (sqrt (546 : ℝ) - sqrt 322) ^ 2 ≤ 121 / 4 := by nlinarith
  unfold sourceConstant
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

/-- The source coefficient has no singular or nonpositive denominator. -/
theorem sourceConstant_pos : 0 < sourceConstant := lt_of_lt_of_le (by norm_num) sourceConstant_ge_sixteen

/-- An upper rational enclosure for the source's prime-error calculation. -/
theorem sourceConstant_le_eighteen : sourceConstant ≤ (18 : ℝ) := by
  have ha := sqrt_nonneg (546 : ℝ)
  have hb := sqrt_nonneg (322 : ℝ)
  have ha2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 546)
  have hb2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 322)
  have hlower : (584 / 25 : ℝ) ≤ sqrt 546 := by nlinarith
  have hupper : sqrt (322 : ℝ) ≤ 359 / 20 := by nlinarith
  have hd : 0 < sqrt (546 : ℝ) - sqrt 322 := by linarith
  have hsq : (541 / 100 : ℝ) ^ 2 ≤ (sqrt (546 : ℝ) - sqrt 322) ^ 2 := by nlinarith
  unfold sourceConstant
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith

/-- At every source height, its complete width is covered by the proved signed-pole region. -/
theorem source_width_le_signedPole {t : ℝ} (ht : sourceHeight ≤ |t|) :
    1 / (sourceConstant * log |t|) ≤ zetaSignedPoleZeroMargin t := by
  have ht0 : 0 < |t| := (exp_pos (999 / 100)).trans_le ht
  have hl : (999 / 100 : ℝ) ≤ log |t| := (le_log_iff_exp_le ht0).mpr ht
  have ht2 : 2 ≤ |t| := by
    have hh := add_one_le_exp (999 / 100 : ℝ)
    change exp (999 / 100) ≤ |t| at ht
    linarith
  have hlog : log (|t| + 2) ≤ log |t| + 1 := by
    calc
      _ ≤ log (2 * |t|) := log_le_log (by positivity) (by linarith)
      _ = log 2 + log |t| := log_mul (by norm_num) ht0.ne'
      _ ≤ _ := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hmul := mul_le_mul_of_nonneg_right sourceConstant_ge_sixteen
    (show 0 ≤ log |t| by linarith)
  unfold zetaSignedPoleZeroMargin
  apply (div_le_div_iff₀ (mul_pos sourceConstant_pos (by linarith))
    (zetaSignedPole_denominator_pos t)).mpr
  nlinarith

/-- The complete literal-zero assertion of Rosser--Schoenfeld Theorem 26. -/
theorem published_zero_margin (ρ : NontrivialZetaZero) (hρ : sourceHeight ≤ |ρ.1.im|) :
    1 / (sourceConstant * log |ρ.1.im|) < 1 - ρ.1.re :=
  (source_width_le_signedPole hρ).trans_lt (zetaSignedPole_margin_lt_one_sub_re ρ)

/-- The source's original right-edge inequality retains its strict edge. -/
theorem published_zero_edge (ρ : NontrivialZetaZero) (hρ : sourceHeight ≤ |ρ.1.im|) :
    ρ.1.re < 1 - 1 / (sourceConstant * log |ρ.1.im|) := by
  linarith [published_zero_margin ρ hρ]

end
end RiemannGaussian.RosserSchoenfeldZeroFree
