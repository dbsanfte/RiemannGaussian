/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaNearOneLineBound
import RiemannGaussian.ZetaFiniteDirichlet
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# A complete logarithmic profile on each near-one zeta line

An explicit short eta prefix pays for small ordinates, including zero.
The full line theorem then gives one logarithmic envelope at every real
height. Its positive-log form is continuous even at zeta zeros, providing
an honest integrable upper carrier for vertical zero-detection averages.
-/

namespace RiemannGaussian.ZetaNearOneLogProfile
noncomputable section
open DerivativePowerExponents DirichletPowerParameters DerivativeOrderComparison
open DirichletDyadicBlocks ZetaDyadicTruncation

/-- The complete finite eta prefix has a trivial bound at every height
in the closed right half-plane. -/
theorem eta_prefix_bound {s : ℂ} (hσ : 0 ≤ s.re) (N : ℕ) :
    ‖pairedEtaCorePartialSum N s‖ ≤ 2 * (N : ℝ) := by
  unfold pairedEtaCorePartialSum
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      rw [eta_pair_eq_features]
      apply (norm_sub_le _ _).trans
      linarith [norm_zetaPrimeFeature_le_one hσ (2 * n + 1),
        norm_zetaPrimeFeature_le_one hσ (2 * n + 2)]
    _ = _ := by simp; ring

/-- A short complete eta prefix and the proved full tail control all
small ordinates uniformly throughout the right half of the strip. -/
theorem low_height_bound {s : ℂ} (hσ : 1 / 2 ≤ s.re) (hσ1 : s.re < 1)
    (ht : |s.im| ≤ 2) : ‖riemannZeta s‖ ≤ 16 / (1 - s.re) := by
  have hs : 0 < s.re := by linarith
  have hsne : s ≠ 1 := by intro h; simp [h] at hσ1
  have hn := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hs.le] at hn
  have hscale : ‖s‖ ≤ ((2 * 2 + 1 : ℕ) : ℝ) := by norm_num; linarith
  have htail := norm_pairedEtaCore_tail_le_two hs 2 hscale
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] at htail
  have hpow : (5 : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hp := eta_prefix_bound hs.le 2
  norm_num only [Nat.cast_ofNat] at hp
  have he := norm_add_le (pairedEtaCore s - pairedEtaCorePartialSum 2 s)
    (pairedEtaCorePartialSum 2 s)
  simp only [sub_add_cancel] at he
  have heta : ‖pairedEtaCore s‖ ≤ 6 := by linarith
  have hid : pairedEtaCore s = etaFactor s * riemannZeta s := by
    rw [factor_eq]
    exact pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hsne
  rw [hid, norm_mul] at heta
  have hgap : (1 - s.re) / 2 ≤ (2 : ℝ) ^ (1 - s.re) - 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := Real.add_one_le_exp (Real.log 2 * (1 - s.re))
    nlinarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right (hgap.trans (factor_lower s))
    (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (by linarith : 0 < 1 - s.re)).mpr
  nlinarith

/-- A positive height coordinate that includes the low-ordinate range. -/
def height (y : ℝ) : ℝ := |y| + 2

/-- The enlarged height is always at least two. -/
theorem two_le_height (y : ℝ) : 2 ≤ height y := by unfold height; linarith [abs_nonneg y]

/-- The full zeta line bound holds at every real ordinate after the
height is enlarged by two; the same uniform constant is retained. -/
theorem all_height_bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k) :
    ‖riemannZeta s‖ ≤
      32768 / delta k * height s.im ^ alpha k * Real.log (height s.im) := by
  have hH := two_le_height s.im
  have hHpos : 0 < height s.im := by linarith
  have hδ := delta_pos k
  by_cases ht : 2 ≤ |s.im|
  · have h := ZetaNearOneLineBound.bound_displacement k hk hline ht
    have hp := Real.rpow_le_rpow (abs_nonneg s.im)
      (show |s.im| ≤ height s.im by unfold height; linarith) (alpha_pos k).le
    have hl := Real.log_le_log (by linarith : 0 < |s.im|)
      (show |s.im| ≤ height s.im by unfold height; linarith)
    have hm := mul_le_mul hp hl (Real.log_nonneg (by linarith))
      (Real.rpow_nonneg hHpos.le _)
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 32768 / delta k by positivity)
    apply h.trans
    convert hm' using 1 <;> ring
  · have hs : 1 / 2 ≤ s.re := by rw [hline]; exact half_le_line k hk
    have hs1 : s.re < 1 := by rw [hline]; exact line_lt_one k
    have h := low_height_bound hs hs1 (lt_of_not_ge ht).le
    have he : 1 - s.re = delta k := by rw [hline, delta_eq_one_sub_line]
    rw [he] at h
    have hp : 1 ≤ height s.im ^ alpha k := Real.one_le_rpow (by linarith) (alpha_pos k).le
    have hl : (1 / 2 : ℝ) ≤ Real.log (height s.im) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hH
      linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ Real.log (height s.im) by linarith)
    apply h.trans
    apply (div_le_iff₀ hδ).mpr
    have hid : (32768 / delta k * height s.im ^ alpha k *
        Real.log (height s.im)) * delta k =
        32768 * (height s.im ^ alpha k * Real.log (height s.im)) := by field_simp
    rw [hid]
    nlinarith

/-- The complete pointwise logarithmic allowance, with its order cost
and both height logarithms explicit. -/
def profile (k : ℕ) (y : ℝ) : ℝ :=
  Real.log (32768 / delta k) + alpha k * Real.log (height y) +
    Real.log (Real.log (height y))

/-- The uniform line coefficient is at least two at every order. -/
theorem coefficient_ge_two (k : ℕ) : (2 : ℝ) ≤ 32768 / delta k := by
  have hd : delta k ≤ 1 := order_mul_alpha_le_one k
  apply (le_div_iff₀ (delta_pos k)).mpr
  linarith

/-- The complete real majorant is at least one, including at height
zero; taking its logarithm therefore gives a nonnegative allowance. -/
theorem one_le_majorant (k : ℕ) (y : ℝ) :
    1 ≤ 32768 / delta k * height y ^ alpha k * Real.log (height y) := by
  have hh := two_le_height y
  have hp : 1 ≤ height y ^ alpha k := Real.one_le_rpow (by linarith) (alpha_pos k).le
  have hl : (1 / 2 : ℝ) ≤ Real.log (height y) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hh
    linarith [Real.log_two_gt_d9]
  have h1 := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 32768 / delta k by have h := delta_pos k; positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ Real.log (height y) by linarith)
  have h3 := mul_le_mul_of_nonneg_right (coefficient_ge_two k)
    (show 0 ≤ Real.log (height y) by linarith)
  nlinarith

/-- The logarithmic profile is exactly the logarithm of the complete
real majorant, before any vertical averaging is applied. -/
theorem profile_eq_log (k : ℕ) (y : ℝ) : profile k y =
    Real.log (32768 / delta k * height y ^ alpha k * Real.log (height y)) := by
  have hh : 0 < height y := by linarith [two_le_height y]
  have hc : 0 < 32768 / delta k := div_pos (by norm_num) (delta_pos k)
  have hl : 0 < Real.log (height y) := Real.log_pos (by linarith [two_le_height y])
  rw [Real.log_mul (mul_pos hc (Real.rpow_pos_of_pos hh _)).ne' hl.ne',
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hh _).ne', Real.log_rpow hh]
  rfl

/-- The complete logarithmic allowance is nonnegative at every height. -/
theorem profile_nonneg (k : ℕ) (y : ℝ) : 0 ≤ profile k y := by
  rw [profile_eq_log]
  exact Real.log_nonneg (one_le_majorant k y)

/-- The positive logarithm of the actual zeta function is controlled
on the whole vertical line, including at its zeros. -/
theorem posLog_bound (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hline : s.re = line k) :
    Real.posLog ‖riemannZeta s‖ ≤ profile k s.im := by
  have h := Real.posLog_le_posLog (norm_nonneg _) (all_height_bound k hk hline)
  have hm := one_le_majorant k s.im
  have hn : 0 ≤ 32768 / delta k * height s.im ^ alpha k * Real.log (height s.im) := by
    linarith
  have he : Real.posLog (32768 / delta k * height s.im ^ alpha k *
      Real.log (height s.im)) = profile k s.im := by
    rw [Real.posLog_eq_log (by simpa only [abs_of_nonneg hn] using hm), profile_eq_log]
  rw [he] at h
  exact h

/-- The positive-log carrier on a balanced vertical line. -/
def positiveLog (k : ℕ) (y : ℝ) : ℝ :=
  Real.posLog ‖riemannZeta ((line k : ℂ) + Complex.I * (y : ℂ))‖

/-- The positive-log carrier is continuous through its zero ordinates. -/
theorem continuous_positiveLog (k : ℕ) : Continuous (positiveLog k) := by
  have hf : Continuous (fun y : ℝ => riemannZeta ((line k : ℂ) + Complex.I * (y : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hs : (line k : ℂ) + Complex.I * (y : ℂ) ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
        Complex.one_re] at he
      linarith [line_lt_one k]
    have ha : ContinuousAt (fun y : ℝ => (line k : ℂ) + Complex.I * (y : ℂ)) y := by
      fun_prop
    exact (differentiableAt_riemannZeta hs).continuousAt.comp
      (f := fun y : ℝ => (line k : ℂ) + Complex.I * (y : ℂ)) ha
  exact Real.continuous_posLog.comp hf.norm

/-- The continuous positive-log carrier has the complete real profile
as a pointwise upper bound. -/
theorem positiveLog_le (k : ℕ) (hk : 1 ≤ k) (y : ℝ) : positiveLog k y ≤ profile k y := by
  have h := posLog_bound k hk (s := (line k : ℂ) + Complex.I * (y : ℂ)) (by simp)
  simpa [positiveLog] using h

end
end RiemannGaussian.ZetaNearOneLogProfile
