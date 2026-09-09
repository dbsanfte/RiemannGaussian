/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseArithmetic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The actual height cost of arbitrary real-frequency spectra

A finite logarithmic moment suffices for the complete local-zero estimate.
For any fixed admissible spectrum, its true height cost divided by
`log (abs y + 22)` tends to its total coefficient mass at nonzero frequencies.
This includes infinite support and frequencies accumulating at zero.

Thus the leading cost is not a prescribed linear frequency weight or a
count of frequencies. The exact per-frequency costs remain available for
finite heights. No uniform assertion for height-dependent spectra is made.
-/

open Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Scaling by any real frequency has an explicit logarithmic overhead,
including zero, negative, and arbitrarily small frequencies. -/
theorem localZetaLogHeight_mul_le_logFrequency (v y : ℝ) :
    localZetaLogHeight (v * y) ≤ localZetaLogHeight y + Real.log (1 + |v|) := by
  unfold localZetaLogHeight
  rw [abs_mul]
  calc
    Real.log (|v| * |y| + 22) ≤ Real.log ((1 + |v|) * (|y| + 22)) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg v, abs_nonneg y])
    _ = Real.log (|y| + 22) + Real.log (1 + |v|) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      ring

/-- The actual height costs are summable under a logarithmic moment,
without a linear moment or a finite-support assumption. -/
theorem summable_zetaPhase_height_of_logMoment {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n ↦ a n * Real.log (1 + |ω n|))) (y : ℝ) :
    Summable (fun n ↦ a n * localZetaLogHeight (ω n * y)) := by
  apply ((hs.mul_right (localZetaLogHeight y)).add hlog).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ha n) (by linarith [two_lt_localZetaLogHeight (ω n * y)]))]
  have h := mul_le_mul_of_nonneg_left (localZetaLogHeight_mul_le_logFrequency (ω n) y) (ha n)
  linarith

/-- The entire frequency cost has an explicit finite-height upper bound
in terms of the coefficient mass and logarithmic frequency moment. -/
theorem zetaPhase_height_le_mass_add_logMoment {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n ↦ a n * Real.log (1 + |ω n|))) (y : ℝ) :
    (∑' n : ℕ, a n * localZetaLogHeight (ω n * y)) ≤
      (∑' n : ℕ, a n) * localZetaLogHeight y +
        ∑' n : ℕ, a n * Real.log (1 + |ω n|) := by
  rw [← tsum_mul_right, ← (hs.mul_right (localZetaLogHeight y)).tsum_add hlog]
  apply (summable_zetaPhase_height_of_logMoment ha hs hlog y).tsum_le_tsum _
    ((hs.mul_right (localZetaLogHeight y)).add hlog)
  intro n
  have h := mul_le_mul_of_nonneg_left (localZetaLogHeight_mul_le_logFrequency (ω n) y) (ha n)
  linarith

/-- The logarithmic height tends to infinity along positive real heights. -/
theorem tendsto_localZetaLogHeight_atTop : Tendsto localZetaLogHeight atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_atTop_mono (fun y : ℝ ↦ show y ≤ |y| + 22 by linarith [le_abs_self y]) tendsto_id)

private theorem localZetaLogHeight_pos (y : ℝ) : 0 < localZetaLogHeight y := by
  linarith [two_lt_localZetaLogHeight y]

/-- Every fixed nonzero real frequency has the same leading logarithmic
height cost. The two logarithmic overheads give explicit upper and lower
control before taking the limit. -/
theorem tendsto_localZetaLogHeight_mul_div {v : ℝ} (hv : v ≠ 0) :
    Tendsto (fun y : ℝ ↦ localZetaLogHeight (v * y) / localZetaLogHeight y)
      atTop (𝓝 1) := by
  have hu := tendsto_localZetaLogHeight_atTop.const_div_atTop (Real.log (1 + |v|))
  have hl := tendsto_localZetaLogHeight_atTop.const_div_atTop (Real.log (1 + |v⁻¹|))
  have hlu : Tendsto (fun y : ℝ ↦ 1 - Real.log (1 + |v⁻¹|) / localZetaLogHeight y)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.sub hl
  have huu : Tendsto (fun y : ℝ ↦ 1 + Real.log (1 + |v|) / localZetaLogHeight y)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlu huu
  · intro y
    have h := localZetaLogHeight_mul_le_logFrequency v⁻¹ (v * y)
    rw [inv_mul_cancel_left₀ hv] at h
    apply (le_div_iff₀ (localZetaLogHeight_pos y)).mpr
    have he : (1 - Real.log (1 + |v⁻¹|) / localZetaLogHeight y) * localZetaLogHeight y =
        localZetaLogHeight y - Real.log (1 + |v⁻¹|) := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (localZetaLogHeight_pos y).ne']
    rw [he]
    linarith
  · intro y
    apply (div_le_iff₀ (localZetaLogHeight_pos y)).mpr
    have he : (1 + Real.log (1 + |v|) / localZetaLogHeight y) * localZetaLogHeight y =
        localZetaLogHeight y + Real.log (1 + |v|) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (localZetaLogHeight_pos y).ne']
    rw [he]
    exact localZetaLogHeight_mul_le_logFrequency v y

/-- A zero frequency has no leading logarithmic height cost; every fixed
nonzero frequency contributes one unit before applying its coefficient. -/
theorem tendsto_localZetaLogHeight_frequency_div (v : ℝ) :
    Tendsto (fun y : ℝ ↦ localZetaLogHeight (v * y) / localZetaLogHeight y)
      atTop (𝓝 (if v = 0 then 0 else 1)) := by
  by_cases hv : v = 0
  · subst v
    simpa using tendsto_localZetaLogHeight_atTop.const_div_atTop (localZetaLogHeight 0)
  · simpa [hv] using tendsto_localZetaLogHeight_mul_div hv

/-- For any fixed finite or infinite spectrum with finite logarithmic
moment, the exact leading cost is its mass at nonzero frequencies. The
dominating summable sequence also covers frequencies accumulating at zero;
no separation or positive minimum frequency is assumed. -/
theorem tendsto_zetaPhase_height_div_logHeight {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n ↦ a n * Real.log (1 + |ω n|))) :
    Tendsto (fun y : ℝ ↦ (∑' n : ℕ, a n * localZetaLogHeight (ω n * y)) /
        localZetaLogHeight y) atTop (𝓝 (∑' n : ℕ, if ω n = 0 then 0 else a n)) := by
  have hab (n : ℕ) : Tendsto (fun y : ℝ ↦ a n *
      (localZetaLogHeight (ω n * y) / localZetaLogHeight y))
      atTop (𝓝 (if ω n = 0 then 0 else a n)) := by
    convert (tendsto_localZetaLogHeight_frequency_div (ω n)).const_mul (a n) using 1
    split_ifs <;> simp
  have hbound (y : ℝ) (n : ℕ) :
      ‖a n * (localZetaLogHeight (ω n * y) / localZetaLogHeight y)‖ ≤
        a n + a n * Real.log (1 + |ω n|) := by
    have hL := localZetaLogHeight_pos y
    have hLi := localZetaLogHeight_pos (ω n * y)
    have hlogpos : 0 ≤ Real.log (1 + |ω n|) := Real.log_nonneg (by linarith [abs_nonneg (ω n)])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n) (div_nonneg hLi.le hL.le))]
    have hratio : localZetaLogHeight (ω n * y) / localZetaLogHeight y ≤
        1 + Real.log (1 + |ω n|) := by
      apply (div_le_iff₀ hL).mpr
      have h := localZetaLogHeight_mul_le_logFrequency (ω n) y
      have hm := mul_le_mul_of_nonneg_left
        (by linarith [two_lt_localZetaLogHeight y] : (1 : ℝ) ≤ localZetaLogHeight y) hlogpos
      nlinarith only [h, hm]
    have h := mul_le_mul_of_nonneg_left hratio (ha n)
    nlinarith only [h]
  have h := tendsto_tsum_of_dominated_convergence (hs.add hlog) hab
    (Eventually.of_forall hbound)
  convert h using 1
  funext y
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  ring

end

end RiemannGaussian
