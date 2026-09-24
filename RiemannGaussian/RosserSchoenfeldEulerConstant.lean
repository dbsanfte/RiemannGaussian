/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Numerical constants for the complete reciprocal zero mass

A corrected harmonic upper sequence gives Euler's constant below 0.57723.
Together with rational logarithm bounds this controls the exact xi
logarithmic-derivative constant needed for Rosser's reciprocal-square
zero estimate. Every numerical inequality is proved in Lean.
-/

open Filter Topology
namespace RiemannGaussian.RosserSchoenfeldEulerConstant
noncomputable section
set_option maxRecDepth 20000

/-- Harmonic upper sequence with a proved telescoping correction. -/
private def corrected (n : ℕ) : ℝ :=
  Real.eulerMascheroniSeq' (n + 1) - 1 / (2 * ((n : ℝ) + 2))

/-- A rational lower bound for one logarithmic cell. -/
private lemma log_gap {a : ℝ} (ha : 0 < a) :
    1 / (a + 1) + (1 / (2 * (a + 1)) - 1 / (2 * (a + 2))) ≤
      Real.log (a + 1) - Real.log a := by
  have hh := Real.le_log_one_add_of_nonneg (show 0 ≤ 1 / a by positivity)
  have he : 1 + 1 / a = (a + 1) / a := by field_simp
  rw [he, Real.log_div (by positivity) ha.ne'] at hh
  apply le_trans _ hh
  have ha1 : 0 < a + 1 := by positivity
  have ha2 : 0 < a + 2 := by positivity
  have hat : 0 < 1 / a + 2 := by positivity
  apply (le_div_iff₀ hat).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * a * (a + 1) * (a + 2) by positivity)).mp
  field_simp
  nlinarith

/-- The corrected harmonic sequence decreases. -/
private lemma corrected_antitone : Antitone corrected := by
  apply antitone_nat_of_succ_le
  intro n
  have hh := log_gap (show 0 < (n : ℝ) + 1 by positivity)
  simp only [corrected, Real.eulerMascheroniSeq', Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte]
  rw [harmonic_succ (n + 1)]
  push_cast
  simp only [one_div, show (n : ℝ) + 2 = (n : ℝ) + 1 + 1 by ring] at *
  linarith

/-- The correction vanishes, preserving the exact Euler constant. -/
private lemma corrected_tendsto : Tendsto corrected atTop (𝓝 Real.eulerMascheroniConstant) := by
  unfold corrected
  have hs : Tendsto (fun n : ℕ => Real.eulerMascheroniSeq' (n + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)
  have hx : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 2)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hi : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hx
  simpa only [sub_zero] using hs.sub hi

/-- A strict checked upper bound for the actual Euler--Mascheroni constant. -/
theorem euler_upper : Real.eulerMascheroniConstant < (57723 / 100000 : ℝ) := by
  have hb := corrected_antitone.le_of_tendsto corrected_tendsto 199
  have he : corrected 199 = (harmonic 200 : ℝ) - Real.log 200 - 1 / 402 := by
    norm_num [corrected, Real.eulerMascheroniSeq']
  rw [he] at hb
  have hlog : Real.log (200 : ℝ) = 3 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  rw [hlog] at hb
  have hh : (harmonic 200 : ℝ) < (5878031 / 1000000 : ℝ) := by
    set_option maxRecDepth 10000 in norm_num
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- A strict logarithm bound proved from the rational lower bound for pi. -/
theorem log_pi_lower : (114472 / 100000 : ℝ) < Real.log Real.pi := by
  have h := Real.le_log_one_add_of_nonneg
    (show (0 : ℝ) ≤ (3141592 / 1000000) / 3 - 1 by norm_num)
  have he : Real.log (3141592 / 1000000 : ℝ) =
      Real.log 3 + Real.log (1 + ((3141592 / 1000000 : ℝ) / 3 - 1)) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have hpi : Real.log (3141592 / 1000000 : ℝ) < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) (by convert Real.pi_gt_d6 using 1; norm_num)
  rw [he] at hpi
  have hthree := Real.log_three_gt_d9
  norm_num at h
  linarith

/-- The exact real constant in twice the xi logarithmic derivative at one. -/
def massConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - 2 * Real.log 2 - Real.log Real.pi

/-- The exact mass constant is strictly below 0.04622. -/
theorem mass_constant_upper : massConstant < (2311 / 50000 : ℝ) := by
  unfold massConstant
  linarith [euler_upper, log_pi_lower, Real.log_two_gt_d9]

end
end RiemannGaussian.RosserSchoenfeldEulerConstant
