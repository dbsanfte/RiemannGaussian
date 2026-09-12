/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ClippedLogNorm
import RiemannGaussian.ZetaEulerLogProfile
import RiemannGaussian.SechVerticalMoments
import RiemannGaussian.ZetaStripDisc

/-!
# The sharp Euler allowance for every retained left negative depth

The actual pole-cleared zeta logarithm, clipped only below an arbitrary
finite negative depth, is integrable on the complete vertical line.
The direct Euler profile and exact density moments give a sharp upper
bound independent of the clipping depth. The original signed mean and
its lower bound remain available before any absolute-value estimate.
-/

namespace RiemannGaussian.ZetaClippedEulerMean
noncomputable section
open Complex MeasureTheory
open DirichletPowerParameters DerivativeOrderComparison ZetaGaussianLocalizer
open ZetaLogarithmicShiftAllowance SechVerticalKernel SechVerticalMoments

/-- The actual left logarithm with a chosen retained negative depth. -/
def value (k : ℕ) (M y : ℝ) : ℝ :=
  ClippedLogNorm.value M (regularized ((line k : ℂ) + I * (y : ℂ)))

/-- The complete original-density mean of the clipped actual left logarithm. -/
def mean (k : ℕ) (M t b : ℝ) : ℝ := ∫ u : ℝ, density u * value k M (t + b * u)

/-- The sharp direct Euler profile plus the exact first-moment allowance. -/
def allowance (k : ℕ) (t b : ℝ) : ℝ :=
  ZetaEulerLogProfile.profile k t + Real.log 2 * shiftCost k t b

/-- Every retained-depth left allowance is nonnegative. -/
theorem allowance_nonneg (k : ℕ) (t b : ℝ) : 0 ≤ allowance k t b := by
  have h := ZetaEulerLogProfile.profile_ge_six k t
  have hshift := mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (shiftCost_nonneg k t b)
  unfold allowance
  linarith

/-- The clipped original logarithm keeps its explicit lower depth. -/
theorem value_lower (k : ℕ) (M y : ℝ) : -M ≤ value k M y := ClippedLogNorm.lower _ _

/-- The direct Euler profile bounds every finite negative-depth clipping,
including at actual zeros and low heights. -/
theorem value_le_profile (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (y : ℝ) :
    value k M y ≤ ZetaEulerLogProfile.profile k y := by
  have hs : ((line k : ℂ) + I * (y : ℂ)).re = line k := by simp
  have hi : ((line k : ℂ) + I * (y : ℂ)).im = y := by simp
  have hz := ZetaEulerLogProfile.regularized_le_exp_profile k hk hs
  rw [hi] at hz
  have hf : Real.exp (-M) ≤ Real.exp (ZetaEulerLogProfile.profile k y) :=
    Real.exp_le_exp.mpr (by linarith [ZetaEulerLogProfile.profile_ge_six k y])
  have h := Real.log_le_log
    (lt_of_lt_of_le (Real.exp_pos (-M)) (le_max_right
      ‖regularized ((line k : ℂ) + I * (y : ℂ))‖ (Real.exp (-M)))) (max_le hz hf)
  simpa only [value, ClippedLogNorm.value, Real.log_exp] using h

/-- The actual clipped line profile is continuous through every zero. -/
theorem continuous_value (k : ℕ) (hk : 1 ≤ k) (M : ℝ) : Continuous (value k M) := by
  have hg : Continuous (fun y : ℝ => regularized ((line k : ℂ) + I * (y : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply (ZetaStripDisc.analyticAt_regularized _).continuousAt.comp (by fun_prop)
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith [half_le_line k hk]
  exact (ClippedLogNorm.continuous M).comp hg

/-- The full shifted logarithm has a logarithmic, rather than linear-height,
absolute dominator at every retained negative depth. -/
theorem abs_value_shift_le (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b u : ℝ) :
    |value k M (t + b * u)| ≤ ZetaEulerLogProfile.profile k t + M + shiftCost k t b * |u| := by
  have hu := (value_le_profile k hk hM (t + b * u)).trans (ZetaEulerLogProfile.profile_shift_le k t b u)
  have hl := value_lower k M (t + b * u)
  have hp := ZetaEulerLogProfile.profile_ge_six k t
  have hb := mul_nonneg (shiftCost_nonneg k t b) (abs_nonneg u)
  rw [abs_le]
  constructor <;> linarith

/-- The full actual clipped logarithm is genuinely density-integrable,
with no finite-height window or unproved negative-part assumption. -/
theorem integrable_value (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b : ℝ) :
    Integrable (fun u : ℝ => density u * value k M (t + b * u)) := by
  have hc := continuous_density.mul ((continuous_value k hk M).comp
    (by fun_prop : Continuous (fun u : ℝ => t + b * u)))
  apply (integrable_affine_density (ZetaEulerLogProfile.profile k t + M) (shiftCost k t b)).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with u
  change ‖density u * value k M (t + b * u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (density_nonneg u)]
  exact mul_le_mul_of_nonneg_left (abs_value_shift_le k hk hM t b u) (density_nonneg u)

/-- The complete actual left mean has the sharp Euler allowance, independent
of how much finite negative depth is retained. -/
theorem mean_le (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b : ℝ) :
    mean k M t b ≤ allowance k t b := by
  have h := integral_mono (integrable_value k hk hM t b)
    (integrable_affine_density (ZetaEulerLogProfile.profile k t) (shiftCost k t b)) (fun u =>
      mul_le_mul_of_nonneg_left
        ((value_le_profile k hk hM _).trans (ZetaEulerLogProfile.profile_shift_le k t b u))
        (density_nonneg u))
  simpa only [mean, allowance, integral_affine_density] using h

/-- The complete actual left mean retains its finite negative floor. -/
theorem mean_lower (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b : ℝ) :
    -M ≤ mean k M t b := by
  have h := integral_mono (integrable_density.mul_const (-M)) (integrable_value k hk hM t b)
    (fun u => mul_le_mul_of_nonneg_left (value_lower k M _) (density_nonneg u))
  simpa only [mean, integral_mul_const, integral_density, one_mul] using h

/-- The full signed mean has a summable logarithmic-frequency envelope;
this estimate does not replace its sharper signed upper bound. -/
theorem abs_mean_le (k : ℕ) (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M) (t b : ℝ) :
    |mean k M t b| ≤ allowance k t b + M := by
  rw [abs_le]
  constructor <;> linarith [mean_le k hk hM t b, mean_lower k hk hM t b, allowance_nonneg k t b]

/-- Retaining more negative depth decreases the entire actual signed left mean. -/
theorem mean_antitone_depth (k : ℕ) (hk : 1 ≤ k) {M N : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N)
    (t b : ℝ) : mean k N t b ≤ mean k M t b := by
  apply integral_mono (integrable_value k hk (hM.trans hMN) t b) (integrable_value k hk hM t b)
  intro u
  exact mul_le_mul_of_nonneg_left (ClippedLogNorm.antitone_depth _ hMN) (density_nonneg u)

end
end RiemannGaussian.ZetaClippedEulerMean
