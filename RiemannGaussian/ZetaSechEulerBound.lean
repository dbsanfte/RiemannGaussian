/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSechExactMass
import RiemannGaussian.ZetaEulerLogProfile

/-!
# Direct Euler growth in the original signed vertical detector

The pole-cleared line bound is returned to the literal zeta logarithm
with its exact rational correction. The correction has a quadratic
central-height bound and an exponentially small contribution from the
remote low-height window. Exact kernel moments remove the factor two
from the main allowance. Every finite window retains its complete
negative logarithmic mass; no infinite negative-part integral is assumed.
-/

namespace RiemannGaussian.ZetaSechEulerBound
noncomputable section
open Complex MeasureTheory Set Real
open DirichletPowerParameters DerivativeOrderComparison ZetaNearOneLogProfile
open ZetaLogarithmicShiftAllowance ZetaGaussianLocalizer
open SechVerticalKernel SechVerticalMoments ZetaSechSignedWindows

/-- The exact logarithmic cost of undoing the rational pole clearing. -/
def correction (k : ℕ) (y : ℝ) : ℝ :=
  Real.log (1 + 4 * line k / ((1 - line k) ^ 2 + y ^ 2)) / 2

private theorem denominator_pos (k : ℕ) (y : ℝ) : 0 < (1 - line k) ^ 2 + y ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith [line_lt_one k])) (sq_nonneg y)

/-- The exact pole correction is nonnegative on each eligible line. -/
theorem correction_nonneg (k : ℕ) (hk : 1 ≤ k) (y : ℝ) : 0 ≤ correction k y := by
  apply div_nonneg (Real.log_nonneg _) (by norm_num)
  have h := half_le_line k hk
  have hp := div_nonneg (by linarith : 0 ≤ 4 * line k) (denominator_pos k y).le
  linarith

/-- The pole correction remains continuous through the low-height window. -/
theorem continuous_correction (k : ℕ) (hk : 1 ≤ k) : Continuous (correction k) := by
  have hc : Continuous (fun y : ℝ => 1 + 4 * line k / ((1 - line k) ^ 2 + y ^ 2)) :=
    continuous_const.add (continuous_const.div₀ (by fun_prop) (fun y => (denominator_pos k y).ne'))
  exact (hc.log (fun y => by
    have h := half_le_line k hk
    have hp := div_nonneg (by linarith : 0 ≤ 4 * line k) (denominator_pos k y).le
    linarith)).div_const 2

/-- The retained correction is exactly the norm logarithm of the inverse
pole-clearing factor, not a substitute majorant. -/
theorem correction_eq_log_ratio (k : ℕ) {s : ℂ} (hs : s.re = line k) :
    correction k s.im = Real.log ‖(s + 1) / (s - 1)‖ := by
  have hrat : ‖(s + 1) / (s - 1)‖ ^ 2 =
      1 + 4 * line k / ((1 - line k) ^ 2 + s.im ^ 2) := by
    rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    simp only [normSq_apply, add_re, add_im, sub_re, sub_im, one_re, one_im,
      add_zero, sub_zero, hs]
    rw [show (line k - 1) * (line k - 1) + s.im * s.im =
      (1 - line k) ^ 2 + s.im ^ 2 by ring]
    field_simp [(denominator_pos k s.im).ne']
    ring
  unfold correction
  rw [← hrat, Real.log_pow]
  norm_num

/-- The low-height correction is largest at ordinate zero. -/
theorem correction_le_zero (k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    correction k y ≤ correction k 0 := by
  unfold correction
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.log_le_log (by
    have h := half_le_line k hk
    have hp := div_nonneg (by linarith : 0 ≤ 4 * line k) (denominator_pos k y).le
    linarith)
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by linarith [half_le_line k hk])
    (denominator_pos k 0)
  nlinarith [sq_nonneg y]

/-- The correction has quadratic decay away from the pole's ordinate. -/
theorem correction_le_quadratic (k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : y ≠ 0) :
    correction k y ≤ 2 / y ^ 2 := by
  have hσ := half_le_line k hk
  have harg : 0 < 1 + 4 * line k / ((1 - line k) ^ 2 + y ^ 2) := by
    have hp := div_nonneg (by linarith : 0 ≤ 4 * line k) (denominator_pos k y).le
    linarith
  have hl := Real.log_le_sub_one_of_pos harg
  have hd : 4 * line k / ((1 - line k) ^ 2 + y ^ 2) ≤ 4 / y ^ 2 := by
    apply div_le_div₀ (by norm_num) (by linarith [line_lt_one k]) (sq_pos_of_ne_zero hy)
    nlinarith [sq_nonneg (1 - line k)]
  unfold correction
  calc
    _ ≤ (4 / y ^ 2) / 2 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    _ = _ := by ring

/-- The actual zeta positive logarithm satisfies the direct Euler profile
plus its exact pole correction, including at zero ordinates. -/
theorem positiveLog_le (k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    positiveLog k y ≤ ZetaEulerLogProfile.profile k y + correction k y := by
  let s : ℂ := (line k : ℂ) + Complex.I * (y : ℂ)
  have hs : s.re = line k := by simp [s]
  have him : s.im = y := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    rw [hs] at he
    simp only [one_re] at he
    linarith [line_lt_one k]
  have hσ : 0 ≤ s.re := by rw [hs]; linarith [half_le_line k hk]
  have he : riemannZeta s = (s + 1) / (s - 1) * regularized s := by
    rw [regularized_eq hs1]
    field_simp [sub_ne_zero.mpr hs1, add_one_ne_zero hσ]
  have hreg := Real.posLog_le_posLog (norm_nonneg _)
    (ZetaEulerLogProfile.regularized_le_exp_profile k hk hs)
  rw [Real.posLog_apply (x := Real.exp (ZetaEulerLogProfile.profile k s.im)), Real.log_exp,
    max_eq_right (by linarith [ZetaEulerLogProfile.profile_ge_six k s.im]), him] at hreg
  have hrat : 1 ≤ ‖(s + 1) / (s - 1)‖ := by
    have hn := norm_ratio_le_one hσ
    rw [norm_div, div_le_one (norm_pos_iff.mpr (add_one_ne_zero hσ))] at hn
    rw [norm_div]
    exact (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr hn
  change Real.posLog ‖riemannZeta s‖ ≤ _
  rw [he, norm_mul]
  have h := Real.posLog_mul (x := ‖(s + 1) / (s - 1)‖) (y := ‖regularized s‖)
  have heq : Real.posLog ‖(s + 1) / (s - 1)‖ = Real.log ‖(s + 1) / (s - 1)‖ :=
    Real.posLog_eq_log (by simpa only [abs_of_nonneg (norm_nonneg _)] using hrat)
  rw [heq, ← correction_eq_log_ratio k hs, him] at h
  linarith

/-- The entire pole correction is a genuine integral on the original
vertical detector line. -/
def poleMass (k : ℕ) (t a : ℝ) : ℝ :=
  ∫ u : ℝ, density u * correction k (t + a * u)

/-- The full pole correction is absolutely integrable, including all
remote low-height ordinates. -/
theorem integrable_correction (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    Integrable (fun u : ℝ => density u * correction k (t + a * u)) := by
  have hc := continuous_density.mul ((continuous_correction k hk).comp
    (by fun_prop : Continuous (fun u : ℝ => t + a * u)))
  apply (integrable_density.mul_const (correction k 0)).mono' hc.aestronglyMeasurable
  filter_upwards [] with u
  change ‖density u * correction k (t + a * u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (density_nonneg u) (correction_nonneg k hk _))]
  exact mul_le_mul_of_nonneg_left (correction_le_zero k hk _) (density_nonneg u)

private theorem correction_le_center_add_tail (k : ℕ) (hk : 1 ≤ k)
    {t a : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) (u : ℝ) :
    correction k (t + a * u) ≤ 8 / t ^ 2 +
      if |t| / (2 * |a|) < |u| then correction k 0 else 0 := by
  by_cases hu : |t| / (2 * |a|) < |u|
  · rw [if_pos hu]
    have hc := correction_le_zero k hk (t + a * u)
    have hp : 0 ≤ 8 / t ^ 2 := by positivity
    linarith
  rw [if_neg hu, add_zero]
  have hau : |a * u| ≤ |t| / 2 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hu) (abs_nonneg a)
    have he : |a| * (|t| / (2 * |a|)) = |t| / 2 := by
      field_simp [abs_ne_zero.mpr ha]
    rwa [he] at h
  have hy : |t| / 2 ≤ |t + a * u| := by
    have h := abs_sub (t + a * u) (a * u)
    rw [add_sub_cancel_right] at h
    linarith
  have hy0 : t + a * u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hy
    linarith [abs_pos.mpr ht]
  apply (correction_le_quadratic k hk hy0).trans
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero hy0) (sq_pos_of_ne_zero ht)).mpr
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ |t| / 2) (abs_nonneg _)).mpr hy
  rw [div_pow, sq_abs, sq_abs] at hsq
  nlinarith

/-- The complete pole correction is quadratic in the central height,
plus an explicitly exponentially suppressed low-height contribution.
There is no global reciprocal-width charge in the main profile. -/
theorem poleMass_le (k : ℕ) (hk : 1 ≤ k) {t a : ℝ} (ht : t ≠ 0) (ha : a ≠ 0) :
    poleMass k t a ≤ 8 / t ^ 2 +
      2 * correction k 0 * Real.exp (-|t| / |a|) := by
  let R := |t| / (2 * |a|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hset : MeasurableSet {u : ℝ | R < |u|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have htail : Integrable (fun u : ℝ => if R < |u| then density u else 0) := by
    convert! integrable_density.indicator hset using 1
  have hbase := integrable_density.mul_const (8 / t ^ 2)
  have hweighted := htail.const_mul (correction k 0)
  have h := integral_mono (integrable_correction k hk t a) (hbase.add hweighted) (fun u => by
    have h := mul_le_mul_of_nonneg_left (correction_le_center_add_tail k hk ht ha u)
      (density_nonneg u)
    change density u * correction k (t + a * u) ≤
      density u * (8 / t ^ 2) + correction k 0 * (if R < |u| then density u else 0)
    convert! h using 1
    dsimp [R]
    split_ifs <;> ring)
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hweighted, integral_mul_const, integral_const_mul,
    integral_density, one_mul] at h
  have hb := mul_le_mul_of_nonneg_left (integral_tail_le hR) (correction_nonneg k hk 0)
  have he : -2 * R = -|t| / |a| := by dsimp [R]; ring
  rw [he] at hb
  unfold poleMass
  nlinarith only [h, hb]

/-- The main allowance uses the true kernel moments, with the complete
pole correction still present as its own evaluated integral. -/
theorem integral_bound_with_pole (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    (∫ u : ℝ, ZetaSechVerticalBound.integrand k t a u) ≤
      ZetaEulerLogProfile.profile k t + Real.log 2 * shiftCost k t a + poleMass k t a := by
  have hi := (integrable_affine_density (ZetaEulerLogProfile.profile k t) (shiftCost k t a)).add
    (integrable_correction k hk t a)
  have h := integral_mono (ZetaSechVerticalBound.integrable_integrand k hk t a) hi (fun u => by
    have hp := positiveLog_le k hk (t + a * u)
    have hs := ZetaEulerLogProfile.profile_shift_le k t a u
    change density u * positiveLog k (t + a * u) ≤ _
    have h := mul_le_mul_of_nonneg_left (show positiveLog k (t + a * u) ≤
      ZetaEulerLogProfile.profile k t + shiftCost k t a * |u| + correction k (t + a * u) by
      linarith) (density_nonneg u)
    simpa only [mul_add, Pi.add_apply] using h)
  simp only [Pi.add_apply] at h
  rwa [integral_add (integrable_affine_density _ _) (integrable_correction k hk t a),
    integral_affine_density] at h

/-- The literal signed zeta window retains its complete negative mass
after the direct Euler profile and exact moments have been substituted. -/
theorem window_bound_with_pole (k : ℕ) (hk : 1 ≤ k) (t a : ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      ZetaEulerLogProfile.profile k t + Real.log 2 * shiftCost k t a + poleMass k t a -
        ∫ u in l..r, negativeIntegrand k t a u := by
  rw [window_exact]
  apply sub_le_sub_right
  have hp : (∫ u in l..r, ZetaSechVerticalBound.integrand k t a u) ≤
      ∫ u : ℝ, ZetaSechVerticalBound.integrand k t a u := by
    rw [intervalIntegral.integral_of_le hlr]
    exact setIntegral_le_integral (ZetaSechVerticalBound.integrable_integrand k hk t a)
      (ae_of_all _ (ZetaSechVerticalBound.integrand_nonneg k t a))
  exact hp.trans (integral_bound_with_pole k hk t a)

/-- The fully explicit bound applies to the original signed zeta window,
keeps its whole negative logarithmic mass, and pays the small pole correction
only quadratically or through the true exponential detector tail. -/
theorem window_bound (k : ℕ) (hk : 1 ≤ k) {t a : ℝ} (ht : t ≠ 0) (ha : a ≠ 0)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      ZetaEulerLogProfile.profile k t + Real.log 2 * shiftCost k t a + 8 / t ^ 2 +
        2 * correction k 0 * Real.exp (-|t| / |a|) -
          ∫ u in l..r, negativeIntegrand k t a u := by
  linarith [window_bound_with_pole k hk t a hlr, poleMass_le k hk ht ha]

end
end RiemannGaussian.ZetaSechEulerBound
