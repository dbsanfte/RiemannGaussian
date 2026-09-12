/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SechVerticalMoments
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The complete rational correction on either vertical boundary

The inverse pole-clearing factor has one exact logarithmic profile on
every nonnegative real line except the pole line. Its original density
integral is retained before applying the quadratic central-height and
exponential tail bounds. The center derivative correction also retains
its exact signed rational form and is favorable in the working strip.
-/

namespace RiemannGaussian.RationalVerticalCorrection
noncomputable section
open Complex MeasureTheory Set
open SechVerticalKernel SechVerticalMoments

/-- The logarithmic norm of the inverse rational pole-clearing factor. -/
def profile (σ y : ℝ) : ℝ := Real.log (1 + 4 * σ / ((σ - 1) ^ 2 + y ^ 2)) / 2

private theorem denominator_pos {σ : ℝ} (hσ : σ ≠ 1) (y : ℝ) :
    0 < (σ - 1) ^ 2 + y ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hσ)) (sq_nonneg y)

/-- The exact inverse normalization has a nonnegative logarithm on either eligible line. -/
theorem profile_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (y : ℝ) : 0 ≤ profile σ y := by
  apply div_nonneg (Real.log_nonneg _) (by norm_num)
  have hp := div_nonneg (by positivity : 0 ≤ 4 * σ) (denominator_pos hσ1 y).le
  linarith

/-- The exact correction is continuous at every height, including ordinate zero. -/
theorem continuous_profile {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) : Continuous (profile σ) := by
  have hc : Continuous (fun y : ℝ => 1 + 4 * σ / ((σ - 1) ^ 2 + y ^ 2)) :=
    continuous_const.add (continuous_const.div₀ (by fun_prop) (fun y => (denominator_pos hσ1 y).ne'))
  exact (hc.log (fun y => by
    have hp := div_nonneg (by positivity : 0 ≤ 4 * σ) (denominator_pos hσ1 y).le
    linarith)).div_const 2

/-- The profile is exactly the inverse rational norm logarithm; its sign and
real-coordinate dependence have not been replaced by a majorant. -/
theorem profile_eq_log_ratio {s : ℂ} (hs : s.re ≠ 1) :
    profile s.re s.im = Real.log ‖(s + 1) / (s - 1)‖ := by
  have he : ‖(s + 1) / (s - 1)‖ ^ 2 = 1 + 4 * s.re / ((s.re - 1) ^ 2 + s.im ^ 2) := by
    rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    simp only [normSq_apply, add_re, add_im, sub_re, sub_im, one_re, one_im, add_zero, sub_zero]
    rw [show (s.re - 1) * (s.re - 1) + s.im * s.im = (s.re - 1) ^ 2 + s.im ^ 2 by ring]
    field_simp [(denominator_pos hs s.im).ne']
    ring
  unfold profile
  rw [← he, Real.log_pow]
  norm_num

/-- The maximum low-height correction occurs at ordinate zero. -/
theorem profile_le_zero {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (y : ℝ) :
    profile σ y ≤ profile σ 0 := by
  unfold profile
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.log_le_log (by
    have hp := div_nonneg (by positivity : 0 ≤ 4 * σ) (denominator_pos hσ1 y).le
    linarith)
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by positivity) (denominator_pos hσ1 0)
  nlinarith [sq_nonneg y]

/-- The inverse normalization decays quadratically, retaining its exact real-coordinate factor. -/
theorem profile_le_quadratic {σ y : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (hy : y ≠ 0) :
    profile σ y ≤ 2 * σ / y ^ 2 := by
  have harg : 0 < 1 + 4 * σ / ((σ - 1) ^ 2 + y ^ 2) := by
    have hp := div_nonneg (by positivity : 0 ≤ 4 * σ) (denominator_pos hσ1 y).le
    linarith
  have hl := Real.log_le_sub_one_of_pos harg
  have hd : 4 * σ / ((σ - 1) ^ 2 + y ^ 2) ≤ 4 * σ / y ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_ne_zero hy) (by nlinarith [sq_nonneg (σ - 1)])
  unfold profile
  calc
    _ ≤ (4 * σ / y ^ 2) / 2 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    _ = _ := by ring

/-- The original full vertical integral of the rational correction. -/
def mass (σ t b : ℝ) : ℝ := ∫ u : ℝ, density u * profile σ (t + b * u)

/-- The entire rational correction is integrable, including the distant low-height window. -/
theorem integrable_profile {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (t b : ℝ) :
    Integrable (fun u : ℝ => density u * profile σ (t + b * u)) := by
  have hc := continuous_density.mul ((continuous_profile hσ hσ1).comp
    (by fun_prop : Continuous (fun u : ℝ => t + b * u)))
  apply (integrable_density.mul_const (profile σ 0)).mono' hc.aestronglyMeasurable
  filter_upwards [] with u
  change ‖density u * profile σ (t + b * u)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (density_nonneg u) (profile_nonneg hσ hσ1 _))]
  exact mul_le_mul_of_nonneg_left (profile_le_zero hσ hσ1 _) (density_nonneg u)

/-- The complete original rational mass is nonnegative. -/
theorem mass_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (t b : ℝ) : 0 ≤ mass σ t b :=
  integral_nonneg (fun u => mul_nonneg (density_nonneg u) (profile_nonneg hσ hσ1 _))

/-- The mass is uniformly bounded by its zero-height profile, with the true density mass one. -/
theorem mass_le_zero {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (t b : ℝ) :
    mass σ t b ≤ profile σ 0 := by
  have h := integral_mono (integrable_profile hσ hσ1 t b) (integrable_density.mul_const (profile σ 0))
    (fun u => mul_le_mul_of_nonneg_left (profile_le_zero hσ hσ1 _) (density_nonneg u))
  simpa only [integral_mul_const, integral_density, one_mul, mass] using! h

private theorem profile_le_center_add_tail {σ t b : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1)
    (ht : t ≠ 0) (hb : b ≠ 0) (u : ℝ) :
    profile σ (t + b * u) ≤ 8 * σ / t ^ 2 +
      if |t| / (2 * |b|) < |u| then profile σ 0 else 0 := by
  by_cases hu : |t| / (2 * |b|) < |u|
  · rw [if_pos hu]
    have hc := profile_le_zero hσ hσ1 (t + b * u)
    have hp : 0 ≤ 8 * σ / t ^ 2 := by positivity
    linarith
  rw [if_neg hu, add_zero]
  have hbu : |b * u| ≤ |t| / 2 := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hu) (abs_nonneg b)
    have he : |b| * (|t| / (2 * |b|)) = |t| / 2 := by field_simp [abs_ne_zero.mpr hb]
    rwa [he] at h
  have hy : |t| / 2 ≤ |t + b * u| := by
    have h := abs_sub (t + b * u) (b * u)
    rw [add_sub_cancel_right] at h
    linarith
  have hy0 : t + b * u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hy
    linarith [abs_pos.mpr ht]
  apply (profile_le_quadratic hσ hσ1 hy0).trans
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ |t| / 2) (abs_nonneg _)).mpr hy
  rw [div_pow, sq_abs, sq_abs] at hsq
  have hh : 2 / (t + b * u) ^ 2 ≤ 8 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hy0) (sq_pos_of_ne_zero ht)).mpr
    nlinarith
  convert! mul_le_mul_of_nonneg_left hh hσ using 1 <;> ring

/-- The full rational mass has quadratic central decay and an exponentially
small low-height contribution, with its original width factor retained. -/
theorem mass_le {σ t b : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1) (ht : t ≠ 0) (hb : b ≠ 0) :
    mass σ t b ≤ 8 * σ / t ^ 2 + 2 * profile σ 0 * Real.exp (-|t| / |b|) := by
  let R := |t| / (2 * |b|)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hset : MeasurableSet {u : ℝ | R < |u|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have htail : Integrable (fun u : ℝ => if R < |u| then density u else 0) := by
    convert! integrable_density.indicator hset using 1
  have hbase := integrable_density.mul_const (8 * σ / t ^ 2)
  have hweighted := htail.const_mul (profile σ 0)
  have h := integral_mono (integrable_profile hσ hσ1 t b) (hbase.add hweighted) (fun u => by
    have h := mul_le_mul_of_nonneg_left (profile_le_center_add_tail hσ hσ1 ht hb u) (density_nonneg u)
    change density u * profile σ (t + b * u) ≤
      density u * (8 * σ / t ^ 2) + profile σ 0 * (if R < |u| then density u else 0)
    convert! h using 1
    dsimp [R]
    split_ifs <;> ring)
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hweighted, integral_mul_const, integral_const_mul, integral_density, one_mul] at h
  have hb := mul_le_mul_of_nonneg_left (integral_tail_le hR) (profile_nonneg hσ hσ1 0)
  have he : -2 * R = -|t| / |b| := by dsimp [R]; ring
  rw [he] at hb
  unfold mass
  nlinarith only [h, hb]

/-- Every nonconstant frequency at least one has the same decaying rational
allowance; no factor proportional to the frequency is introduced. -/
theorem mass_mul_le {σ t b ω : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≠ 1)
    (ht : t ≠ 0) (hb : b ≠ 0) (hω : 1 ≤ ω) :
    mass σ (ω * t) b ≤ 8 * σ / t ^ 2 + 2 * profile σ 0 * Real.exp (-|t| / |b|) := by
  have hωp : 0 < ω := zero_lt_one.trans_le hω
  have hh : |t| ≤ |ω * t| := by
    rw [abs_mul, abs_of_pos hωp]
    nlinarith [abs_nonneg t]
  have hs : t ^ 2 ≤ (ω * t) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (abs_nonneg (ω * t))).mpr hh
  have hq := div_le_div_of_nonneg_left (by positivity : 0 ≤ 8 * σ) (sq_pos_of_ne_zero ht) hs
  have he : Real.exp (-|ω * t| / |b|) ≤ Real.exp (-|t| / |b|) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) (abs_nonneg b)
  have hw := mul_le_mul_of_nonneg_left he
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (profile_nonneg hσ hσ1 0))
  exact (mass_le hσ hσ1 (mul_ne_zero hωp.ne' ht) hb).trans (add_le_add hq hw)

/-- The center derivative correction retains its full complex rational identity. -/
theorem pole_eq (c : ℂ) (hm : c ≠ 1) (hp : c ≠ -1) :
    1 / (c - 1) - 1 / (c + 1) = 2 / (c ^ 2 - 1) := by
  have hminus : c - 1 ≠ 0 := sub_ne_zero.mpr hm
  have hplus : c + 1 ≠ 0 := by
    intro h
    apply hp
    linear_combination h
  have hs : c ^ 2 - 1 ≠ 0 := by
    rw [show c ^ 2 - 1 = (c - 1) * (c + 1) by ring]
    exact mul_ne_zero hminus hplus
  field_simp
  ring

/-- Away from ordinate zero the real correction has an exact signed numerator. -/
theorem pole_re {c : ℂ} (ht : c.im ≠ 0) :
    (1 / (c - 1) - 1 / (c + 1)).re =
      2 * (c.re ^ 2 - 1 - c.im ^ 2) /
        (((c.re - 1) ^ 2 + c.im ^ 2) * ((c.re + 1) ^ 2 + c.im ^ 2)) := by
  have hm : (c.re - 1) ^ 2 + c.im ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ht)).ne'
  have hp : (c.re + 1) ^ 2 + c.im ^ 2 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero ht)).ne'
  simp only [Complex.sub_re, Complex.div_re, one_re, one_im, sub_im,
    add_re, add_im, normSq_apply, one_mul, zero_mul, add_zero, sub_zero]
  rw [show (c.re - 1) * (c.re - 1) + c.im * c.im = (c.re - 1) ^ 2 + c.im ^ 2 by ring,
    show (c.re + 1) * (c.re + 1) + c.im * c.im = (c.re + 1) ^ 2 + c.im ^ 2 by ring]
  field_simp
  ring

/-- The center correction is favorable whenever its actual squared height dominates. -/
theorem pole_re_nonpos {c : ℂ} (ht : c.im ≠ 0) (hsq : c.re ^ 2 ≤ 1 + c.im ^ 2) :
    (1 / (c - 1) - 1 / (c + 1)).re ≤ 0 := by
  rw [pole_re ht]
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  positivity

/-- Throughout the working strip at height at least two, the center
correction has favorable sign and costs no positive allowance. -/
theorem pole_re_nonpos_of_height {c : ℂ} (hσ : 0 ≤ c.re) (hσ' : c.re ≤ 3 / 2)
    (ht : 2 ≤ |c.im|) : (1 / (c - 1) - 1 / (c + 1)).re ≤ 0 := by
  have ht0 : c.im ≠ 0 := by intro h; norm_num [h] at ht
  apply pole_re_nonpos ht0
  have hy := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg c.im)).mpr ht
  rw [sq_abs] at hy
  nlinarith [pow_le_pow_left₀ hσ hσ' 2]

end
end RiemannGaussian.RationalVerticalCorrection
