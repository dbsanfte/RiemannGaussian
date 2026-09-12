/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceShift

/-!
# A conservative Gaussian source at a positive Euler center

Reflection retains the displaced finite interval before it is bounded.
The resulting positive-damping lower bound gives a rational source surplus
at a fixed physical scale. The center remains strictly right of one, so
the arithmetic application needs no boundary substitution or limiting pole.
-/

namespace RiemannGaussian.GaussianStripProfile
noncomputable section
open GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds GaussianHalfLaplaceShift

/-- Reflection turns the retained interval upper bound into a lower bound
at every nonnegative real damping. -/
theorem halfGaussian_shift_lower {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) :
    Real.exp (q ^ 2 / (4 * B)) * (Real.sqrt (Real.pi / B) / 2 - q / (2 * B)) ≤
      halfGaussian B q := by
  have hr := halfGaussian_reflection hB q
  have hu := halfGaussian_neg_shift_upper hB hq
  nlinarith only [hr, hu]

/-- The target horizontal width of the explicit Gaussian band. -/
def width : ℝ := 1 / 450000

/-- A strictly positive center shift, one thousandth of the target width. -/
def shift : ℝ := width / 1000

/-- The physical Gaussian scale is fixed independently of any phase family. -/
def gaussianScale : ℝ := 4 * width ^ 2

/-- The positive-damping Gaussian source has a conservative rational
lower enclosure after the exact scale change. -/
theorem source_lower : (152000 : ℝ) ≤ halfGaussian gaussianScale (shift + width) := by
  have hsq : (443 / 1000 : ℝ) ≤ Real.sqrt (Real.pi / 4) / 2 := by
    have h := Real.sq_sqrt (show 0 ≤ Real.pi / 4 by positivity)
    nlinarith [Real.pi_gt_d2, Real.sqrt_nonneg (Real.pi / 4)]
  have he := Real.add_one_le_exp ((1001 / 1000 : ℝ) ^ 2 / 16)
  have h := halfGaussian_shift_lower (by norm_num : (0 : ℝ) < 4)
    (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
  norm_num only at h he
  have hlo : (1 + (1001 / 1000 : ℝ) ^ 2 / 16) * (443 / 1000 - (1001 / 1000) / 8) ≤
      halfGaussian 4 (1001 / 1000) := by
    apply le_trans ?_ h
    convert mul_le_mul he
      (by linarith : (443 / 1000 : ℝ) - (1001 / 1000) / 8 ≤
        Real.sqrt (Real.pi / 4) / 2 - (1001 / 1000) / 8)
      (by norm_num) (Real.exp_pos _).le using 1 <;> norm_num
  have hs := halfGaussian_scale (by norm_num [width] : 0 < width) 4 (1001 / 1000)
  have hd : (1001 / 1000 : ℝ) * width = shift + width := by unfold shift; ring
  rw [hd] at hs
  change width * halfGaussian gaussianScale (shift + width) = _ at hs
  rw [← hs] at hlo
  norm_num [width] at hlo ⊢
  linarith

/-- The constant Gaussian channel is bounded at zero damping, after
retaining its actual positive shift. -/
theorem constant_upper : halfGaussian gaussianScale shift ≤ (199575 : ℝ) := by
  have hsq : Real.sqrt Real.pi / 4 ≤ (887 / 2000 : ℝ) := by
    have h := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.pi_lt_d4, Real.sqrt_nonneg Real.pi]
  have hs := halfGaussian_scale (by norm_num [width] : 0 < width) 4 0
  simp only [zero_mul] at hs
  change width * halfGaussian gaussianScale 0 = halfGaussian 4 0 at hs
  have hroot : Real.sqrt (Real.pi / 4) = Real.sqrt Real.pi / 2 := by
    rw [Real.sqrt_div Real.pi_pos.le]
    norm_num
  rw [halfGaussian_zero 4, hroot] at hs
  have hu := halfGaussian_antitone (by norm_num [gaussianScale, width] : 0 < gaussianScale)
    (show 0 ≤ shift by norm_num [shift, width])
  change halfGaussian gaussianScale shift ≤ halfGaussian gaussianScale 0 at hu
  norm_num [width] at hs
  nlinarith only [hs, hsq, hu]

end
end RiemannGaussian.GaussianStripProfile
