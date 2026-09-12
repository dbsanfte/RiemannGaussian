/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLocalDiscBounds
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# A pole-cleared Gaussian localizer for vertical zeta strips

The exact complex carrier is pole-removed zeta divided by `s+1`, times
an entire Gaussian centered at the desired ordinate. On the right
half-plane the rational multiplier has norm at most one. The previously
proved coarse zeta growth makes the carrier bounded on the complete
strip, discharging the growth premise for Phragmen--Lindelof.
-/

namespace RiemannGaussian.ZetaGaussianLocalizer
noncomputable section
open Complex Filter Metric Set
open scoped Topology

/-- The exact rationally normalized, pole-cleared zeta function. -/
def regularized (s : ℂ) : ℂ := riemannZeta₁ s / (s + 1)

/-- The full complex Gaussian localizer, before any norm is taken. -/
def carrier (t : ℝ) (s : ℂ) : ℂ :=
  regularized s * Complex.exp ((s - Complex.I * (t : ℂ)) ^ 2)

/-- The normalized carrier keeps the original zeta function and its
rational factor exactly away from the original pole. -/
theorem regularized_eq {s : ℂ} (hs : s ≠ 1) :
    regularized s = (s - 1) / (s + 1) * riemannZeta s := by
  rw [regularized, riemannZeta₁_eq_sub_one_mul hs]
  ring

/-- The normalization denominator is nonzero on the closed right half-plane. -/
theorem add_one_ne_zero {s : ℂ} (hs : 0 ≤ s.re) : s + 1 ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
  linarith

/-- The rational pole-clearing factor has norm at most one on the right
half-plane, so it introduces no extra power of the height. -/
theorem norm_ratio_le_one {s : ℂ} (hs : 0 ≤ s.re) : ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr (add_one_ne_zero hs))).mpr
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, sub_zero, add_zero]
  nlinarith

/-- The exact normalized zeta carrier is no larger than zeta itself
where its original pole has been excluded. -/
theorem norm_regularized_le_zeta {s : ℂ} (hs : 0 ≤ s.re) (hs1 : s ≠ 1) :
    ‖regularized s‖ ≤ ‖riemannZeta s‖ := by
  rw [regularized_eq hs1, norm_mul]
  simpa using mul_le_mul_of_nonneg_right (norm_ratio_le_one hs) (norm_nonneg (riemannZeta s))

/-- The Gaussian keeps the vertical displacement and real coordinate
in its exact norm formula. -/
theorem norm_carrier (t : ℝ) (s : ℂ) :
    ‖carrier t s‖ = ‖regularized s‖ * Real.exp (s.re ^ 2 - (s.im - t) ^ 2) := by
  simp only [carrier, norm_mul, Complex.norm_exp, pow_two, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero,
    sub_zero, zero_add]

/-- The localizer is complex differentiable wherever its normalization
denominator is nonzero; the original zeta pole has been removed. -/
theorem differentiableAt_carrier (t : ℝ) {s : ℂ} (hs : s + 1 ≠ 0) :
    DifferentiableAt ℂ (carrier t) s := by
  unfold carrier regularized
  exact ((differentiable_riemannZeta₁ s).div (by fun_prop) hs).mul (by fun_prop)

/-- The existing actual-zeta disc estimate supplies polynomial growth
throughout the complete strip needed by the localizer. -/
theorem norm_poleRemoved_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖riemannZeta₁ s‖ ≤ 8 * (|s.im| + 22) ^ 2 := by
  have h := norm_localZetaPoleRemoved_le s.im
    (z := ((s.re - 3 / 2 : ℝ) : ℂ)) (by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
  have he : (3 / 2 : ℂ) + Complex.I * (s.im : ℂ) +
      ((s.re - 3 / 2 : ℝ) : ℂ) = s := by
    apply Complex.ext <;> simp
  simpa only [localZetaPoleRemoved, he] using h

/-- The normalization denominator costs at most one in the full strip. -/
theorem norm_regularized_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖regularized s‖ ≤ 8 * (|s.im| + 22) ^ 2 := by
  have hden : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  rw [regularized, norm_div]
  exact (div_le_self (norm_nonneg _) hden).trans (norm_poleRemoved_le hs hs')

/-- A quadratic polynomial is uniformly controlled by its complete
Gaussian damping, with no omitted tails. -/
theorem quadratic_gaussian_bound (t y : ℝ) :
    (|y| + 22) ^ 2 * Real.exp (-(y - t) ^ 2) ≤ 2 * (1 + (|t| + 22) ^ 2) := by
  let d : ℝ := |y - t|
  let T : ℝ := |t| + 22
  have hd : 0 ≤ d := abs_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hy : |y| + 22 ≤ d + T := by
    have h := abs_add_le (y - t) t
    rw [sub_add_cancel] at h
    dsimp [d, T]
    linarith
  have hs : (|y| + 22) ^ 2 ≤ 2 * d ^ 2 + 2 * T ^ 2 := by
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ |y| + 22) (add_nonneg hd hT) |>.mpr hy
    nlinarith [sq_nonneg (d - T)]
  have he : Real.exp (-d ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg d))
  have hx : d ^ 2 * Real.exp (-d ^ 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show d ^ 2 ≤ Real.exp (d ^ 2) by linarith [Real.add_one_le_exp (d ^ 2)])
      (Real.exp_pos (-d ^ 2)).le
    simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using h
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-d ^ 2)).le
  have ht := mul_le_mul_of_nonneg_left he (sq_nonneg T)
  have heq : (y - t) ^ 2 = d ^ 2 := by dsimp [d]; rw [sq_abs]
  rw [heq]
  change _ ≤ 2 * (1 + T ^ 2)
  nlinarith

/-- The actual complex carrier is bounded on the whole closed strip.
This coarse estimate is used only to discharge the growth condition;
the sharper line data determine the eventual strip bound. -/
theorem carrier_bounded (t : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖carrier t s‖ ≤ 16 * Real.exp 3 * (1 + (|t| + 22) ^ 2) := by
  rw [norm_carrier]
  have hr : s.re ^ 2 ≤ 3 := by nlinarith
  have he := Real.exp_le_exp.mpr (sub_le_sub_right hr ((s.im - t) ^ 2))
  have hm := mul_le_mul (norm_regularized_le hs hs') he (Real.exp_pos _).le (by positivity)
  apply hm.trans
  rw [Real.exp_sub]
  have hx := quadratic_gaussian_bound t s.im
  have hm' := mul_le_mul_of_nonneg_left hx (show 0 ≤ 8 * Real.exp 3 by positivity)
  rw [Real.exp_neg] at hm'
  convert hm' using 1 <;> ring

end
end RiemannGaussian.ZetaGaussianLocalizer
