/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianComplexHalfMoments

/-!
# The full inverse-cube remainder of the Gaussian Laplace pole

The exact complex moment recurrence retains the vanishing first Gaussian
endpoint derivative. The remainder after subtracting the original pole has
the uniform bound `12*B/norm(z)^3` on the closed right half-plane away from
zero. Only after proving that bound is it weakened to the inverse-square
form needed by a smoothed strip comparison at a fixed distance cutoff.
-/

namespace RiemannGaussian.GaussianLaplacePoleRemainder
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiZeroPair GaussianComplexHalfMoments

/-- The original complex transform minus its actual endpoint pole. -/
def remainder (B : ℝ) (z : ℂ) : ℂ := transform B z - 1 / z

/-- Nonnegative real damping bounds each complete complex moment by its
genuine positive zero-damping mass; the estimate follows the exact recurrence. -/
theorem norm_moment_le_zero {B : ℝ} (hB : 0 < B) (n : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖moment B n z‖ ≤ (moment B n 0).re := by
  have hi : Integrable (fun t : ℝ => t ^ n * window B t) := by
    simpa only [atom, neg_zero, zero_mul, Complex.exp_zero, mul_one,
      Complex.ofReal_re] using! (integrable_atom hB n 0).re
  have hbound : ‖moment B n z‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ n * window B t := by
    apply norm_integral_le_of_norm_le hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_atom, abs_of_pos ht]
    apply mul_le_of_le_one_right (mul_nonneg (pow_nonneg ht.le n) (Real.exp_pos _).le)
    apply Real.exp_le_one_iff.mpr
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hz ht.le)
  have he : (∫ t in Ioi (0 : ℝ), t ^ n * window B t) = (moment B n 0).re := by
    simpa only [moment, atom, neg_zero, zero_mul, Complex.exp_zero, mul_one,
      Complex.ofReal_re] using! (integral_re (integrable_atom hB n 0).integrableOn)
  exact hbound.trans_eq he

/-- The first complex moment has its sharp positive half-Gaussian majorant. -/
theorem norm_moment_one_le {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖moment B 1 z‖ ≤ 1 / (2 * B) := by
  have h := norm_moment_le_zero hB 1 hz
  rw [moment_one_zero hB] at h
  norm_cast at h

/-- The third complex moment has its sharp positive half-Gaussian majorant. -/
theorem norm_moment_three_le {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖moment B 3 z‖ ≤ 1 / (2 * B ^ 2) := by
  have h := norm_moment_le_zero hB 3 hz
  rw [moment_three_zero hB] at h
  norm_cast at h

/-- The full complex inverse-cube identity keeps both odd moments and
the signed second endpoint together before any norm is taken. -/
theorem remainder_eq {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : z ≠ 0) :
    remainder B z = (-2 * (B : ℂ) + 12 * (B : ℂ) ^ 2 * moment B 1 z -
      8 * (B : ℂ) ^ 3 * moment B 3 z) / z ^ 3 := by
  have h := third_endpoint_identity hB z
  unfold remainder
  field_simp
  linear_combination h

/-- The entire original Gaussian Laplace remainder has inverse-cube
decay with a coefficient linear in the Gaussian scale, uniformly through
the imaginary axis. No first-derivative endpoint cost is introduced. -/
theorem norm_remainder_le {B : ℝ} (hB : 0 < B) {z : ℂ} (hz0 : 0 ≤ z.re) (hz : z ≠ 0) :
    ‖remainder B z‖ ≤ 12 * B / ‖z‖ ^ 3 := by
  have h1 := norm_moment_one_le hB hz0
  have h3 := norm_moment_three_le hB hz0
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [remainder_eq hB hz, norm_div, norm_pow]
  calc
    _ ≤ (2 * B + 12 * B ^ 2 * ‖moment B 1 z‖ + 8 * B ^ 3 * ‖moment B 3 z‖) / ‖z‖ ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ ‖-2 * (B : ℂ) + 12 * (B : ℂ) ^ 2 * moment B 1 z‖ +
            ‖8 * (B : ℂ) ^ 3 * moment B 3 z‖ := norm_sub_le _ _
        _ ≤ (‖-2 * (B : ℂ)‖ + ‖12 * (B : ℂ) ^ 2 * moment B 1 z‖) +
            ‖8 * (B : ℂ) ^ 3 * moment B 3 z‖ := add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by
          norm_num [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    _ ≤ (2 * B + 12 * B ^ 2 * (1 / (2 * B)) + 8 * B ^ 3 * (1 / (2 * B ^ 2))) / ‖z‖ ^ 3 := by
      gcongr
    _ = _ := by field_simp; ring

/-- A geometric distance cutoff converts the proved cubic estimate into
the precise inverse-square allowance needed for a complete divisor tail. -/
theorem norm_remainder_le_inverse_square {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hzη : η ≤ ‖z‖) :
    ‖remainder B z‖ ≤ (12 * B / η) / ‖z‖ ^ 2 := by
  have hnz : 0 < ‖z‖ := hη.trans_le hzη
  apply (norm_remainder_le hB hz0 (norm_pos_iff.mp hnz)).trans
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hzη (sq_nonneg ‖z‖)]

end
end RiemannGaussian.GaussianLaplacePoleRemainder
