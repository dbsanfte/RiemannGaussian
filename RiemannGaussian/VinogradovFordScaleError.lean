/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordSchedule

/-!
# Quantitative error in Ford's original backward scales

Equation (3.12) of Ford gives a factor one half on the excess over the
stationary scale. A quadratic supersolution sums every triangular forcing
term and retains the finite terminal error. In particular the first scale
is at most `phiStar + 2^(-n)/r + 2*phiStar/(k*r)`.
No moment or prime-supply hypothesis is used in this scalar estimate.
-/

namespace RiemannGaussian.VinogradovFordScaleError
noncomputable section
open VinogradovFordScales VinogradovFordSchedule

/-- Ford's (3.12), with the full triangular forcing term retained. -/
theorem previous_excess_le_half {k r d : ℕ} {delta psi : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (hdepth : (d : ℝ) * ((d : ℝ) - 1) ≤ depthReserve k r delta)
    (hpsi : stationaryScale k r delta ≤ psi) :
    previousScale k d r delta psi - stationaryScale k r delta ≤
      (psi - stationaryScale k r delta) / 2 +
        (d : ℝ) * ((d : ℝ) - 1) / (4 * k * r) * stationaryScale k r delta := by
  have hy := (depth_nonneg d).trans hdepth
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : previousScale k d r delta psi - stationaryScale k r delta =
      (2 * (k : ℝ) * r + (d : ℝ) * ((d : ℝ) - 1) - depthReserve k r delta) /
          (4 * k * r) * (psi - stationaryScale k r delta) +
        (d : ℝ) * ((d : ℝ) - 1) / (4 * k * r) * stationaryScale k r delta := by
    conv_lhs => rw [← stationary_fixed hk hr hy]
    unfold previousScale depthReserve
    push_cast
    field_simp
    ring
  rw [he]
  apply add_le_add _ le_rfl
  have hc : (2 * (k : ℝ) * r + (d : ℝ) * ((d : ℝ) - 1) - depthReserve k r delta) /
      (4 * k * r) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k * r)).mpr
    linarith
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
    mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hpsi)

/-- A finite quadratic supersolution sums all triangular errors without
enlarging the stationary term or losing the terminal geometric factor. -/
theorem backwardScale_excess_le {k r : ℕ} {delta : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) (d t : ℕ)
    (hdepth : ((d + t : ℕ) : ℝ) * (((d + t : ℕ) : ℝ) - 1) ≤ depthReserve k r delta) :
    backwardScale k r delta d t - stationaryScale k r delta ≤
      (1 / 2 : ℝ) ^ t * (1 / (r : ℝ) - stationaryScale k r delta) +
        (2 * (d : ℝ) ^ 2 + 6 * d + 8) / (4 * k * r) * stationaryScale k r delta := by
  induction t generalizing d with
  | zero =>
    have hy := (depth_nonneg (d + 0)).trans hdepth
    have hstar := (stationary_bounds hk hr hy).1.le
    simp only [backwardScale, pow_zero, one_mul]
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (by positivity) (by positivity)) hstar)
  | succ t ih =>
    have hnext := ih (d + 1) (by simpa only [Nat.add_assoc, Nat.add_comm 1] using hdepth)
    have hd := (depth_mono (by omega : d + 1 ≤ d + (t + 1))).trans hdepth
    have hy := (depth_nonneg (d + (t + 1))).trans hdepth
    have hs := stationary_le_backwardScale hk hr hy hdelta (d + 1) t
    have hp := previous_excess_le_half hk hr hd hs
    change previousScale k (d + 1) r delta (backwardScale k r delta (d + 1) t) -
      stationaryScale k r delta ≤ _
    refine hp.trans ?_
    calc
      _ ≤ ((1 / 2 : ℝ) ^ t * (1 / (r : ℝ) - stationaryScale k r delta) +
          (2 * ((d + 1 : ℕ) : ℝ) ^ 2 + 6 * ((d + 1 : ℕ) : ℝ) + 8) /
            (4 * k * r) * stationaryScale k r delta) / 2 +
          ((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) /
            (4 * k * r) * stationaryScale k r delta := by linarith
      _ = _ := by push_cast; rw [pow_succ]; ring

/-- The exact first-scale allowance from the proof of Ford's Lemma 3.6. -/
theorem first_scale_le {k r n : ℕ} {delta : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta) :
    schedule k r n delta 0 ≤ stationaryScale k r delta +
      (1 / 2 : ℝ) ^ n / r + 2 * stationaryScale k r delta / (k * r) := by
  have hy := (depth_nonneg n).trans hdepth
  have hstar := (stationary_bounds hk hr hy).1.le
  have hh := backwardScale_excess_le hk hr hdelta 0 n (by simpa using hdepth)
  have he : (2 * (0 : ℝ) ^ 2 + 6 * 0 + 8) / (4 * k * r) * stationaryScale k r delta =
      2 * stationaryScale k r delta / (k * r) := by ring
  simp only [Nat.cast_zero] at hh
  rw [he] at hh
  have hg := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n) hstar
  simp only [schedule, Nat.sub_zero]
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

end
end RiemannGaussian.VinogradovFordScaleError
