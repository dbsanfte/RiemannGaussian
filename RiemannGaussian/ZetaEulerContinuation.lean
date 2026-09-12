/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerCell

/-!
# Direct Euler continuation of the actual zeta function

The regularized complex Euler cells converge locally uniformly on the
entire positive half-plane, including the pole coordinate. The analytic
identity principle identifies their full sum with `1-riemannZeta₁`.
Dividing the final exact identity, away from the actual pole, reconstructs
zeta directly from ordinary Dirichlet cells without any eta denominator.
-/

namespace RiemannGaussian.ZetaEulerContinuation
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology ZetaEulerCell

/-- The complete series of entire pole-cleared Euler cells. -/
def regularizedSum (s : ℂ) : ℂ := ∑' n, regularizedCell s n

/-- The pole-cleared Euler series is complex differentiable throughout
the full positive half-plane, with local uniform summability proved. -/
theorem differentiableOn_regularizedSum :
    DifferentiableOn ℂ regularizedSum {s : ℂ | 0 < s.re} := by
  intro z hz
  change 0 < z.re at hz
  let d := z.re / 2
  let K := ‖z‖ + d
  have hd : 0 < d := by dsimp [d]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm := (summable_envelope hd).mul_left ((1 + K) * K)
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ ball z d) :
      ‖regularizedCell w n‖ ≤ (1 + K) * K * (n + 1 : ℝ) ^ (-d - 1) := by
    have hn : ‖w - z‖ < d := by simpa only [mem_ball, dist_eq_norm] using hw
    have hre : d < w.re := by
      have h := Complex.abs_re_le_norm (w - z)
      simp only [sub_re] at h
      dsimp only [d] at hn ⊢
      linarith [neg_le_abs (w.re - z.re)]
    have hnw : ‖w‖ ≤ K := by
      have h := norm_add_le (w - z) z
      simp only [sub_add_cancel] at h
      dsimp only [K]
      linarith
    have hn1 : ‖1 - w‖ ≤ 1 + K := by
      have h := norm_sub_le (1 : ℂ) w
      simp only [norm_one] at h
      linarith
    have hp : (n + 1 : ℝ) ^ (-w.re - 1) ≤ (n + 1 : ℝ) ^ (-d - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    rw [regularizedCell_eq, norm_mul]
    calc
      _ ≤ ‖1 - w‖ * (‖w‖ * (n + 1 : ℝ) ^ (-w.re - 1)) :=
        mul_le_mul_of_nonneg_left (norm_cell_le (hd.trans hre) n) (norm_nonneg _)
      _ ≤ (1 + K) * (K * (n + 1 : ℝ) ^ (-d - 1)) :=
        mul_le_mul hn1 (mul_le_mul hnw hp (by positivity) hK) (by positivity) (by positivity)
      _ = _ := by ring
  have hl : DifferentiableOn ℂ regularizedSum (ball z d) := by
    unfold regularizedSum
    exact Complex.differentiableOn_tsum_of_summable_norm hm
      (fun n ↦ (differentiable_regularizedCell n).differentiableOn) isOpen_ball hb
  exact (hl.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hd))).differentiableWithinAt

/-- The actual regularized Euler sum is analytic, including at `s=1`. -/
theorem analyticOnNhd_regularizedSum :
    AnalyticOnNhd ℂ regularizedSum {s : ℂ | 0 < s.re} :=
  differentiableOn_regularizedSum.analyticOnNhd (Complex.isOpen_re_gt 0)

/-- The full complex upper endpoint tends to zero in the original
absolute-convergence half-plane. -/
theorem endpoint_tendsto_zero {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ (N + 1 : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1)).comp ht
  apply h.congr
  intro N
  rw [show (N + 1 : ℂ) = ((N + 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Function.comp_apply, sub_re, one_re, neg_sub]

/-- The ordinary convergent Dirichlet series identifies the complete
regularized sum on the Euler half-plane. -/
theorem regularizedSum_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    regularizedSum s = 1 - riemannZeta₁ s := by
  have hp : Tendsto (fun N : ℕ ↦ partialSum N s) atTop (𝓝 (riemannZeta s)) := by
    simpa only [partialSum, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one,
      Complex.ofReal_add, Complex.ofReal_one] using
      (hasSum_nat_add_one_cpow_neg_riemannZeta hs).tendsto_sum_nat
  have he := endpoint_tendsto_zero hs
  have hlim := ((hp.const_mul (1 - s)).sub he).add_const 1
  have hreg := (summable_regularizedCell (by linarith : 0 < s.re)).hasSum.tendsto_sum_nat
  simp only [sum_regularizedCell] at hreg
  simp only [sub_zero] at hlim
  have hu := tendsto_nhds_unique hreg hlim
  have hsne : s ≠ 1 := by intro h; simp [h] at hs
  have hmul : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
  change regularizedSum s = (1 - s) * riemannZeta s + 1 at hu
  linear_combination hu - hmul

/-- Analytic continuation identifies the entire Euler-cell series
with the actual pole-cleared zeta function on the positive half-plane. -/
theorem regularizedSum_eq {s : ℂ} (hs : 0 < s.re) :
    regularizedSum s = 1 - riemannZeta₁ s := by
  have hr : AnalyticOnNhd ℂ (fun s : ℂ ↦ 1 - riemannZeta₁ s) {s : ℂ | 0 < s.re} :=
    ((differentiable_const (1 : ℂ)).sub differentiable_riemannZeta₁).differentiableOn.analyticOnNhd
      (Complex.isOpen_re_gt 0)
  have he : regularizedSum =ᶠ[𝓝 (2 : ℂ)] (fun s ↦ 1 - riemannZeta₁ s) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s h
    exact regularizedSum_eq_of_one_lt_re h
  exact analyticOnNhd_regularizedSum.eqOn_of_preconnected_of_eventuallyEq hr
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by norm_num : (2 : ℂ).re > 0) he hs

/-- The original signed complex Euler remainder reconstructs actual
zeta with only its genuine simple pole denominator. -/
theorem tsum_cell_eq {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) :
    (∑' n, cell s n) = riemannZeta s - 1 / (s - 1) := by
  have h := regularizedSum_eq hs
  have hm : (s - 1) * riemannZeta s = riemannZeta₁ s := by
    rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
  simp only [regularizedSum, regularizedCell_eq, tsum_mul_left, ← hm] at h
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hsne) : 1 - s ≠ 0)
  rw [h]
  field_simp
  ring

end
end RiemannGaussian.ZetaEulerContinuation
