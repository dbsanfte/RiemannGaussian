/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscCanonicalBounds
import RiemannGaussian.AnalyticDiscCaratheodory

/-!
# Radius-uniform logarithmic derivative control

A nonvanishing analytic disc function has a normalized logarithm retaining
its exact center value. A one-sided growth allowance controls the complete
complex derivative at the center by `2 * allowance / radius`. The radius
and the center cost remain explicit for shrinking-disc applications.
-/

namespace RiemannGaussian.AnalyticDiscLogarithm
noncomputable section
open Complex Filter Metric Set Topology

variable {g L : ℂ → ℂ} {R : ℝ}

/-- A zero-free analytic disc has a logarithmic primitive normalized
at its center. -/
theorem exists_logarithm (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z := by
  have hd : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have ha := hg z (ball_subset_closedBall hz)
    have hl : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using ha.deriv.div ha (hne z (ball_subset_closedBall hz))
    exact hl.differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at 0 0

/-- The normalized primitive exponentiates to the full original
function divided by its actual nonzero center value. -/
theorem exp_mul_center (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) (hL0 : L 0 = 0)
    (hL : ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z)
    {z : ℂ} (hz : z ∈ ball 0 R) : Complex.exp (L z) * g 0 = g z := by
  let q : ℂ → ℂ := (fun w ↦ Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    exact ((hL w hw).neg.cexp.mul
      (hg w (ball_subset_closedBall hw)).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hq : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w) w :=
      (hL w hw).neg.cexp.mul (hg w (ball_subset_closedBall hw)).differentiableAt.hasDerivAt
    rw [hq.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply, mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ (hne w (ball_subset_closedBall hw))]
    ring
  have he := isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
    hdiff hderiv hzero hz
  have hg0 : g 0 = Complex.exp (-L z) * g z := by simpa [q, hL0] using he
  rw [hg0, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The real part of the normalized logarithm pays exactly the growth
allowance and the center's negative logarithm. -/
theorem re_le (hR : 0 < R) (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0) (hL0 : L 0 = 0)
    (hL : ∀ z ∈ ball 0 R, HasDerivAt L (logDeriv g z) z)
    {B C : ℝ} (hB : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B)
    (hC : -Real.log ‖g 0‖ ≤ C) {z : ℂ} (hz : z ∈ ball 0 R) :
    (L z).re ≤ B + C := by
  have hp0 : 0 < ‖g 0‖ := norm_pos_iff.mpr (hne 0 (mem_closedBall_self hR.le))
  have hpz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z (ball_subset_closedBall hz))
  have he := congrArg norm (exp_mul_center hR hg hne hL0 hL hz)
  rw [norm_mul, Complex.norm_exp] at he
  have hl := congrArg Real.log he
  rw [Real.log_mul (Real.exp_pos _).ne' hp0.ne', Real.log_exp] at hl
  have hb := Real.log_le_log hpz (hB z (ball_subset_closedBall hz))
  rw [Real.log_exp] at hb
  linarith

/-- The sharp Carathéodory estimate controls the complete logarithmic
derivative at the center with constant two, retaining the actual center
allowance and every positive disc radius. -/
theorem norm_logDeriv_center_le_sharp (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0)
    {B C : ℝ} (hA : 0 < B + C)
    (hB : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B)
    (hC : -Real.log ‖g 0‖ ≤ C) : ‖logDeriv g 0‖ ≤ 2 * (B + C) / R := by
  obtain ⟨L, hL0, hL⟩ := exists_logarithm hg hne
  have hd0 := AnalyticDiscCaratheodory.norm_deriv_zero_le hA hR
    (fun z hz ↦ (hL z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ re_le hR hg hne hL0 hL hB hC hz) hL0
  rw [(hL 0 (mem_ball_self hR)).deriv] at hd0
  exact hd0

/-- The preceding constant-four estimate follows from the sharp bound;
the stronger theorem is used by the actual zeta exclusion chain. -/
theorem norm_logDeriv_center_le (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hne : ∀ z ∈ closedBall 0 R, g z ≠ 0)
    {B C : ℝ} (hA : 0 < B + C)
    (hB : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ Real.exp B)
    (hC : -Real.log ‖g 0‖ ≤ C) : ‖logDeriv g 0‖ ≤ 4 * (B + C) / R := by
  apply (norm_logDeriv_center_le_sharp hR hg hne hA hB hC).trans
  gcongr
  norm_num

end
end RiemannGaussian.AnalyticDiscLogarithm
