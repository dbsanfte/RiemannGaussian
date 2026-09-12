/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# The exact differenced logarithmic phase and its derivative scales

The phase of a Dirichlet term is `-t*log(x)`. A positive shift gives
`-t*log(1+h/x)`, with derivative `t*h/(x*(x+h))`. The derivative is positive
and decreasing for positive parameters. On `X <= x <= 2*X`, `0 <= h <= X`,
the exact derivative lies between `t*h/(6*X^2)` and `t*h/X^2`.

All logarithmic identities and calculus statements retain their positive
domain hypotheses. These are the actual phases used after van der Corput
differencing, not a claimed exponential-sum cancellation theorem. Avoidance
of integer multiples of `2*pi` remains an additional derivative-test issue.
-/

namespace RiemannGaussian.LogarithmicShiftPhase
noncomputable section

/-- The unscaled-radian phase of the imaginary part of a Dirichlet term. -/
def phase (t x : ℝ) : ℝ := -t * Real.log x

/-- The exact phase difference at a real displacement, before estimation. -/
def shift (t h x : ℝ) : ℝ := phase t (x + h) - phase t x

/-- The derivative of the shifted logarithmic phase on the positive axis. -/
def slope (t h x : ℝ) : ℝ := t * h / (x * (x + h))

/-- Differencing preserves the logarithm of the exact ratio. Both
arguments are positive, so no singular logarithm is totalized away. -/
theorem shift_eq_log_ratio (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    shift t h x = -t * Real.log ((x + h) / x) := by
  rw [Real.log_div (by positivity : x + h ≠ 0) hx.ne']
  unfold shift phase
  ring

/-- The ratio form exposes the relative shift `h/x` without an
approximation or a dropped endpoint. -/
theorem shift_eq_log_one_add (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    shift t h x = -t * Real.log (1 + h / x) := by
  rw [shift_eq_log_ratio t hh hx, add_div, div_self hx.ne']

/-- The original logarithmic phase is differentiable at every positive
argument, with its signed derivative retained. -/
theorem hasDerivAt_phase (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (phase t) (-t / x) x := by
  unfold phase
  convert! (Real.hasDerivAt_log hx.ne').const_mul (-t) using 1

/-- The exact first derivative of the differenced phase. -/
theorem hasDerivAt_shift (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    HasDerivAt (shift t h) (slope t h x) x := by
  have hp : 0 < x + h := by positivity
  have hd := (((hasDerivAt_id x).add_const h).log hp.ne').const_mul (-t)
  have he := hd.sub ((Real.hasDerivAt_log hx.ne').const_mul (-t))
  unfold shift phase
  convert! he using 1
  unfold slope
  dsimp
  field_simp [hx.ne', hp.ne']
  ring

/-- The derivative of the slope is the exact signed second derivative
of the logarithmic phase difference. -/
theorem hasDerivAt_slope (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    HasDerivAt (slope t h)
      (-(t * h * (2 * x + h)) / (x ^ 2 * (x + h) ^ 2)) x := by
  have hd := (hasDerivAt_const x (t * h)).div
    ((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const h))
    (by positivity : x * (x + h) ≠ 0)
  unfold slope
  convert! hd using 1
  dsimp
  simp only [zero_mul, zero_sub, one_mul, mul_one, mul_pow]
  ring

/-- Positive height and displacement give a strictly positive slope. -/
theorem slope_pos {t h x : ℝ} (ht : 0 < t) (hh : 0 < h) (hx : 0 < x) :
    0 < slope t h x := by
  unfold slope
  positivity

/-- The actual derivative decreases on the full positive axis. -/
theorem slope_antitoneOn {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    AntitoneOn (slope t h) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hden : x * (x + h) ≤ y * (y + h) :=
    mul_le_mul hxy (by linarith) (by positivity) hy.le
  exact div_le_div_of_nonneg_left (mul_nonneg ht hh) (by positivity) hden

/-- On a genuine dyadic block with shifts no larger than its scale,
the derivative has the expected `t*h/X^2` size, with explicit constants. -/
theorem slope_dyadic_bounds {t h x X : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hX : 0 < X) (hhX : h ≤ X) (hl : X ≤ x) (hu : x ≤ 2 * X) :
    t * h / (6 * X ^ 2) ≤ slope t h x ∧ slope t h x ≤ t * h / X ^ 2 := by
  have hx : 0 < x := lt_of_lt_of_le hX hl
  have hp : 0 < x + h := by positivity
  have hlo : X ^ 2 ≤ x * (x + h) := by
    calc
      _ = X * X := pow_two X
      _ ≤ x * (x + h) := mul_le_mul hl (by linarith) hX.le hx.le
  have hhi : x * (x + h) ≤ 6 * X ^ 2 := by
    calc
      _ ≤ (2 * X) * (3 * X) := mul_le_mul hu (by linarith) hp.le (by positivity)
      _ = _ := by ring
  constructor
  · exact div_le_div_of_nonneg_left (mul_nonneg ht hh) (mul_pos hx hp) hhi
  · exact div_le_div_of_nonneg_left (mul_nonneg ht hh) (sq_pos_of_pos hX) hlo

end
end RiemannGaussian.LogarithmicShiftPhase
