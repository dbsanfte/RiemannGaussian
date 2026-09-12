/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogarithmicShiftAllowance
import RiemannGaussian.SechVerticalKernel

/-!
# Complete positive logarithmic mass in the vertical zeta detector

The literal zeta positive-log carrier is integrable against the original
hyperbolic-secant density over the whole real line. Its integral has an
explicit upper bound uniform in order, central height and real shift.
The signed logarithm and its negative part are not identified with this
positive carrier; their zero-sensitive reconstruction remains separate.
-/

namespace RiemannGaussian.ZetaSechVerticalBound
noncomputable section
open MeasureTheory Filter ZetaNearOneLogProfile ZetaLogarithmicShiftAllowance
open SechVerticalKernel
open scoped Topology

/-- The actual zeta positive logarithm with the full detector density. -/
def integrand (k : ℕ) (t a u : ℝ) : ℝ := density u * positiveLog k (t + a * u)

/-- The carrier is the literal positive logarithm of zeta on the
shifted vertical line, with the original detector denominator. -/
theorem integrand_eq (k : ℕ) (t a u : ℝ) : integrand k t a u =
    Real.posLog ‖riemannZeta ((DirichletPowerParameters.line k : ℂ) +
      Complex.I * ((t + a * u : ℝ) : ℂ))‖ / (2 * Real.cosh u ^ 2) := by
  unfold integrand density positiveLog
  ring

/-- The full positive-log integrand is nonnegative, including zero ordinates. -/
theorem integrand_nonneg (k : ℕ) (t a u : ℝ) : 0 ≤ integrand k t a u :=
  mul_nonneg (density_nonneg u) Real.posLog_nonneg

/-- The complete positive-log detector integrand is continuous. -/
theorem continuous_integrand (k : ℕ) (t a : ℝ) : Continuous (integrand k t a) := by
  have hs : Continuous (fun u : ℝ => t + a * u) := by fun_prop
  exact continuous_density.mul ((continuous_positiveLog k).comp hs)

/-- One integrable affine Laplace envelope bounds the actual integrand
at every ordinate, with no excluded local window or discarded far tail. -/
theorem integrand_le (k : ℕ) (hk : 1 ≤ k) (t a u : ℝ) :
    integrand k t a u ≤
      (profile k t + shiftCost k t a * |u|) * Real.exp (-|u|) := by
  have h := mul_le_mul (density_le_exp u) (positiveLog_shift_le k hk t a u)
    (show 0 ≤ positiveLog k (t + a * u) from Real.posLog_nonneg) (Real.exp_pos _).le
  simpa only [integrand, mul_comm] using h

/-- The positive logarithmic mass of the actual zeta function is
genuinely integrable over the entire detector line. -/
theorem integrable_integrand (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    Integrable (integrand k t a) := by
  apply (integrable_affine (profile k t) (shiftCost k t a)).mono'
    (continuous_integrand k t a).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg k t a u)]
  exact integrand_le k hk t a u

/-- The full positive logarithmic detector mass has an explicit bound
with both order and shift dependence retained. -/
theorem integral_bound (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    (∫ u : ℝ, integrand k t a u) ≤ 2 * profile k t + 2 * shiftCost k t a := by
  have h := integral_mono (integrable_integrand k hk t a)
    (integrable_affine (profile k t) (shiftCost k t a)) (integrand_le k hk t a)
  rwa [integral_affine] at h

/-- The complete vertical zeta allowance has an order-independent
shift error, decaying inversely with the enlarged central height. -/
theorem integral_bound_simple (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    (∫ u : ℝ, integrand k t a u) ≤ 2 * profile k t + 6 * |a| / height t := by
  apply (integral_bound k hk t a).trans
  have h := shiftCost_le k t a
  have he : 6 * |a| / height t = 2 * (3 * |a| / height t) := by ring
  rw [he]
  linarith

/-- Symmetric finite integrals converge to the genuine full positive
logarithmic detector mass, using its proved absolute integrability. -/
theorem truncation_tendsto (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    Tendsto (fun R : ℝ => ∫ u in -R..R, integrand k t a u) atTop
      (𝓝 (∫ u : ℝ, integrand k t a u)) :=
  intervalIntegral_tendsto_integral (integrable_integrand k hk t a)
    tendsto_neg_atTop_atBot tendsto_id

end
end RiemannGaussian.ZetaSechVerticalBound
