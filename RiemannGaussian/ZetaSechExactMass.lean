/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SechVerticalMoments
import RiemannGaussian.ZetaSechSignedWindows

/-!
# The actual zeta detector with its exact kernel mass

The previously proved all-height zeta logarithmic bound is integrated
against the original density. Its leading allowance is halved, and its
affine shift coefficient improves from two to `log 2`. The whole negative
logarithmic mass is retained on every finite signed window.
-/

namespace RiemannGaussian.ZetaSechExactMass
noncomputable section
open MeasureTheory ZetaNearOneLogProfile ZetaLogarithmicShiftAllowance
open SechVerticalKernel SechVerticalMoments ZetaSechVerticalBound ZetaSechSignedWindows

/-- Exact integration of the density improves the actual complete
positive logarithmic mass, uniformly in order, ordinate and shift. -/
theorem integral_bound (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) :
    (∫ u : ℝ, ZetaSechVerticalBound.integrand k t a u) ≤
      profile k t + Real.log 2 * shiftCost k t a := by
  have h := integral_mono (integrable_integrand k hk t a)
    (integrable_affine_density (profile k t) (shiftCost k t a))
    (fun u => mul_le_mul_of_nonneg_left (positiveLog_shift_le k hk t a u) (density_nonneg u))
  rwa [integral_affine_density] at h

/-- The original signed zeta logarithm has the sharper full allowance
while retaining all negative mass, including through every zero singularity. -/
theorem window_bound_with_negative (k : ℕ) (hk : 1 ≤ k) (t a : ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      profile k t + Real.log 2 * shiftCost k t a -
        ∫ u in l..r, negativeIntegrand k t a u := by
  rw [window_exact]
  apply sub_le_sub_right
  have hp : (∫ u in l..r, ZetaSechVerticalBound.integrand k t a u) ≤
      ∫ u : ℝ, ZetaSechVerticalBound.integrand k t a u := by
    rw [intervalIntegral.integral_of_le hlr]
    exact setIntegral_le_integral (integrable_integrand k hk t a)
      (ae_of_all _ (integrand_nonneg k t a))
  exact hp.trans (integral_bound k hk t a)

/-- Every finite signed window obeys the improved complete-line bound,
with no global integrability assumption on the negative logarithm. -/
theorem window_bound (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      profile k t + Real.log 2 * shiftCost k t a := by
  have hn := intervalIntegral.integral_nonneg (μ := volume) hlr
    (fun u _ => negativeIntegrand_nonneg k t a u)
  linarith [window_bound_with_negative k hk t a hlr]

/-- The actual signed-window bound has an explicit inverse-height shift
cost with its exact `log 2` moment coefficient. -/
theorem window_bound_simple (k : ℕ) (hk : 1 ≤ k) (t a : ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      profile k t + 3 * Real.log 2 * |a| / height t := by
  apply (window_bound k hk t a hlr).trans
  have h := mul_le_mul_of_nonneg_left (shiftCost_le k t a)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  calc
    _ ≤ profile k t + Real.log 2 * (3 * |a| / height t) := add_le_add_right h _
    _ = _ := by ring

end
end RiemannGaussian.ZetaSechExactMass
