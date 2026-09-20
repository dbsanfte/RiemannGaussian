/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReserveExact

/-!
# The exact retained source and a stronger uniform deficit

Evaluating the whole positive reserve simplifies the remaining harmonic cost.
For a simple exposed zero the retained signed carrier must eventually be
strictly below `-3/40`. An independent cofinal arithmetic floor at `-3/40`
would contradict this; such a floor is not asserted here.
-/

namespace RiemannGaussian.ZetaRieszMaskSupport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszWingReserve RieszHarmonicCostBounds ZetaRieszPrimeCountFrequency

/-- The harmonic cost after evaluating the complete positive reserve. -/
def retainedCost (u : ℝ) : ℝ :=
  Real.log (32 / 13) / (-2 * u * Real.log u) - Real.log (19 / 13)

/-- The exact reserve joins adjacent harmonic intervals, preserving their signs. -/
theorem paidCost_sub_reserveMass (u : ℝ) :
    paidHarmonicCost u - reserveMass u = retainedCost u := by
  have h₁ : Real.log (32 / 15 : ℝ) + Real.log (15 / 13 : ℝ) = Real.log (32 / 13 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  have h₂ : Real.log (17 / 15 : ℝ) + Real.log (19 / 17 : ℝ) +
      Real.log (15 / 13 : ℝ) = Real.log (19 / 13 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    ring
  unfold paidHarmonicCost reserveMass retainedCost
  rw [← h₁, ← h₂]
  ring

/-- The literal retained carrier has an exact complex source limit after every paid component is removed. -/
theorem tendsto_retained_exact_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (retainedRemainder (3 / 2 - rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (retainedCost (3 / 2 - rho.1.re) : ℂ))) := by
  have h := (tendsto_retained_add_reserve rho hrho hexposed huh).sub
    ((tendsto_reserve_exact rho hrho hexposed huh).comp tendsto_dyadicMomentOrder)
  have he := congrArg Complex.ofReal (paidCost_sub_reserveMass (3 / 2 - rho.1.re))
  push_cast at he
  have hlim : -(analyticZetaZeroMultiplicity rho : ℂ) +
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        (paidHarmonicCost (3 / 2 - rho.1.re) : ℂ) -
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        (reserveMass (3 / 2 - rho.1.re) : ℂ) =
      -(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (retainedCost (3 / 2 - rho.1.re) : ℂ) := by
    linear_combination (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * he
  rw [hlim] at h
  exact h.congr' (Eventually.of_forall fun _ => by simp only [Function.comp_def]; ring)

private theorem reserve_log_scale_lower {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) : 691 / 1000 ≤ -2 * u * Real.log u := by
  have hu0 : 0 < u := by linarith
  have huq : u ≤ 503 / 1000 := huh.trans ZetaRieszJointAllocation.radius_ceiling
  have hh := Real.log_le_sub_one_of_pos (show 0 < 2 * u by positivity)
  rw [Real.log_mul (by norm_num) hu0.ne'] at hh
  have hlog2 : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * u by positivity)
  have hml := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2 * u by positivity)
  have hq := mul_nonneg (show 0 ≤ u - 1 / 2 by linarith)
    (show 0 ≤ 503 / 1000 - u by linarith)
  nlinarith

private theorem log_thirtytwo_thirteenths_lt : Real.log (32 / 13 : ℝ) < 901 / 1000 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 901 / 1000) 10
  norm_num [Finset.sum_range_succ] at he
  linarith

private theorem log_nineteen_thirteenths_gt : (379 / 1000 : ℝ) < Real.log (19 / 13) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3 / 16)
    (by norm_num : (3 / 16 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A rational bound for the complete retained cost, uniform throughout the reserve radius interval. -/
theorem retainedCost_lt_thirtyseven_fortieths {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) : retainedCost u < 37 / 40 := by
  have hD := reserve_log_scale_lower hu huh
  have hDp : 0 < -2 * u * Real.log u := by linarith
  have hlo := log_nineteen_thirteenths_gt
  have hhi := log_thirtytwo_thirteenths_lt
  have hm := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 37 / 40 + Real.log (19 / 13 : ℝ) by linarith)
  unfold retainedCost
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ hDp).mpr
  nlinarith

/-- A simple exposed zero forces the retained sum below a uniform negative rational threshold; this is the source-side deficit, not an independent arithmetic floor. -/
theorem eventually_retained_re_lt_neg_three_fortieths (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ∀ᶠ j in atTop, (retainedRemainder (3 / 2 - rho.1.re) rho.1.im j).re < -(3 / 40 : ℝ) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := retainedCost_lt_thirtyseven_fortieths hu huh.le
  have h := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_retained_exact_source rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, one_mul, Complex.add_re,
    Complex.neg_re, Complex.one_re, Complex.ofReal_re] at h
  exact h.eventually (eventually_lt_nhds (by linarith))

end
end RiemannGaussian.ZetaRieszMaskSupport
