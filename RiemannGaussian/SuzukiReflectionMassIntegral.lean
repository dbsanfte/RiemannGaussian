/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassCurrent

/-!
# Finite signed reflection integrals with an independent explicit allowance

Integration by parts removes the horizontal derivative of the complex
carrier. The remaining signed mass variation is retained. Every other
term has an explicit allowance involving only the reflection and heat
weights, divided by the positive smoothing radius. All integrability
conditions are proved on the actual finite interval. No area or shrinking
puncture limit is exchanged with this one-dimensional integral.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- A purely explicit envelope for the weight-derivative and heat remainder. -/
def suzukiXiReflectionMassAllowance (rho : NontrivialZetaZero) (r c tau y x : ℝ) : ℝ :=
  ‖deriv (suzukiXiHorizontalReflectionHeat rho c tau y) x‖ / r +
    ‖suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I * ((x : ℂ) + (y : ℂ) * I))‖ / (2*r)

/-- The finite weight budget is independent of the smoothing radius and of eta values. -/
def suzukiXiReflectionMassBudget (rho : NontrivialZetaZero) (c tau y a b : ℝ) : ℝ :=
  ‖suzukiXiHorizontalReflectionHeat rho c tau y b‖ +
    ‖suzukiXiHorizontalReflectionHeat rho c tau y a‖ +
      ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho 1 c tau y x

/-- All terms of the actual finite integration-by-parts formula are
integrable through the full carrier divisor. Only reflection-node
avoidance is required of the interval. -/
theorem intervalIntegrable_suzukiXiReflectionMass_terms
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y a b : ℝ)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    IntervalIntegrable (fun x : ℝ => suzukiXiSmoothReflectionSource rho r c tau
      ((x : ℂ) + (y : ℂ) * I)) volume a b ∧
    IntervalIntegrable (deriv (suzukiXiReflectionMassCurrent rho r c tau y)) volume a b ∧
    IntervalIntegrable (suzukiXiReflectionMassVariation rho r c tau y) volume a b ∧
    IntervalIntegrable (suzukiXiReflectionMassRemainder rho r c tau y) volume a b ∧
    IntervalIntegrable (suzukiXiReflectionMassAllowance rho r c tau y) volume a b := by
  have hl : Continuous (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hW : ContinuousOn (fun u : ℝ => suzukiXiReflectionWeight rho ((u : ℂ) + (y : ℂ) * I)) (uIcc a b) := by
    intro u hu
    have hc : ContinuousAt (fun v : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I)) u :=
      (analyticAt_suzukiXiReflectionWeight rho (havoid u hu).1 (havoid u hu).2).continuousAt.comp
        (f := fun v : ℝ => (v : ℂ) + (y : ℂ) * I) (x := u) hl.continuousAt
    exact hc.continuousWithinAt
  have hP : ContinuousOn (suzukiXiHorizontalReflectionHeat rho c tau y) (uIcc a b) := by
    intro u hu
    exact (contDiffAt_suzukiXiHorizontalReflectionHeat rho c tau y u (havoid u hu).1
      (havoid u hu).2).continuousAt.continuousWithinAt
  have hPd : ContinuousOn (deriv (suzukiXiHorizontalReflectionHeat rho c tau y)) (uIcc a b) := by
    intro u hu
    exact ((contDiffAt_suzukiXiHorizontalReflectionHeat rho c tau y u (havoid u hu).1
      (havoid u hu).2).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hJd : ContinuousOn (deriv (suzukiXiReflectionMassCurrent rho r c tau y)) (uIcc a b) := by
    intro u hu
    exact ((contDiffAt_suzukiXiReflectionMassCurrent rho hr c tau y u (havoid u hu).1
      (havoid u hu).2).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hU := Complex.continuous_ofReal.comp (contDiff_suzukiXiHorizontalMass hr y).continuous
  have hUd := Complex.continuous_ofReal.comp
    ((contDiff_suzukiXiHorizontalMass hr y).continuous_deriv (by simp))
  have hS := (contDiff_suzukiXiHorizontalCarrier hr y).continuous
  have hH : Continuous (fun u : ℝ => suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau
      (I * ((u : ℂ) + (y : ℂ) * I))) :=
    (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau).comp (continuous_const.mul hl)
  have hG : ContinuousOn (fun x : ℝ => suzukiXiSmoothReflectionSource rho r c tau
      ((x : ℂ) + (y : ℂ) * I)) (uIcc a b) :=
    hW.mul ((continuous_suzukiXiSmoothBoundaryHeatBulk hr c tau).comp hl).continuousOn
  have hT : ContinuousOn (suzukiXiReflectionMassVariation rho r c tau y) (uIcc a b) :=
    (hP.mul hS.continuousOn).mul hUd.continuousOn
  have hR : ContinuousOn (suzukiXiReflectionMassRemainder rho r c tau y) (uIcc a b) :=
    (((continuousOn_const.mul hPd).mul hU.continuousOn).mul hS.continuousOn).add
      (((continuousOn_const.mul hW).mul hS.continuousOn).mul hH.continuousOn)
  have hC : ContinuousOn (suzukiXiReflectionMassAllowance rho r c tau y) (uIcc a b) :=
    (hPd.norm.div_const r).add ((hW.mul hH.continuousOn).norm.div_const (2*r))
  exact ⟨hG.intervalIntegrable, hJd.intervalIntegrable, hT.intervalIntegrable,
    hR.intervalIntegrable, hC.intervalIntegrable⟩

/-- The finite integral of the complete original density retains every
signed term and has an evaluated current boundary. All integrability
and differentiability hypotheses are discharged for the actual carrier. -/
theorem integral_suzukiXiSmoothReflectionSource_eq_mass_variation
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y a b : ℝ)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    (∫ x : ℝ in a..b, suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I)) =
      2 * I * (r : ℂ)^2 * (suzukiXiReflectionMassCurrent rho r c tau y b -
        suzukiXiReflectionMassCurrent rho r c tau y a) -
      4 * I * (r : ℂ)^2 * (∫ x : ℝ in a..b, suzukiXiReflectionMassVariation rho r c tau y x) -
        ∫ x : ℝ in a..b, suzukiXiReflectionMassRemainder rho r c tau y x := by
  obtain ⟨_hG, hJ, hT, hR, _hC⟩ := intervalIntegrable_suzukiXiReflectionMass_terms rho hr c tau y a b havoid
  have hFTC : (∫ x : ℝ in a..b, deriv (suzukiXiReflectionMassCurrent rho r c tau y) x) =
      suzukiXiReflectionMassCurrent rho r c tau y b - suzukiXiReflectionMassCurrent rho r c tau y a :=
    intervalIntegral.integral_deriv_eq_sub (fun x hx =>
      (contDiffAt_suzukiXiReflectionMassCurrent rho hr c tau y x (havoid x hx).1
        (havoid x hx).2).differentiableAt (by simp)) hJ
  calc
    _ = ∫ x : ℝ in a..b,
        (2 * I * (r : ℂ)^2 * deriv (suzukiXiReflectionMassCurrent rho r c tau y) x -
          4 * I * (r : ℂ)^2 * suzukiXiReflectionMassVariation rho r c tau y x -
            suzukiXiReflectionMassRemainder rho r c tau y x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact suzukiXiSmoothReflectionSource_eq_mass_current_deriv rho hr c tau y x
        (havoid x hx).1 (havoid x hx).2
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hJ.const_mul _).sub (hT.const_mul _)) hR,
        intervalIntegral.integral_sub (hJ.const_mul _) (hT.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC]

/-- An independent finite-interval bound on the full explicit remainder.
Its right-hand side contains only the reflection and Gaussian weights. -/
theorem norm_integral_suzukiXiReflectionMassRemainder_le
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ‖∫ x : ℝ in a..b, suzukiXiReflectionMassRemainder rho r c tau y x‖ ≤
      ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho r c tau y x := by
  have hC := (intervalIntegrable_suzukiXiReflectionMass_terms rho hr c tau y a b havoid).2.2.2.2
  exact intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall (fun x _hx => norm_suzukiXiReflectionMassRemainder_le rho hr c tau y x)) hC

/-- After retaining the signed mass variation, the entire finite
reflection integral has an independent explicit endpoint and weight allowance. -/
theorem norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ‖(∫ x : ℝ in a..b, suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I)) +
      4 * I * (r : ℂ)^2 * (∫ x : ℝ in a..b, suzukiXiReflectionMassVariation rho r c tau y x)‖ ≤
      (‖suzukiXiHorizontalReflectionHeat rho c tau y b‖ +
        ‖suzukiXiHorizontalReflectionHeat rho c tau y a‖) / r +
          ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho r c tau y x := by
  rw [integral_suzukiXiSmoothReflectionSource_eq_mass_variation rho hr c tau y a b havoid]
  rw [show ∀ A B C : ℂ, A - B - C + B = A - C by intros; ring]
  have hJb := norm_suzukiXiReflectionMassCurrent_le rho hr c tau y b
  have hJa := norm_suzukiXiReflectionMassCurrent_le rho hr c tau y a
  have hR := norm_integral_suzukiXiReflectionMassRemainder_le rho hr c tau y hab havoid
  calc
    _ ≤ ‖2 * I * (r : ℂ)^2‖ *
        (‖suzukiXiReflectionMassCurrent rho r c tau y b‖ + ‖suzukiXiReflectionMassCurrent rho r c tau y a‖) +
          ‖∫ x : ℝ in a..b, suzukiXiReflectionMassRemainder rho r c tau y x‖ := by
      apply le_trans (norm_sub_le _ _)
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (norm_sub_le (suzukiXiReflectionMassCurrent rho r c tau y b)
          (suzukiXiReflectionMassCurrent rho r c tau y a))
        (norm_nonneg (2 * I * (r : ℂ)^2))) (le_refl _)
    _ ≤ (2*r^2) *
        (‖suzukiXiHorizontalReflectionHeat rho c tau y b‖ / (2*r^3) +
          ‖suzukiXiHorizontalReflectionHeat rho c tau y a‖ / (2*r^3)) +
            ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho r c tau y x := by
      simp only [norm_mul, norm_pow, norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, norm_ofNat, mul_one]
      gcongr
    _ = _ := by field_simp

/-- The explicit finite budget is nonnegative on every forward interval. -/
theorem suzukiXiReflectionMassBudget_nonneg (rho : NontrivialZetaZero)
    (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ suzukiXiReflectionMassBudget rho c tau y a b := by
  have hi : 0 ≤ ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho 1 c tau y x := by
    apply intervalIntegral.integral_nonneg hab
    intro x _hx
    unfold suzukiXiReflectionMassAllowance
    positivity
  exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) hi

/-- The full error after retaining the signed mass variation has an
explicit inverse-radius bound. Its finite budget is independent of r. -/
theorem norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le_budget
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    ‖(∫ x : ℝ in a..b, suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I)) +
      4 * I * (r : ℂ)^2 * (∫ x : ℝ in a..b, suzukiXiReflectionMassVariation rho r c tau y x)‖ ≤
      suzukiXiReflectionMassBudget rho c tau y a b / r := by
  have he : suzukiXiReflectionMassAllowance rho r c tau y =
      fun x => (1/r) * suzukiXiReflectionMassAllowance rho 1 c tau y x := by
    funext x
    unfold suzukiXiReflectionMassAllowance
    field_simp
  calc
    _ ≤ (‖suzukiXiHorizontalReflectionHeat rho c tau y b‖ +
        ‖suzukiXiHorizontalReflectionHeat rho c tau y a‖) / r +
          ∫ x : ℝ in a..b, suzukiXiReflectionMassAllowance rho r c tau y x :=
      norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le rho hr c tau y hab havoid
    _ = _ := by
      rw [he, intervalIntegral.integral_const_mul]
      unfold suzukiXiReflectionMassBudget
      ring

/-- The corresponding signed upper bound for the actual density. The
real part of the retained complex mass variation is not replaced by its norm. -/
theorem im_integral_suzukiXiSmoothReflectionSource_le_mass_variation
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    (∫ x : ℝ in a..b, suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I)).im ≤
      -4*r^2 * (∫ x : ℝ in a..b, suzukiXiReflectionMassVariation rho r c tau y x).re +
        suzukiXiReflectionMassBudget rho c tau y a b / r := by
  have h := (Complex.im_le_norm _).trans
    (norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le_budget rho hr c tau y hab havoid)
  have hi (A B : ℂ) : (A + 4 * I * (r : ℂ)^2 * B).im = A.im + 4*r^2*B.re := by
    simp only [← Complex.ofReal_pow, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hi] at h
  linarith

/-- On each fixed admissible interval the entire error tends to zero
as smoothing grows. This is not uniform in a shrinking reflection puncture. -/
theorem tendsto_integral_suzukiXiSmoothReflectionSource_add_mass_variation
    (rho : NontrivialZetaZero) (c tau y : ℝ) {a b : ℝ} (hab : a ≤ b)
    (havoid : ∀ x ∈ uIcc a b,
      (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1 ∧
      (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    Tendsto (fun r : ℝ =>
      (∫ x : ℝ in a..b, suzukiXiSmoothReflectionSource rho r c tau ((x : ℂ) + (y : ℂ) * I)) +
        4 * I * (r : ℂ)^2 * (∫ x : ℝ in a..b, suzukiXiReflectionMassVariation rho r c tau y x))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show ∀ᶠ r : ℝ in atTop, _ ≤ suzukiXiReflectionMassBudget rho c tau y a b / r from ?_)
  · exact tendsto_const_nhds.div_atTop tendsto_id
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact norm_integral_suzukiXiSmoothReflectionSource_add_mass_variation_le_budget rho hr c tau y hab havoid

end
end RiemannGaussian
