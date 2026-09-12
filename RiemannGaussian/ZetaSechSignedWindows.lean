/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSechVerticalBound
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Signed logarithmic zeta windows through the divisor

Real analyticity gives genuine local integrability of the logarithmic
singularities on every finite vertical window. The signed detector is
exactly its positive mass minus its negative mass. Its upper bound is
uniform in the window, while the nonnegative negative mass is retained.
For a nonzero vertical scale, the zero ordinates form a null set, so
Mathlib's assigned value of the real logarithm at zero is immaterial.
No full-line integrability of the negative part is assumed or asserted.
-/

namespace RiemannGaussian.ZetaSechSignedWindows
noncomputable section
open MeasureTheory Set Filter DirichletPowerParameters ZetaNearOneLogProfile
open ZetaLogarithmicShiftAllowance SechVerticalKernel

/-- Zeta restricted to any affine vertical line away from the pole's
real coordinate is real analytic, including at zeta zeros. -/
theorem analyticAt_vertical {σ : ℝ} (hσ : σ ≠ 1) (t a u : ℝ) :
    AnalyticAt ℝ (fun v : ℝ => riemannZeta ((σ : ℂ) +
      Complex.I * ((t + a * v : ℝ) : ℂ))) u := by
  have hs : (σ : ℂ) + Complex.I * ((t + a * u : ℝ) : ℂ) ≠ 1 := by
    intro h
    apply hσ
    simpa using congrArg Complex.re h
  have hf : AnalyticAt ℝ (fun v : ℝ => (σ : ℂ) +
      Complex.I * ((t + a * v : ℝ) : ℂ)) u := by
    have hr : AnalyticAt ℝ (fun v : ℝ => t + a * v) u := by fun_prop
    exact analyticAt_const.add (analyticAt_const.mul
      ((Complex.ofRealCLM.analyticAt _).comp hr))
  exact (analyticOn_riemannZeta _ hs).restrictScalars.comp
    (f := fun v : ℝ => (σ : ℂ) + Complex.I * ((t + a * v : ℝ) : ℂ)) hf

/-- On every nonconstant vertical parametrization, the exceptional zero
ordinates form a countable set. This makes their assigned log values harmless. -/
theorem countable_zero_ordinates (σ t : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Set.Countable {u : ℝ | riemannZeta ((σ : ℂ) +
      Complex.I * ((t + a * u : ℝ) : ℂ)) = 0} := by
  have hi : Function.Injective (fun u : ℝ => (σ : ℂ) +
      Complex.I * ((t + a * u : ℝ) : ℂ)) := by
    intro u v h
    have he : t + a * u = t + a * v := by
      simpa using congrArg Complex.im h
    exact mul_left_cancel₀ ha (add_left_cancel he)
  exact ((HereditarilyLindelofSpace.isLindelof riemannZetaZeros).countable_of_isDiscrete
    isDiscrete_riemannZetaZeros).preimage hi

/-- The zeta value is nonzero almost everywhere on a nonconstant
vertical line; zeros need not be avoided by the finite windows. -/
theorem ae_vertical_ne_zero (σ t : ℝ) {a : ℝ} (ha : a ≠ 0) :
    ∀ᵐ u : ℝ, riemannZeta ((σ : ℂ) +
      Complex.I * ((t + a * u : ℝ) : ℂ)) ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using (countable_zero_ordinates σ t ha).measure_zero volume

/-- The signed logarithm on the actual near-one zeta line is locally
integrable even when its window crosses the divisor. -/
theorem intervalIntegrable_log (k : ℕ) (t a l r : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log ‖riemannZeta ((line k : ℂ) +
      Complex.I * ((t + a * u : ℝ) : ℂ))‖) volume l r := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro u _
  exact (analyticAt_vertical (ne_of_lt (line_lt_one k)) t a u).meromorphicAt

/-- The original signed vertical detector, before discarding either sign. -/
def signedIntegrand (k : ℕ) (t a u : ℝ) : ℝ :=
  density u * Real.log ‖riemannZeta ((line k : ℂ) +
    Complex.I * ((t + a * u : ℝ) : ℂ))‖

/-- The negative logarithmic mass, retained as a separate nonnegative carrier. -/
def negativeIntegrand (k : ℕ) (t a u : ℝ) : ℝ :=
  density u * Real.posLog (‖riemannZeta ((line k : ℂ) +
    Complex.I * ((t + a * u : ℝ) : ℂ))‖⁻¹)

/-- The signed density has the literal detector denominator. -/
theorem signedIntegrand_eq (k : ℕ) (t a u : ℝ) : signedIntegrand k t a u =
    Real.log ‖riemannZeta ((line k : ℂ) + Complex.I * ((t + a * u : ℝ) : ℂ))‖ /
      (2 * Real.cosh u ^ 2) := by
  unfold signedIntegrand density
  ring

/-- Exact sign splitting of the actual logarithmic density. -/
theorem signed_eq_positive_sub_negative (k : ℕ) (t a u : ℝ) :
    signedIntegrand k t a u =
      ZetaSechVerticalBound.integrand k t a u - negativeIntegrand k t a u := by
  unfold signedIntegrand ZetaSechVerticalBound.integrand positiveLog negativeIntegrand
  rw [← Real.posLog_sub_posLog_inv, mul_sub]

/-- Negative logarithmic mass is nonnegative at every ordinate. -/
theorem negativeIntegrand_nonneg (k : ℕ) (t a u : ℝ) : 0 ≤ negativeIntegrand k t a u :=
  mul_nonneg (density_nonneg u) Real.posLog_nonneg

/-- Multiplication by the continuous detector density preserves genuine
integrability of the signed logarithm on every finite interval. -/
theorem intervalIntegrable_signed (k : ℕ) (t a l r : ℝ) :
    IntervalIntegrable (signedIntegrand k t a) volume l r :=
  (intervalIntegrable_log k t a l r).continuousOn_mul continuous_density.continuousOn

/-- The retained negative part is genuinely integrable on finite windows. -/
theorem intervalIntegrable_negative (k : ℕ) (t a l r : ℝ) :
    IntervalIntegrable (negativeIntegrand k t a) volume l r := by
  have h := (ZetaSechVerticalBound.continuous_integrand k t a).intervalIntegrable l r |>.sub
    (intervalIntegrable_signed k t a l r)
  convert h using 1
  ext u
  simp only [signed_eq_positive_sub_negative]
  ring

/-- The finite signed detector retains the entire negative logarithmic
mass exactly; neither part is represented by a totalized divergent integral. -/
theorem window_exact (k : ℕ) (t a l r : ℝ) :
    (∫ u in l..r, signedIntegrand k t a u) =
      (∫ u in l..r, ZetaSechVerticalBound.integrand k t a u) -
        ∫ u in l..r, negativeIntegrand k t a u := by
  simp_rw [signed_eq_positive_sub_negative]
  exact intervalIntegral.integral_sub
    ((ZetaSechVerticalBound.continuous_integrand k t a).intervalIntegrable l r)
    (intervalIntegrable_negative k t a l r)

/-- The complete positive allowance bounds the signed window while
retaining its entire negative mass as an explicit improvement. -/
theorem window_bound_with_negative (k : ℕ) (hk : 1 ≤ k) (t a : ℝ)
    {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      2 * profile k t + 2 * shiftCost k t a -
        ∫ u in l..r, negativeIntegrand k t a u := by
  rw [window_exact]
  apply sub_le_sub_right
  have hp : (∫ u in l..r, ZetaSechVerticalBound.integrand k t a u) ≤
      ∫ u : ℝ, ZetaSechVerticalBound.integrand k t a u := by
    rw [intervalIntegral.integral_of_le hlr]
    exact setIntegral_le_integral (ZetaSechVerticalBound.integrable_integrand k hk t a)
      (ae_of_all _ (ZetaSechVerticalBound.integrand_nonneg k t a))
  exact hp.trans (ZetaSechVerticalBound.integral_bound k hk t a)

/-- Every ordered signed window has the same complete-line allowance.
The bound includes all zero singularities and does not depend on its endpoints. -/
theorem window_bound (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤
      2 * profile k t + 2 * shiftCost k t a := by
  have hn := intervalIntegral.integral_nonneg (μ := volume) hlr
    (fun u _ => negativeIntegrand_nonneg k t a u)
  linarith [window_bound_with_negative k hk t a hlr]

/-- The uniform signed-window estimate with the simplified inverse-height
shift allowance. -/
theorem window_bound_simple (k : ℕ) (hk : 1 ≤ k) (t a : ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ u in l..r, signedIntegrand k t a u) ≤ 2 * profile k t + 6 * |a| / height t := by
  apply (window_bound k hk t a hlr).trans
  have h := shiftCost_le k t a
  have he : 6 * |a| / height t = 2 * (3 * |a| / height t) := by ring
  rw [he]
  linarith

/-- Enlarging a symmetric window can only increase its retained negative
mass. No bound on the full negative mass is built into this statement. -/
theorem negative_window_mono (k : ℕ) (t a : ℝ) {R S : ℝ}
    (hR : 0 ≤ R) (hRS : R ≤ S) :
    (∫ u in -R..R, negativeIntegrand k t a u) ≤
      ∫ u in -S..S, negativeIntegrand k t a u := by
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    intervalIntegral.integral_of_le (by linarith : -S ≤ S)]
  exact setIntegral_mono_set (intervalIntegrable_negative k t a (-S) S).1
    (ae_of_all _ (negativeIntegrand_nonneg k t a))
    (Filter.Eventually.of_forall (fun _ hx =>
      Set.Ioc_subset_Ioc (neg_le_neg hRS) hRS hx))

end
end RiemannGaussian.ZetaSechSignedWindows
