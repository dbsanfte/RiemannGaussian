/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionRemainderChart
import RiemannGaussian.ComplexAngularCancellation

/-!
# Signed decay of the complete remainder at a reflection node

The actual xi remainder is compared with its exact angular leading term.
The difference has one simple-pole majorant uniform in smoothing. The
leading harmonic cancels on a centered disk, and dominated convergence
removes the rest, including the companion Gaussian heat term.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

private lemma companion_uniform_bound (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
      ‖I * suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z *
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z)‖ ≤
          C/‖z-zetaSpectralCoordinate rho.1‖ := by
  obtain ⟨q, hq, _hq0, heq⟩ := exists_suzukiXiCarrier_uniform_mass_chart rho
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  let t := fun z : ℂ => (z-a)/(z-b)-1
  let p := fun z : ℂ => -I*(t z)^2*q z*
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z)
  have hab : a ≠ b := by
    intro he
    have hi := congrArg Complex.im he
    change a.im = -a.im at hi
    exact him (by linarith)
  have ht : ContinuousAt t a :=
    (((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hab)).sub continuousAt_const)
  have hp : ContinuousAt p a :=
    (((continuousAt_const.mul (ht.pow 2)).mul hq.continuousAt).mul
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau).continuousAt.comp
        (continuousAt_const.mul continuousAt_id)))
  have hbp : ∀ᶠ z in 𝓝 a, ‖p z‖ ≤ ‖p a‖+1 :=
    hp.norm.eventually (eventually_le_nhds (by linarith))
  refine ⟨‖p a‖+1, by positivity, ?_⟩
  filter_upwards [hbp.filter_mono nhdsWithin_le_nhds,
    heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    (continuousAt_id.eventually_ne hab).filter_mono nhdsWithin_le_nhds] with z hpz hqz hza hzb r
  let D : ℝ := 1+r^2*normSq ((z-a)*q z)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [normSq_nonneg ((z-a)*q z), sq_nonneg r]
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have he : I * suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z *
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z) = p z/((z-a)*(D:ℂ)) := by
    rw [(hqz r).1]
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    have hwa := sub_ne_zero.mpr hza
    have hwb := sub_ne_zero.mpr hzb
    dsimp only [p, t, D, a, b] at hwa hwb ⊢
    field_simp
    ring
  have hw : 0 < ‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  rw [he, norm_div, norm_mul (z-a) (D : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
  apply (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (le_mul_of_one_le_right (norm_nonneg (z-a)) hD)).trans
  exact div_le_div_of_nonneg_right hpz (norm_nonneg _)

/-- At every fixed point the actual complete remainder tends to zero
as smoothing increases. This assertion alone does not exchange an integral
with the limit at a reflection node. -/
theorem tendsto_suzukiXiPlanarReflectionMassRemainder_atTop
    (rho : NontrivialZetaZero) (c tau : ℝ) (z : ℂ) :
    Tendsto (fun r : ℝ => suzukiXiPlanarReflectionMassRemainder rho r c tau z) atTop (𝓝 0) := by
  let A := ‖deriv (suzukiXiHorizontalReflectionHeat rho c tau z.im) z.re‖
  let B := ‖suzukiXiReflectionWeight rho z *
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z)‖
  have hl : Tendsto (fun r : ℝ => (A+B/2)/r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb := norm_suzukiXiReflectionMassRemainder_le rho hr c tau z.im z.re
  simp only [Complex.re_add_im] at hb
  change ‖suzukiXiPlanarReflectionMassRemainder rho r c tau z‖ ≤ _ at hb
  convert hb using 1
  dsimp [A, B]
  ring

/-- The complete actual remainder, after subtracting its exact frozen
angular term, has an integrable simple-pole majorant independent of the
smoothing radius. No xi-dependent denominator has been discarded. -/
theorem exists_suzukiXiReflectionMassRemainder_angular_error_bound
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
      ‖suzukiXiPlanarReflectionMassRemainder rho r c tau z -
        (4*I*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
          (analyticZetaZeroMultiplicity rho : ℂ)^3) *
            complexAngularResolventKernel r (1/(analyticZetaZeroMultiplicity rho : ℝ)^2)
              (z-zetaSpectralCoordinate rho.1)‖ ≤ C/‖z-zetaSpectralCoordinate rho.1‖ := by
  obtain ⟨N, Q, hN, hQ, hN0, hQ0, he⟩ :=
    exists_suzukiXiReflectionMassRemainder_angular_chart rho c tau him
  have hQa : 0 < Q (zetaSpectralCoordinate rho.1) := by
    rw [hQ0]
    have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive rho
    positivity
  obtain ⟨C, hC, herror⟩ := exists_complexAngularResolventKernel_local_error_bound
    (hN.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    (hQ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) hQa
  obtain ⟨D, hD, hcomp⟩ := companion_uniform_bound rho c tau him
  refine ⟨C+D, add_nonneg hC hD, ?_⟩
  filter_upwards [he, herror, hcomp] with z hz hEz hDz r
  rw [hz r, ← hN0, ← hQ0]
  rw [add_sub_right_comm]
  exact (norm_add_le _ _).trans ((add_le_add (hEz r) (hDz r)).trans_eq (by ring))

/-- On every sufficiently small centered disk the entire actual complex
remainder has vanishing integral as smoothing grows. The disk contains
the selected reflection node; no puncture or principal value is used. -/
theorem exists_tendsto_integral_suzukiXiReflectionMassRemainder_node
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ε ≤ R →
      Tendsto (fun r : ℝ => ∫ z in Metric.closedBall (zetaSpectralCoordinate rho.1) ε,
        suzukiXiPlanarReflectionMassRemainder rho r c tau z) atTop (𝓝 0) := by
  obtain ⟨C, _hC, he⟩ := exists_suzukiXiReflectionMassRemainder_angular_error_bound rho c tau him
  have he' := eventually_nhdsWithin_iff.mp he
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he'
  refine ⟨R, hR, fun ε _hε hεR => ?_⟩
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  apply tendsto_integral_disk_of_angular_error (C := C)
    (q := 1/(analyticZetaZeroMultiplicity rho : ℝ)^2)
    (v := 4*I*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
      (analyticZetaZeroMultiplicity rho : ℂ)^3) (by positivity)
  · intro r hr
    exact (locallyIntegrable_suzukiXiPlanarReflectionMassRemainder rho hr c tau).integrableOn_isCompact
      (isCompact_closedBall _ ε)
  · intro z hz hza r _hr
    exact hball (Metric.closedBall_subset_closedBall hεR hz) hza r
  · intro z _hz _hza
    exact tendsto_suzukiXiPlanarReflectionMassRemainder_atTop rho c tau z

/-- Exchanging the reflection nodes preserves the entire existing
remainder, including the horizontal derivative and companion heat. -/
theorem suzukiXiPlanarReflectionMassRemainder_conjugatePartner
    (rho : NontrivialZetaZero) (r c tau : ℝ) :
    suzukiXiPlanarReflectionMassRemainder rho.conjugatePartner r c tau =
      suzukiXiPlanarReflectionMassRemainder rho r c tau := by
  have hP : suzukiXiHorizontalReflectionHeat rho.conjugatePartner c tau =
      suzukiXiHorizontalReflectionHeat rho c tau := by
    funext y x
    simp only [suzukiXiHorizontalReflectionHeat, suzukiXiReflectionWeight_conjugatePartner]
  funext z
  simp only [suzukiXiPlanarReflectionMassRemainder, suzukiXiReflectionMassRemainder,
    hP, suzukiXiReflectionWeight_conjugatePartner]

/-- For a hypothetical right-half zero the remainder also vanishes on
small full disks around its upper reflected node, where the positive
source is located. No simplicity assumption is made. -/
theorem exists_tendsto_integral_suzukiXiReflectionMassRemainder_reflected_node
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ε ≤ R →
      Tendsto (fun r : ℝ => ∫ z in Metric.closedBall
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) ε,
          suzukiXiPlanarReflectionMassRemainder rho r c tau z) atTop (𝓝 0) := by
  have him : (zetaSpectralCoordinate rho.conjugatePartner.1).im ≠ 0 := by
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, zetaSpectralCoordinate_im]
    linarith
  simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    suzukiXiPlanarReflectionMassRemainder_conjugatePartner] using
      exists_tendsto_integral_suzukiXiReflectionMassRemainder_node rho.conjugatePartner c tau him

end
end RiemannGaussian
