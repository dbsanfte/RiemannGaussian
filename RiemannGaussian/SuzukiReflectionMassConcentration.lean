/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionRemainderCompact

/-!
# The full reflected source persists in the signed mass variation

On a fixed eligible upper rectangle the actual source converges to its
original reflected-node value as smoothing grows. The independently
vanishing complete error then identifies the limit of the signed mass
variation itself. It has positive imaginary part under the hypothetical
right-half zero, so smoothing alone supplies no source deficit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace RiemannGaussian
noncomputable section

/-- The actual complete source on a fixed rectangle tends to its
reflected-node mass when smoothing grows. This uses the independent
Gaussian boundary estimate and ordinary through-node integrability. -/
theorem tendsto_suzukiXiSmoothReflectionSource_smoothing_area
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) {tau R : ℝ}
    (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ)
    (hc : 2*|c| ≤ R) (hRe : 2*|(zetaSpectralCoordinate rho.1).re| ≤ R) :
    Tendsto (fun r : ℝ => ∫ z in [[-R,R]] ×ℂ [[0,R]],
      suzukiXiSmoothReflectionSource rho r c tau z) atTop
      (𝓝 ((2*Real.pi*I)*((analyticZetaZeroMultiplicity rho : ℂ)⁻¹*
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let L := (2*Real.pi*I)*((analyticZetaZeroMultiplicity rho : ℂ)⁻¹*
    suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)))
  have hbound : Tendsto (fun r : ℝ => rectangularBoundaryIntegral (-R) R 0 R
      (suzukiXiSmoothReflectionField rho r c tau)) atTop (𝓝 0) := by
    have hl : Tendsto (fun r : ℝ =>
        (384*(zetaSpectralCoordinate rho.1).im^2*R^2*Real.exp (-tau*R^2/4))/r)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    convert norm_suzukiXiSmoothReflectionField_boundary_le rho hr htau hR c hc hRe using 1
    ring
  have ht := hbound.add_const L
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have he := rectangularAreaIntegral_suzukiXiSmoothReflectionSource_eq_boundary_add_mass
    rho hzero hr c tau (-R) R 0 R le_rfl
    (by rw [conj_re]; nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_re]; nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_im, zetaSpectralCoordinate_im]; linarith)
    (by rw [conj_im]; linarith [neg_le_abs (zetaSpectralCoordinate rho.1).im])
  rw [rectangularAreaIntegral_eq_setIntegral (by linarith) hR0.le _
    ((locallyIntegrable_suzukiXiSmoothReflectionSource rho hr c tau).integrableOn_isCompact
      (isCompact_uIcc.reProdIm isCompact_uIcc))] at he
  exact he.symm

/-- The original reflected source is the limit of the retained signed
mass variation itself on every fixed eligible rectangle. Neither a
vanishing remainder nor increasing smoothing reduces this mass. -/
theorem tendsto_suzukiXiReflectionMassVariation_smoothing_area
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) {tau R : ℝ}
    (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ)
    (hc : 2*|c| ≤ R) (hRe : 2*|(zetaSpectralCoordinate rho.1).re| ≤ R) :
    Tendsto (fun r : ℝ => -4*I*(r:ℂ)^2*
      (∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiPlanarReflectionMassVariation rho r c tau z)) atTop
      (𝓝 ((2*Real.pi*I)*((analyticZetaZeroMultiplicity rho : ℂ)⁻¹*
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  have hs := tendsto_suzukiXiSmoothReflectionSource_smoothing_area rho hzero htau hR c hc hRe
  have he := tendsto_suzukiXiReflectionSource_add_mass_rectangle rho hzero htau.le
    (lt_of_lt_of_le zero_lt_one hR) c hRe (by
      rw [conj_im]
      have h := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      linarith [neg_le_abs (zetaSpectralCoordinate rho.1).im])
  have h := hs.sub he
  simp only [sub_zero] at h
  convert h using 1
  funext r
  ring

/-- Under a hypothetical right-half zero, the retained signed area is
eventually larger than half of the full positive source in imaginary
part. This is a lower bound diagnosing concentration, not an RH ceiling. -/
theorem eventually_suzukiXiReflectionMassVariation_im_gt_half_source
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) {tau R : ℝ}
    (htau : 0 < tau) (hR : 1 ≤ R) (c : ℝ)
    (hc : 2*|c| ≤ R) (hRe : 2*|(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ∀ᶠ r : ℝ in atTop,
      (((2*Real.pi*I)*((analyticZetaZeroMultiplicity rho : ℂ)⁻¹*
        suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)))).im)/2 <
          (-4*I*(r:ℂ)^2*(∫ z in [[-R,R]] ×ℂ [[0,R]],
            suzukiXiPlanarReflectionMassVariation rho r c tau z)).im := by
  have ht := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_suzukiXiReflectionMassVariation_smoothing_area rho hzero htau hR c hc hRe)
  have hp := suzukiXiSmoothReflectionSource_mass_im_pos rho hzero c tau
  exact ht.eventually (eventually_gt_nhds (by linarith))

end
end RiemannGaussian
