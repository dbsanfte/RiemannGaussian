/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionLocalIntegrability

/-!
# Finite signed mass identities through the reflection divisor

Every term of the mass-current identity is locally integrable in the
plane. The identity therefore passes to ordinary integrals on compact
sets, including both selected nodes. No pointwise division at a node,
principal value, or exchange of smoothing and puncture limits is used.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff Interval
namespace RiemannGaussian
noncomputable section

/-- The existing signed horizontal variation, viewed on the plane. -/
def suzukiXiPlanarReflectionMassVariation (rho : NontrivialZetaZero)
    (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionMassVariation rho r c tau z.im z.re

/-- The complete existing remainder, including its companion heat term. -/
def suzukiXiPlanarReflectionMassRemainder (rho : NontrivialZetaZero)
    (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionMassRemainder rho r c tau z.im z.re

private lemma horizontal_deriv_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℂ → F} (hf : Differentiable ℝ f) (y x : ℝ) :
    deriv (fun u : ℝ => f ((u : ℂ) + (y : ℂ) * I)) x =
      fderiv ℝ f ((x : ℂ) + (y : ℂ) * I) 1 := by
  have hl : HasDerivAt (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) 1 x :=
    Complex.ofRealCLM.hasDerivAt.add_const _
  exact ((hf _).hasFDerivAt.comp_hasDerivAt x hl).deriv

/-- The horizontal current is smooth on every full line, even when the
line goes through a selected reflection node. -/
theorem contDiff_suzukiXiReflectionMassCurrent
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y : ℝ) :
    ContDiff ℝ ∞ (suzukiXiReflectionMassCurrent rho r c tau y) :=
  (contDiff_suzukiXiPlanarReflectionMassCurrent rho hr c tau).comp
    (Complex.ofRealCLM.contDiff.add contDiff_const)

/-- The actual one-dimensional derivative is the horizontal partial
derivative of the globally smooth planar current, including at both nodes. -/
theorem deriv_suzukiXiReflectionMassCurrent_eq_fderiv
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau y x : ℝ) :
    deriv (suzukiXiReflectionMassCurrent rho r c tau y) x =
      fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau)
        ((x : ℂ) + (y : ℂ) * I) 1 :=
  horizontal_deriv_eq_fderiv
    ((contDiff_suzukiXiPlanarReflectionMassCurrent rho hr c tau).differentiable (by simp)) y x

private lemma mass_deriv_eq_fderiv {r : ℝ} (hr : 0 < r) (z : ℂ) :
    deriv (suzukiXiHorizontalMass r z.im) z.re = fderiv ℝ (suzukiXiNormalizedMass r) z 1 := by
  simpa only [suzukiXiHorizontalMass, Complex.re_add_im] using! horizontal_deriv_eq_fderiv
    ((contDiff_suzukiXiNormalizedMass hr).differentiable (by simp)) z.im z.re

private lemma current_deriv_continuous (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    Continuous (fun z => fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1) :=
  ((contDiff_suzukiXiPlanarReflectionMassCurrent rho hr c tau).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The signed mass variation is locally integrable through the complete
reflection divisor. Its full complex value is retained. -/
theorem locallyIntegrable_suzukiXiPlanarReflectionMassVariation
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    LocallyIntegrable (suzukiXiPlanarReflectionMassVariation rho r c tau) volume := by
  have hc : Continuous (fun z => (fderiv ℝ (suzukiXiNormalizedMass r) z 1 : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((contDiff_suzukiXiNormalizedMass hr).continuous_fderiv (by simp)).clm_apply continuous_const)
  have he : suzukiXiPlanarReflectionMassVariation rho r c tau = fun z =>
      suzukiXiSmoothReflectionField rho r c tau z *
        (fderiv ℝ (suzukiXiNormalizedMass r) z 1 : ℂ) := by
    funext z
    rw [suzukiXiPlanarReflectionMassVariation, suzukiXiReflectionMassVariation,
      mass_deriv_eq_fderiv hr]
    simp only [suzukiXiHorizontalReflectionHeat, suzukiXiHorizontalCarrier,
      Complex.re_add_im, suzukiXiSmoothReflectionField]
    ring
  rw [he]
  exact LocallyIntegrable.mul_continuous hc (locallyIntegrable_suzukiXiSmoothReflectionField rho hr c tau)

/-- The exact signed identity holds almost everywhere on the entire
plane. Only the two selected points are removed in this statement. -/
theorem suzukiXiSmoothReflectionSource_ae_eq_mass_deriv
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    suzukiXiSmoothReflectionSource rho r c tau =ᵐ[volume] fun z =>
      2 * I * (r : ℂ) ^ 2 * fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1 -
        4 * I * (r : ℂ) ^ 2 * suzukiXiPlanarReflectionMassVariation rho r c tau z -
          suzukiXiPlanarReflectionMassRemainder rho r c tau z := by
  filter_upwards [volume.ae_ne (zetaSpectralCoordinate rho.1),
    volume.ae_ne (starRingEnd ℂ (zetaSpectralCoordinate rho.1))] with z ha hb
  have h := suzukiXiSmoothReflectionSource_eq_mass_current_deriv rho hr c tau z.im z.re
    (by simpa only [Complex.re_add_im] using ha) (by simpa only [Complex.re_add_im] using hb)
  rw [deriv_suzukiXiReflectionMassCurrent_eq_fderiv rho hr c tau] at h
  simpa only [Complex.re_add_im, suzukiXiPlanarReflectionMassVariation,
    suzukiXiPlanarReflectionMassRemainder] using! h

/-- Both explicit remainder terms together are locally integrable in
the plane. This uses their exact identity and does not integrate the
nonintegrable weight-only envelope near a reflection node. -/
theorem locallyIntegrable_suzukiXiPlanarReflectionMassRemainder
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    LocallyIntegrable (suzukiXiPlanarReflectionMassRemainder rho r c tau) volume := by
  have hD : LocallyIntegrable (fun z => 2 * I * (r : ℂ)^2 *
      fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1) volume :=
    (continuous_const.mul (current_deriv_continuous rho hr c tau)).locallyIntegrable
  have hM := LocallyIntegrable.continuous_mul (continuous_const : Continuous (fun _ : ℂ =>
    4 * I * (r : ℂ)^2)) (locallyIntegrable_suzukiXiPlanarReflectionMassVariation rho hr c tau)
  have hG := locallyIntegrable_suzukiXiSmoothReflectionSource rho hr c tau
  apply ((hD.sub hM).sub hG).congr
  filter_upwards [suzukiXiSmoothReflectionSource_ae_eq_mass_deriv rho hr c tau] with z hz
  change 2 * I * (r : ℂ)^2 * fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1 -
    4 * I * (r : ℂ)^2 * suzukiXiPlanarReflectionMassVariation rho r c tau z -
      suzukiXiSmoothReflectionSource rho r c tau z = _
  rw [hz]
  ring

/-- The full ordinary area integral splits into its three signed terms
on every compact planar set, with all integrability obligations proved. -/
theorem integral_suzukiXiSmoothReflectionSource_eq_mass_area
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ)
    {K : Set ℂ} (hK : IsCompact K) :
    (∫ z in K, suzukiXiSmoothReflectionSource rho r c tau z) =
      2 * I * (r : ℂ)^2 * (∫ z in K,
        fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1) -
      4 * I * (r : ℂ)^2 * (∫ z in K, suzukiXiPlanarReflectionMassVariation rho r c tau z) -
        ∫ z in K, suzukiXiPlanarReflectionMassRemainder rho r c tau z := by
  have hD : IntegrableOn (fun z =>
      fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1) K volume :=
    (current_deriv_continuous rho hr c tau).continuousOn.integrableOn_compact hK
  have hM := (locallyIntegrable_suzukiXiPlanarReflectionMassVariation rho hr c tau).integrableOn_isCompact hK
  have hR := (locallyIntegrable_suzukiXiPlanarReflectionMassRemainder rho hr c tau).integrableOn_isCompact hK
  have hs := integral_sub ((hD.const_mul (2 * I * (r : ℂ)^2)).sub
    (hM.const_mul (4 * I * (r : ℂ)^2))) hR
  simp only [Pi.sub_apply] at hs
  rw [integral_congr_ae (ae_restrict_of_ae
    (suzukiXiSmoothReflectionSource_ae_eq_mass_deriv rho hr c tau)),
    hs,
    integral_sub (hD.const_mul _) (hM.const_mul _), integral_const_mul, integral_const_mul]

private lemma integral_current_partial_rectangle
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau l v b u : ℝ)
    (hlv : l ≤ v) (hbu : b ≤ u) :
    (∫ z in [[l,v]] ×ℂ [[b,u]],
      fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1) =
      ∫ y : ℝ in b..u, suzukiXiReflectionMassCurrent rho r c tau y v -
        suzukiXiReflectionMassCurrent rho r c tau y l := by
  let D := fun z => fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau) z 1
  have hD : Continuous D := current_deriv_continuous rho hr c tau
  have hK : IsCompact ([[l,v]] ×ℂ [[b,u]]) := isCompact_uIcc.reProdIm isCompact_uIcc
  rw [← rectangularAreaIntegral_eq_setIntegral hlv hbu D
    (hD.continuousOn.integrableOn_compact hK)]
  have hjoint : Continuous (fun p : ℝ × ℝ => D ((p.1 : ℂ) + (p.2 : ℂ) * I)) :=
    hD.comp ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hi : IntegrableOn (fun p : ℝ × ℝ => D ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (uIoc l v ×ˢ uIoc b u) volume :=
    (hjoint.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  unfold rectangularAreaIntegral
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun x y : ℝ => D ((x : ℂ) + (y : ℂ) * I)) hi]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only
  have he : (fun x : ℝ => D ((x : ℂ) + (y : ℂ) * I)) =
      deriv (suzukiXiReflectionMassCurrent rho r c tau y) := by
    funext x
    exact (deriv_suzukiXiReflectionMassCurrent_eq_fderiv rho hr c tau y x).symm
  rw [he]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _hx => (contDiff_suzukiXiReflectionMassCurrent rho hr c tau y).differentiable (by simp) x)
    (((contDiff_suzukiXiReflectionMassCurrent rho hr c tau y).continuous_deriv (by simp)).intervalIntegrable l v)

/-- On every finite rectangle, including those containing both nodes,
the ordinary full-source integral has exactly two current edges, the
signed mass variation, and the complete remainder. Fubini and the
fundamental theorem are justified for the actual fields. -/
theorem integral_suzukiXiSmoothReflectionSource_eq_mass_rectangle
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau l v b u : ℝ)
    (hlv : l ≤ v) (hbu : b ≤ u) :
    (∫ z in [[l,v]] ×ℂ [[b,u]], suzukiXiSmoothReflectionSource rho r c tau z) =
      2 * I * (r : ℂ)^2 * (∫ y : ℝ in b..u,
        suzukiXiReflectionMassCurrent rho r c tau y v - suzukiXiReflectionMassCurrent rho r c tau y l) -
      4 * I * (r : ℂ)^2 *
        (∫ z in [[l,v]] ×ℂ [[b,u]], suzukiXiPlanarReflectionMassVariation rho r c tau z) -
          ∫ z in [[l,v]] ×ℂ [[b,u]], suzukiXiPlanarReflectionMassRemainder rho r c tau z := by
  rw [integral_suzukiXiSmoothReflectionSource_eq_mass_area rho hr c tau
    (isCompact_uIcc.reProdIm isCompact_uIcc),
    integral_current_partial_rectangle rho hr c tau l v b u hlv hbu]

end
end RiemannGaussian
