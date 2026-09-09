/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmoothReflection
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSimplePoleExcision

/-!
# Excision for the actual smooth Gaussian reflection field

The original reflection weight and both signed Gaussian area terms are
kept together. Genuine carrier poles of every order need no punctures:
the actual carrier is smooth there. The reflected xi test node still
contributes its exact negative inverse-multiplicity source. Four
rectangles around that node give a genuine improper area identity,
without an interchange with the singular zero-smoothing limit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff Interval
namespace RiemannGaussian
noncomputable section

/-- The actual full reflection field with the moving Gaussian. -/
def suzukiXiSmoothReflectionField (rho : NontrivialZetaZero) (r x tau : ℝ) (z : ℂ) : ℂ :=
  (suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z) *
    suzukiSmoothSpectralBoundaryHeat x tau z

/-- The complete signed reflection-weighted area density. -/
def suzukiXiSmoothReflectionSource (rho : NontrivialZetaZero) (r x tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z * suzukiXiSmoothBoundaryHeatBulk r x tau z

private def reflectionDomain (rho : NontrivialZetaZero) : Set ℂ :=
  {z | z ≠ zetaSpectralCoordinate rho.1 ∧ z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)}

private lemma field_differentiable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau : ℝ) {z : ℂ} (hz : z ∈ reflectionDomain rho) :
    DifferentiableAt ℝ (suzukiXiSmoothReflectionField rho r x tau) z :=
  (((analyticAt_suzukiXiReflectionWeight rho hz.1 hz.2).differentiableAt.restrictScalars ℝ).mul
    ((contDiff_suzukiXiSmoothCarrier hr).differentiable (by simp) z)).mul
      (differentiable_suzukiSmoothSpectralBoundaryHeat x tau z)

private lemma field_continuous (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) :
    ContinuousOn (suzukiXiSmoothReflectionField rho r x tau) (reflectionDomain rho) :=
  fun _ hz => (field_differentiable rho hr x tau hz).continuousAt.continuousWithinAt

private lemma source_continuous (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) :
    ContinuousOn (suzukiXiSmoothReflectionSource rho r x tau) (reflectionDomain rho) :=
  fun _ hz => ((analyticAt_suzukiXiReflectionWeight rho hz.1 hz.2).continuousAt.mul
    (continuous_suzukiXiSmoothBoundaryHeatBulk hr x tau).continuousAt).continuousWithinAt

private lemma source_eq (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau : ℝ) {z : ℂ} (hz : z ∈ reflectionDomain rho) :
    complexCauchyGreenSource (suzukiXiSmoothReflectionField rho r x tau) z =
      suzukiXiSmoothReflectionSource rho r x tau z :=
  complexCauchyGreenSource_suzukiXiSmoothCarrier_reflection_heat rho hr x tau hz.1 hz.2

private lemma rectangle_integrable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau l v b u : ℝ) (hdomain : [[l,v]] ×ℂ [[b,u]] ⊆ reflectionDomain rho) :
    rectangularBoundaryIntegrable l v b u (suzukiXiSmoothReflectionField rho r x tau) :=
  rectangularBoundaryIntegrable_of_continuousOn_reProdIm ((field_continuous rho hr x tau).mono hdomain)

/-- On every rectangle avoiding only the two reflection nodes, the
full actual field has its complete signed area identity. Original
carrier poles and other xi zeros are allowed everywhere in the rectangle. -/
theorem suzukiXiSmoothReflectionField_rectangularCauchyGreen
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau l v b u : ℝ)
    (hdomain : ∀ z ∈ [[l,v]] ×ℂ [[b,u]],
      z ≠ zetaSpectralCoordinate rho.1 ∧ z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    rectangularBoundaryIntegral l v b u (suzukiXiSmoothReflectionField rho r x tau) =
      rectangularAreaIntegral l v b u (suzukiXiSmoothReflectionSource rho r x tau) := by
  let K : Set ℂ := [[l,v]] ×ℂ [[b,u]]
  let F := suzukiXiSmoothReflectionField rho r x tau
  let G := suzukiXiSmoothReflectionSource rho r x tau
  have hk : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hd : DifferentiableOn ℝ F K :=
    fun _ hz => (field_differentiable rho hr x tau (hdomain _ hz)).differentiableWithinAt
  have hG : IntegrableOn G K :=
    ((source_continuous rho hr x tau).mono hdomain).integrableOn_compact hk
  have hi : IntegrableOn (fun z => complexCauchyGreenSource F z) K :=
    hG.congr_fun (fun _ hz => (source_eq rho hr x tau (hdomain _ hz)).symm) hk.measurableSet
  have hbnd := Complex.integral_boundary_rect_of_differentiableOn_real F
    ((l : ℂ) + (b : ℂ) * I) ((v : ℂ) + (u : ℂ) * I)
    (by simpa [K] using hd) (by simpa [K, complexCauchyGreenSource, smul_eq_mul] using hi)
  calc
    _ = rectangularAreaIntegral l v b u (complexCauchyGreenSource F) := by
      simpa [rectangularBoundaryIntegral, rectangularAreaIntegral, complexCauchyGreenSource] using hbnd
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro y hy
      exact source_eq rho hr x tau (hdomain _ ⟨by simpa using ha, by simpa using hy⟩)

private lemma horizontal_integrable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau l v y : ℝ) (ha : y ≠ (zetaSpectralCoordinate rho.1).im)
    (hb : y ≠ (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im) :
    IntervalIntegrable (fun t : ℝ => suzukiXiSmoothReflectionField rho r x tau
      ((t : ℂ) + (y : ℂ) * I)) volume l v := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (field_differentiable rho hr x tau ?_).continuousAt.comp
    (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) t)
  constructor
  · intro he
    exact ha (by simpa using congrArg Complex.im he)
  · intro he
    exact hb (by simpa using congrArg Complex.im he)

private lemma vertical_integrable (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (x tau b u v : ℝ) (hv : v ≠ (zetaSpectralCoordinate rho.1).re) :
    IntervalIntegrable (fun y : ℝ => suzukiXiSmoothReflectionField rho r x tau
      ((v : ℂ) + (y : ℂ) * I)) volume b u := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (field_differentiable rho hr x tau ?_).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) y)
  constructor <;> intro he <;> exact hv (by simpa using congrArg Complex.re he)

private lemma alpha_im_neg (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) :
    (zetaSpectralCoordinate rho.1).im < 0 := by
  rw [zetaSpectralCoordinate_im]
  linarith

/-- For every hypothetical right-half zero, the actual shrinking-square
boundary has the complete moving Gaussian source `-2*pi*i*B(beta)/m`.
All side integrability conditions are discharged for the smooth carrier. -/
theorem tendsto_square_suzukiXiSmoothReflectionField (rho : NontrivialZetaZero)
    (hzero : 1 / 2 < rho.1.re) {r : ℝ} (hr : 0 < r) (x tau : ℝ) :
    Tendsto (fun q : ℝ => rectangularBoundaryIntegral
      ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re - q)
      ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re + q)
      ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im - q)
      ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im + q)
      (suzukiXiSmoothReflectionField rho r x tau)) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * I) * (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  have ha := alpha_im_neg rho hzero
  apply tendsto_rectangularBoundaryIntegral_centeredSquare_nhdsGT_zero_of_tendsto_sub_mul _
    (tendsto_sub_mul_suzukiXiSmoothCarrier_reflection_heat rho hr x tau ha.ne)
  have hb : 0 < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im := by simpa using neg_pos.mpr ha
  filter_upwards [Ioo_mem_nhdsGT hb] with q hq
  refine ⟨horizontal_integrable rho hr x tau _ _ _ ?_ ?_,
    horizontal_integrable rho hr x tau _ _ _ ?_ ?_,
    vertical_integrable rho hr x tau _ _ _ ?_, vertical_integrable rho hr x tau _ _ _ ?_⟩ <;>
    simp only [conj_re, conj_im] at * <;> linarith [hq.1, hq.2]

private lemma upper_rectangle_domain (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re)
    {l v b u : ℝ} (hb : 0 ≤ b) (hbu : b ≤ u) :
    (([[l,v]] ×ℂ [[b,u]]) \ {starRingEnd ℂ (zetaSpectralCoordinate rho.1)}) ⊆ reflectionDomain rho := by
  intro z hz
  refine ⟨?_, hz.2⟩
  intro he
  have him : b ≤ z.im := by
    have hh := hz.1.2
    rw [uIcc_of_le hbu] at hh
    exact hh.1
  rw [he] at him
  linarith [alpha_im_neg rho hzero]

/-- Exact fixed-square excision for the full original reflection field.
The four area pieces retain both signed Gaussian terms and all original
carrier poles. Only the reflected test node is punctured. -/
theorem suzukiXiSmoothReflectionField_onePunctureSquareCauchyGreen
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r : ℝ} (hr : 0 < r)
    (x tau l v b u q : ℝ) (hb0 : 0 ≤ b) (hq : 0 < q)
    (hl : l < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re - q)
    (hv : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re + q < v)
    (hb : b < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im - q)
    (hu : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im + q < u) :
    rectangularBoundaryIntegral l v b u (suzukiXiSmoothReflectionField rho r x tau) =
      rectangularAreaIntegralOutsideCenteredSquare l v b u
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) q (suzukiXiSmoothReflectionSource rho r x tau) +
      rectangularBoundaryIntegral
        ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re - q)
        ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re + q)
        ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im - q)
        ((starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im + q)
        (suzukiXiSmoothReflectionField rho r x tau) := by
  let c := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  let F := suzukiXiSmoothReflectionField rho r x tau
  let G := suzukiXiSmoothReflectionSource rho r x tau
  have hdomain := upper_rectangle_domain rho hzero (l := l) (v := v) hb0 (show b ≤ u by linarith)
  obtain ⟨hLD, hBD, hTD, hRD⟩ :=
    fourRectanglesOutsideCenteredSquare_subset_of_rectangle_diff_singleton_subset
      l v b u c q hq hl hv hb hu hdomain
  have hLI := rectangle_integrable rho hr x tau _ _ _ _ hLD
  have hBI := rectangle_integrable rho hr x tau _ _ _ _ hBD
  have hTI := rectangle_integrable rho hr x tau _ _ _ _ hTD
  have hRI := rectangle_integrable rho hr x tau _ _ _ _ hRD
  have hSI : rectangularBoundaryIntegrable (c.re-q) (c.re+q) (c.im-q) (c.im+q) F :=
    ⟨hBI.2.1, hTI.1, hRI.2.2.2.mono_set (by
      intro y hy
      rw [uIcc_of_le (by linarith : c.im-q ≤ c.im+q)] at hy
      rw [uIcc_of_le (by linarith : b ≤ u)]
      exact ⟨hb.le.trans hy.1, hy.2.trans hu.le⟩), hLI.2.2.1.mono_set (by
      intro y hy
      rw [uIcc_of_le (by linarith : c.im-q ≤ c.im+q)] at hy
      rw [uIcc_of_le (by linarith : b ≤ u)]
      exact ⟨hb.le.trans hy.1, hy.2.trans hu.le⟩)⟩
  have hd := rectangularBoundaryIntegral_eq_fourPieces_add_centeredSquare
    l v b u c q F hLI hBI hSI hTI hRI
  have hL := suzukiXiSmoothReflectionField_rectangularCauchyGreen rho hr x tau _ _ _ _ hLD
  have hB := suzukiXiSmoothReflectionField_rectangularCauchyGreen rho hr x tau _ _ _ _ hBD
  have hT := suzukiXiSmoothReflectionField_rectangularCauchyGreen rho hr x tau _ _ _ _ hTD
  have hR := suzukiXiSmoothReflectionField_rectangularCauchyGreen rho hr x tau _ _ _ _ hRD
  change rectangularBoundaryIntegral l v b u F = _
  rw [hd, hL, hB, hT, hR]
  unfold rectangularAreaIntegralOutsideCenteredSquare
  ring

/-- The actual reflection-weighted improper area limit is the outer
boundary plus its exact positive-sign source correction. This is a
proved limit of four genuine rectangle integrals, with no area integral
through a singular point or zero-smoothing exchange assumed. -/
theorem tendsto_area_suzukiXiSmoothReflectionSource
    (rho : NontrivialZetaZero) (hzero : 1 / 2 < rho.1.re) {r : ℝ} (hr : 0 < r)
    (x tau l v b u : ℝ) (hb0 : 0 ≤ b)
    (hl : l < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re)
    (hv : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re < v)
    (hb : b < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im)
    (hu : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im < u) :
    Tendsto (fun q : ℝ => rectangularAreaIntegralOutsideCenteredSquare l v b u
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) q (suzukiXiSmoothReflectionSource rho r x tau))
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l v b u (suzukiXiSmoothReflectionField rho r x tau) +
        (2 * Real.pi * I) * ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
          suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  let c := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  let F := suzukiXiSmoothReflectionField rho r x tau
  have hs := tendsto_square_suzukiXiSmoothReflectionField rho hzero hr x tau
  have ht := (tendsto_const_nhds (x := rectangularBoundaryIntegral l v b u F)).sub hs
  have hlim : Tendsto (fun q : ℝ => rectangularBoundaryIntegral l v b u F -
      rectangularBoundaryIntegral (c.re-q) (c.re+q) (c.im-q) (c.im+q) F) (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l v b u F + (2 * Real.pi * I) *
        ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹ * suzukiSmoothSpectralBoundaryHeat x tau c))) := by
    simpa only [mul_neg, neg_mul, sub_neg_eq_add] using ht
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hl), Ioo_mem_nhdsGT (sub_pos.mpr hv),
    Ioo_mem_nhdsGT (sub_pos.mpr hb), Ioo_mem_nhdsGT (sub_pos.mpr hu)] with q hql hqv hqb hqu
  have he := suzukiXiSmoothReflectionField_onePunctureSquareCauchyGreen rho hzero hr
    x tau l v b u q hb0 hql.1 (by linarith [hql.2]) (by linarith [hqv.2])
      (by linarith [hqb.2]) (by linarith [hqu.2])
  change rectangularBoundaryIntegral l v b u F = _ at he
  rw [he]
  ring

end
end RiemannGaussian
