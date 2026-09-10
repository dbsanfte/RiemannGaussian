/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionRemainderDecay

/-!
# Through-node decay of the remainder on compact regions

The independent geometric envelope is integrable on compact sets away
from both reflection nodes. Combining it with the signed disk cancellation
removes the complete remainder from any compact upper region containing
the reflected node in its interior. The region is fixed during smoothing.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff Interval
namespace RiemannGaussian
noncomputable section

/-- On any measurable subset of a fixed compact region avoiding the two
nodes, dominated convergence removes the complete actual remainder.
Genuine carrier poles and repeated xi zeros remain allowed. -/
theorem tendsto_integral_suzukiXiReflectionMassRemainder_compact_avoid
    (rho : NontrivialZetaZero) (c tau : ℝ) {K s : Set ℂ}
    (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K)
    (ha : zetaSpectralCoordinate rho.1 ∉ K)
    (hb : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ∉ K) :
    Tendsto (fun r : ℝ => ∫ z in s, suzukiXiPlanarReflectionMassRemainder rho r c tau z)
      atTop (𝓝 0) := by
  let P := fun z => suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z
  let A := fun z => ‖fderiv ℝ P z 1‖ +
    ‖suzukiXiReflectionWeight rho z *
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z)‖/2
  have hP : ∀ z ∈ K, ContDiffAt ℝ ∞ P z := by
    intro z hz
    exact ((analyticAt_suzukiXiReflectionWeight rho (ne_of_mem_of_not_mem hz ha)
      (ne_of_mem_of_not_mem hz hb)).contDiffAt.restrict_scalars ℝ).mul
        (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt
  have hA : ContinuousOn A K := by
    intro z hz
    have hd : ContinuousAt (fun w : ℂ => fderiv ℝ P w 1) z :=
      ((hP z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
    have hw := (analyticAt_suzukiXiReflectionWeight rho (ne_of_mem_of_not_mem hz ha)
      (ne_of_mem_of_not_mem hz hb)).continuousAt
    exact (hd.norm.add ((hw.mul
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau).continuousAt.comp
        (continuousAt_const.mul continuousAt_id))).norm.div_const 2)).continuousWithinAt
  have hAi : IntegrableOn A s volume := (hA.integrableOn_compact hK).mono_set hsK
  have hbound : ∀ r : ℝ, 0 < r → ∀ z ∈ s,
      ‖suzukiXiPlanarReflectionMassRemainder rho r c tau z‖ ≤ A z / r := by
    intro r hr z hz
    have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + (z.im : ℂ)*I) 1 z.re :=
      Complex.ofRealCLM.hasDerivAt.add_const _
    have hd := (((hP z (hsK hz)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
      z.re hl (Complex.re_add_im z).symm).deriv
    dsimp only [Function.comp_def] at hd
    change deriv (suzukiXiHorizontalReflectionHeat rho c tau z.im) z.re = _ at hd
    have he := norm_suzukiXiReflectionMassRemainder_le rho hr c tau z.im z.re
    rw [hd] at he
    simp only [Complex.re_add_im] at he
    change ‖suzukiXiPlanarReflectionMassRemainder rho r c tau z‖ ≤ _ at he
    convert he using 1
    dsimp only [A]
    ring
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict s) (F := fun r => suzukiXiPlanarReflectionMassRemainder rho r c tau)
    (f := fun _ => (0 : ℂ)) A
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact (((locallyIntegrable_suzukiXiPlanarReflectionMassRemainder rho hr c tau).integrableOn_isCompact hK).mono_set
        hsK).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      filter_upwards [ae_restrict_mem hs] with z hz
      exact (hbound r (lt_of_lt_of_le zero_lt_one hr) z hz).trans
        (div_le_self (by dsimp [A]; positivity) hr))
    hAi
    (ae_of_all _ (fun z => tendsto_suzukiXiPlanarReflectionMassRemainder_atTop rho c tau z))
  simpa only [integral_zero] using hD

/-- The actual complete remainder vanishes in ordinary area integral on
every fixed compact region that avoids the lower node and contains the
upper reflected node in its interior. All node integrability is discharged. -/
theorem tendsto_integral_suzukiXiReflectionMassRemainder_compact_reflected
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ)
    {K : Set ℂ} (hK : IsCompact K) (ha : zetaSpectralCoordinate rho.1 ∉ K)
    (hb : K ∈ 𝓝 (starRingEnd ℂ (zetaSpectralCoordinate rho.1))) :
    Tendsto (fun r : ℝ => ∫ z in K, suzukiXiPlanarReflectionMassRemainder rho r c tau z)
      atTop (𝓝 0) := by
  let a := starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  obtain ⟨R, hR, hlimR⟩ :=
    exists_tendsto_integral_suzukiXiReflectionMassRemainder_reflected_node rho hzero c tau
  obtain ⟨δ, hδ, hδK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hb
  let ε := min R δ
  have hε : 0 < ε := lt_min hR hδ
  have hεR : ε ≤ R := min_le_left _ _
  have hεK : Metric.closedBall a ε ⊆ K :=
    (Metric.closedBall_subset_closedBall (min_le_right R δ)).trans hδK
  have hcomp : IsCompact (K \ Metric.ball a ε) := hK.diff Metric.isOpen_ball
  have havoidA : zetaSpectralCoordinate rho.1 ∉ K \ Metric.ball a ε := by
    exact fun hz => ha hz.1
  have havoidB : a ∉ K \ Metric.ball a ε := by
    intro hz
    exact hz.2 (Metric.mem_ball_self hε)
  have hsub : K \ Metric.closedBall a ε ⊆ K \ Metric.ball a ε := by
    intro z hz
    exact ⟨hz.1, fun hh => hz.2 (Metric.ball_subset_closedBall hh)⟩
  have ht := tendsto_integral_suzukiXiReflectionMassRemainder_compact_avoid rho c tau hcomp
    (hK.measurableSet.diff measurableSet_closedBall) hsub havoidA havoidB
  have hdisk := hlimR ε hε hεR
  have hsum := ht.add hdisk
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hi := (locallyIntegrable_suzukiXiPlanarReflectionMassRemainder rho hr c tau).integrableOn_isCompact hK
  rw [setIntegral_sdiff measurableSet_closedBall hi hεK]
  ring

/-- The remainder disappears on each actual finite upper rectangle
containing the reflected node. This is a smoothing limit on a fixed
rectangle, with the complete companion term and original xi field. -/
theorem tendsto_integral_suzukiXiReflectionMassRemainder_rectangle
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau l v b u : ℝ)
    (hb0 : 0 ≤ b)
    (hl : l < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re)
    (hv : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).re < v)
    (hb : b < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im)
    (hu : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im < u) :
    Tendsto (fun r : ℝ => ∫ z in [[l,v]] ×ℂ [[b,u]],
      suzukiXiPlanarReflectionMassRemainder rho r c tau z) atTop (𝓝 0) := by
  have hlv : l ≤ v := (hl.trans hv).le
  have hbu : b ≤ u := (hb.trans hu).le
  apply tendsto_integral_suzukiXiReflectionMassRemainder_compact_reflected rho hzero c tau
    (isCompact_uIcc.reProdIm isCompact_uIcc)
  · intro hz
    rw [Complex.mem_reProdIm, uIcc_of_le hlv, uIcc_of_le hbu] at hz
    have hi := hz.2.1
    rw [zetaSpectralCoordinate_im] at hi
    linarith
  · have hr := Complex.continuous_re.continuousAt.eventually (Icc_mem_nhds hl hv)
    have hi := Complex.continuous_im.continuousAt.eventually (Icc_mem_nhds hb hu)
    filter_upwards [hr, hi] with z hzr hzi
    simpa only [Complex.mem_reProdIm, uIcc_of_le hlv, uIcc_of_le hbu, mem_Icc] using And.intro hzr hzi

/-- On each eligible fixed upper rectangle the entire analytic error
vanishes as smoothing grows: the actual source and its retained signed
mass variation differ only by independently vanishing current edges and
the complete through-node remainder. This does not bound the variation. -/
theorem tendsto_suzukiXiReflectionSource_add_mass_rectangle
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) {tau R : ℝ}
    (htau : 0 ≤ tau) (hR : 0 < R) (c : ℝ)
    (hRe : 2*|(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hIm : (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im < R) :
    Tendsto (fun r : ℝ =>
      (∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiSmoothReflectionSource rho r c tau z) +
        4*I*(r:ℂ)^2*(∫ z in [[-R,R]] ×ℂ [[0,R]],
          suzukiXiPlanarReflectionMassVariation rho r c tau z)) atTop (𝓝 0) := by
  have hrem := tendsto_integral_suzukiXiReflectionMassRemainder_rectangle
    rho hzero c tau (-R) R 0 R le_rfl
    (by rw [conj_re]; nlinarith [neg_le_abs (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_re]; nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).re])
    (by rw [conj_im, zetaSpectralCoordinate_im]; linarith) hIm
  have hedge : Tendsto (fun r : ℝ => suzukiXiReflectionMassEdge rho r c tau R) atTop (𝓝 0) := by
    have hl : Tendsto
        (fun r : ℝ => (256*(zetaSpectralCoordinate rho.1).im^2/R^2)/r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hl
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    convert norm_suzukiXiReflectionMassEdge_le rho hr htau hR c hRe using 1
    ring
  have he := hedge.sub hrem
  simp only [sub_zero] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hi := integral_suzukiXiSmoothReflectionSource_eq_mass_rectangle
    rho hr c tau (-R) R 0 R (by linarith) hR.le
  change (∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiSmoothReflectionSource rho r c tau z) =
    suzukiXiReflectionMassEdge rho r c tau R -
      4*I*(r:ℂ)^2*(∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiPlanarReflectionMassVariation rho r c tau z) -
        (∫ z in [[-R,R]] ×ℂ [[0,R]], suzukiXiPlanarReflectionMassRemainder rho r c tau z) at hi
  rw [hi]
  ring

end
end RiemannGaussian
