/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSmoothHeatBound
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatPuncture

/-!
# The original signed reflection source survives smooth regularization

The full original reflection weight is retained. Its source at the
reflected xi node is exactly minus the inverse analytic multiplicity,
for every positive smoothing radius. Its Cauchy--Green density away
from the two test nodes keeps the complete signed Wronskian and crosses
all genuine carrier poles. A vanishing Gaussian boundary therefore
cannot justify discarding either the node source or the area density.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The original reflection weight is holomorphic away from its two
actual test nodes; no carrier-denominator condition is involved. -/
theorem analyticAt_suzukiXiReflectionWeight (rho : NontrivialZetaZero) {z : ℂ}
    (ha : z ≠ zetaSpectralCoordinate rho.1)
    (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    AnalyticAt ℂ (suzukiXiReflectionWeight rho) z := by
  unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
  exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr ha)).sub
    ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hb))).pow 2 |>.neg

/-- Multiplication by the original reflection weight retains the full
signed area source even at genuine carrier poles. Only the two test
nodes themselves are excluded from this pointwise derivative formula. -/
theorem complexCauchyGreenSource_suzukiXiSmoothCarrier_reflection
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (ha : z ≠ zetaSpectralCoordinate rho.1)
    (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    complexCauchyGreenSource (fun w => suzukiXiReflectionWeight rho w * suzukiXiSmoothCarrier r w) z =
      suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrierSource r z := by
  have hW := (analyticAt_suzukiXiReflectionWeight rho ha hb).differentiableAt
  rw [complexCauchyGreenSource_mul (hW.restrictScalars ℝ)
    ((contDiff_suzukiXiSmoothCarrier hr).differentiable (by simp) z),
    complexCauchyGreenSource_eq_zero hW, zero_mul, zero_add,
    complexCauchyGreenSource_suzukiXiSmoothCarrier hr]

/-- The exact local model gives the original inverse multiplicity in
the first divided smooth carrier, without any simplicity assumption. -/
theorem tendsto_suzukiXiSmoothCarrier_div_node (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun z => suzukiXiSmoothCarrier r z / (z - zetaSpectralCoordinate rho.1))
      (𝓝[≠] zetaSpectralCoordinate rho.1) (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)⁻¹) := by
  obtain ⟨p, hp, he⟩ := exists_suzukiXiSmoothCarrier_source_model rho hr
  let a := zetaSpectralCoordinate rho.1
  have hc : ContinuousAt (fun z => (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ + (z - a) * p z) a :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hp.continuousAt)
  have ht : Tendsto (fun z => (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ + (z - a) * p z)
      (𝓝[≠] a) (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)⁻¹) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [he, self_mem_nhdsWithin] with z hz hza
  have hz0 : z - a ≠ 0 := sub_ne_zero.mpr hza
  change suzukiXiSmoothCarrier r z / (z - a) ^ 2 =
    (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ / (z - a) + p z at hz
  change _ = suzukiXiSmoothCarrier r z / (z - a)
  field_simp at hz ⊢
  linear_combination -hz

private lemma reflected_node_ne (rho : NontrivialZetaZero)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate rho.1 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  exact him (by linear_combination -hi / 2)

/-- The complete reflection-weighted field has precisely the original
negative xi source at the upper partner of a hypothetical right-half
zero. This statement preserves the actual analytic multiplicity. -/
theorem tendsto_sub_mul_suzukiXiSmoothCarrier_reflection
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    Tendsto (fun z => (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z))
      (𝓝[≠] starRingEnd ℂ (zetaSpectralCoordinate rho.1))
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹)) := by
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  have hba : b ≠ a := reflected_node_ne rho him
  have hS : Tendsto (fun z => suzukiXiSmoothCarrier r z / (z - b))
      (𝓝[≠] b) (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)⁻¹) := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
      analyticZetaZeroMultiplicity_conjugatePartner] using
      tendsto_suzukiXiSmoothCarrier_div_node rho.conjugatePartner hr
  have hc : ContinuousAt (fun z : ℂ => -((z - b) / (z - a) - 1) ^ 2) b := by
    fun_prop (disch := exact sub_ne_zero.mpr hba)
  have ht : Tendsto (fun z => -((z - b) / (z - a) - 1) ^ 2 *
      (suzukiXiSmoothCarrier r z / (z - b))) (𝓝[≠] b)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹)) := by
    simpa using (hc.tendsto.mono_left nhdsWithin_le_nhds).mul hS
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (continuousAt_id.eventually_ne hba).filter_mono nhdsWithin_le_nhds] with z hzb hza
  change z ≠ b at hzb
  unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
  change _ = (z - b) * (-((z - a)⁻¹ - (z - b)⁻¹) ^ 2 * _)
  field_simp

/-- Every sufficiently small circle around the reflected node is an
actual integrable contour for the smoothed reflection field, including
any original denominator zeros on that circle. -/
theorem eventually_circleIntegrable_suzukiXiSmoothCarrier_reflection
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∀ᶠ q : ℝ in 𝓝[>] 0,
      CircleIntegrable (fun z => suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z)
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) q := by
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  have hd : 0 < dist a b := dist_pos.mpr (reflected_node_ne rho him).symm
  filter_upwards [Ioo_mem_nhdsGT hd] with q hq
  apply ContinuousOn.circleIntegrable hq.1.le
  intro z hz
  have hdist : dist z b = q := by simpa only [Metric.mem_sphere] using hz
  have hza : z ≠ a := by
    intro he
    rw [he] at hdist
    linarith [hq.2]
  have hzb : z ≠ b := by
    intro he
    rw [he, dist_self] at hdist
    linarith [hq.1]
  exact ((analyticAt_suzukiXiReflectionWeight rho hza hzb).continuousAt.mul
    (contDiff_suzukiXiSmoothCarrier hr).continuous.continuousAt).continuousWithinAt

/-- The shrinking reflected-node contour keeps exactly `-2*pi*i/m`
for every positive smoothing radius. Smoothness at the carrier poles
does not remove the original reflection source. -/
theorem tendsto_circleIntegral_suzukiXiSmoothCarrier_reflection
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    Tendsto (fun q : ℝ => ∮ z in C(starRingEnd ℂ (zetaSpectralCoordinate rho.1), q),
      suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * I) * (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹))) :=
  tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul
    (eventually_circleIntegrable_suzukiXiSmoothCarrier_reflection rho hr him)
    (tendsto_sub_mul_suzukiXiSmoothCarrier_reflection rho hr him)

/-- The Gaussian and original reflection weight retain both signed
area terms as exactly the reflection weight times the complete bulk.
All genuine carrier poles are included; only the two test nodes are
excluded from this local differential identity. -/
theorem complexCauchyGreenSource_suzukiXiSmoothCarrier_reflection_heat
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ) {z : ℂ}
    (ha : z ≠ zetaSpectralCoordinate rho.1)
    (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    complexCauchyGreenSource (fun w =>
      (suzukiXiReflectionWeight rho w * suzukiXiSmoothCarrier r w) *
        suzukiSmoothSpectralBoundaryHeat x tau w) z =
      suzukiXiReflectionWeight rho z * suzukiXiSmoothBoundaryHeatBulk r x tau z := by
  have hF : DifferentiableAt ℝ (fun w => suzukiXiReflectionWeight rho w * suzukiXiSmoothCarrier r w) z :=
    ((analyticAt_suzukiXiReflectionWeight rho ha hb).differentiableAt.restrictScalars ℝ).mul
      ((contDiff_suzukiXiSmoothCarrier hr).differentiable (by simp) z)
  rw [complexCauchyGreenSource_mul hF (differentiable_suzukiSmoothSpectralBoundaryHeat x tau z),
    complexCauchyGreenSource_suzukiXiSmoothCarrier_reflection rho hr ha hb,
    complexCauchyGreenSource_suzukiSmoothSpectralBoundaryHeat]
  unfold suzukiXiSmoothBoundaryHeatBulk
  ring

/-- The moving Gaussian preserves the exact signed reflected source,
with its actual value at the zero rather than a frozen or absolute weight. -/
theorem tendsto_sub_mul_suzukiXiSmoothCarrier_reflection_heat
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    Tendsto (fun z => (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      ((suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z) *
        suzukiSmoothSpectralBoundaryHeat x tau z))
      (𝓝[≠] starRingEnd ℂ (zetaSpectralCoordinate rho.1))
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)))) := by
  simpa only [mul_assoc] using (tendsto_sub_mul_suzukiXiSmoothCarrier_reflection rho hr him).mul
    ((differentiable_suzukiSmoothSpectralBoundaryHeat x tau).continuous.tendsto
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) |>.mono_left nhdsWithin_le_nhds)

/-- The actual Gaussian-reflection puncture has its full source for
every positive smoothing radius and all Gaussian centers and times.
This is the source term required in any subsequent weighted area excision. -/
theorem tendsto_circleIntegral_suzukiXiSmoothCarrier_reflection_heat
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (x tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    Tendsto (fun q : ℝ => ∮ z in C(starRingEnd ℂ (zetaSpectralCoordinate rho.1), q),
      (suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z) *
        suzukiSmoothSpectralBoundaryHeat x tau z) (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * I) * (-(analyticZetaZeroMultiplicity rho : ℂ)⁻¹ *
        suzukiSmoothSpectralBoundaryHeat x tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1))))) := by
  apply tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul _
    (tendsto_sub_mul_suzukiXiSmoothCarrier_reflection_heat rho hr x tau him)
  filter_upwards [eventually_circleIntegrable_suzukiXiSmoothCarrier_reflection rho hr him] with q hq
  exact hq.mul_continuousOn (differentiable_suzukiSmoothSpectralBoundaryHeat x tau).continuous.continuousOn

end
end RiemannGaussian
