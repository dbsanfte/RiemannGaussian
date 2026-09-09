/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierCircleAverage
import RiemannGaussian.SuzukiEtaContourGeometry
import RiemannGaussian.SuzukiReflectionWeightSector
import RiemannGaussian.SuzukiCarrierReflectionComparison

/-!
# Bounding the projected part of both actual strip segments

The exact parameter-circle projection has a quartic weighted strip
bound. Measurability and integrability include its cutoff interface.
On actual admissible sides, the original complex reflection correction
is exactly this bounded part plus the complementary large-value part.
The latter and the original pole residues remain in the full target;
their joint bound is not supplied by this decomposition.
-/

open Complex Filter MeasureTheory Real Set Topology
namespace RiemannGaussian
noncomputable section

/-- The literal carrier, with its original point values at exceptions,
is measurable. This statement does not assert continuity at its poles. -/
theorem measurable_suzukiXiZeroCarrier : Measurable suzukiXiZeroCarrier := by
  have hA : Continuous riemannXiSpectral := differentiable_riemannXiSpectral.continuous
  have hd : Continuous (deriv riemannXiSpectral) := continuous_iff_continuousAt.mpr
    (fun z => (analyticAt_riemannXiSpectral z).deriv.continuousAt)
  unfold suzukiXiZeroCarrier suzukiXiThetaValue suzukiXiEValue suzukiXiESharpValue
    analyticEValue analyticESharpValue
  fun_prop

/-- The exact cutoff is measurable even on the interface where the
parameter-circle integral is singular. -/
theorem measurable_suzukiXiCircleProjection (r : ℝ) : Measurable (suzukiXiCircleProjection r) := by
  unfold suzukiXiCircleProjection
  exact Measurable.ite
    (measurableSet_lt (measurable_const.mul measurable_suzukiXiZeroCarrier.norm) measurable_const)
    measurable_suzukiXiZeroCarrier measurable_const

private lemma weight_measurable (rho : NontrivialZetaZero) :
    Measurable (suzukiXiReflectionWeight rho) := by
  unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
  fun_prop

private lemma projected_bound (rho : NontrivialZetaZero) {r R v y : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hv : R ≤ |v|)
    (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)‖ ≤
        64 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) := by
  rw [norm_mul]
  calc
    _ ≤ (64 * (zetaSpectralCoordinate rho.1).im ^ 2 / R ^ 4) * (1 / r) := by
      apply mul_le_mul (norm_suzukiXiReflectionWeight_vertical_le rho hR hv ha)
        (norm_suzukiXiCircleProjection_lt hr _).le (norm_nonneg _)
      positivity
    _ = _ := by ring

/-- Every projected weighted strip trace is genuinely integrable on
the complete segment, including all cutoff crossings and both endpoints. -/
theorem intervalIntegrable_suzukiXiCircleProjection_weighted_vertical
    (rho : NontrivialZetaZero) {r R v : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    IntervalIntegrable (fun y : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)) volume 0 (1 / 2) := by
  have hm : Measurable (fun y : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)) :=
    ((weight_measurable rho).comp (by fun_prop)).mul
      ((measurable_suzukiXiCircleProjection r).comp (by fun_prop))
  exact (intervalIntegrable_const (c := 64 * (zetaSpectralCoordinate rho.1).im ^ 2 /
    (r * R ^ 4))).mono_fun' hm.aestronglyMeasurable
      (Eventually.of_forall (fun _ => projected_bound rho hr hR hv ha))

/-- A complete projected side has a quartic bound, with no denominator
floor inside the strip and no exceptional cutoff points removed. -/
theorem norm_integral_suzukiXiCircleProjection_weighted_vertical_le
    (rho : NontrivialZetaZero) {r R v : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)‖ ≤
        32 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1 / 2)
    (fun y _hy => projected_bound rho hr hR hv ha (y := y))
  norm_num only [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hb
  convert hb using 1
  ring

/-- Both projected strip sides, retaining their original opposing
orientations and their complex reflection weights. -/
def suzukiXiProjectedReflectionStripSides (rho : NontrivialZetaZero) (r l v : ℝ) : ℂ :=
  I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
    suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)) -
  I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
    suzukiXiCircleProjection r ((l : ℂ) + (y : ℂ) * I))

/-- An independent quartic estimate for the bounded part of both
complete strip segments, before taking any real part. -/
theorem norm_suzukiXiProjectedReflectionStripSides_le
    (rho : NontrivialZetaZero) {r R l v : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hl : R ≤ |l|) (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R) :
    ‖suzukiXiProjectedReflectionStripSides rho r l v‖ ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) := by
  have hleft := norm_integral_suzukiXiCircleProjection_weighted_vertical_le rho hr hR hl ha
  have hright := norm_integral_suzukiXiCircleProjection_weighted_vertical_le rho hr hR hv ha
  unfold suzukiXiProjectedReflectionStripSides
  calc
    _ ≤ ‖I * _‖ + ‖I * _‖ := norm_sub_le _ _
    _ ≤ 32 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) +
        32 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) := by
      simpa only [norm_mul, norm_I, one_mul] using add_le_add hright hleft
    _ = _ := by ring

private lemma mixed_integrable (a b : NontrivialZetaZero) {v : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v) :
    IntervalIntegrable (fun y : ℝ => suzukiXiMixedCarrierChannel a b ((v : ℂ) + (y : ℂ) * I))
      volume 0 (1 / 2) := by
  apply Continuous.intervalIntegrable
  apply continuous_comp_of_forall_analyticAt _ _ (by fun_prop)
  intro y
  apply analyticAt_suzukiXiMixedCarrierChannel_of_not_mem
  intro hc
  exact hv.1 _ hc (by simp)

private lemma reflection_integrable (rho : NontrivialZetaZero) {v : ℝ}
    (hv : SuzukiXiEtaVerticalAdmissible v) :
    IntervalIntegrable (fun y : ℝ => suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I)) volume 0 (1 / 2) := by
  have hh := (((mixed_integrable rho rho hv).sub
    (mixed_integrable rho rho.conjugatePartner hv)).sub
      (mixed_integrable rho.conjugatePartner rho hv)).add
        (mixed_integrable rho.conjugatePartner rho.conjugatePartner hv)
  change IntervalIntegrable (fun y : ℝ => suzukiXiReflectionCarrierChannel rho
    ((v : ℂ) + (y : ℂ) * I)) volume 0 (1 / 2) at hh
  simpa only [suzukiXiReflectionCarrierChannel_eq_weight_mul] using hh

private lemma density_split (rho : NontrivialZetaZero) (r : ℝ) (z : ℂ) :
    suzukiXiReflectionWeight rho z * suzukiXiZeroCarrier z =
      suzukiXiReflectionWeight rho z * suzukiXiCircleProjection r z +
        if 1 ≤ r * ‖suzukiXiZeroCarrier z‖ then
          suzukiXiReflectionWeight rho z * suzukiXiZeroCarrier z else 0 := by
  by_cases h : r * ‖suzukiXiZeroCarrier z‖ < 1
  · simp [suzukiXiCircleProjection, h, not_le_of_gt h]
  · simp [suzukiXiCircleProjection, h, le_of_not_gt h]

/-- The original full side splits into two genuine complex integrals.
All large values and cutoff-boundary values are retained in the second. -/
theorem integral_suzukiXiReflection_vertical_eq_projection_add_large
    (rho : NontrivialZetaZero) {r R v : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hvadm : SuzukiXiEtaVerticalAdmissible v) :
    (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I)) =
    (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiCircleProjection r ((v : ℂ) + (y : ℂ) * I)) +
    (∫ y : ℝ in 0..(1 / 2), if 1 ≤ r * ‖suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I)‖ then
      suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
        suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I) else 0) := by
  have hp := intervalIntegrable_suzukiXiCircleProjection_weighted_vertical rho hr hR hv ha
  have ht := reflection_integrable rho hvadm
  have hl := ht.sub hp
  have he (z : ℂ) : suzukiXiReflectionWeight rho z * suzukiXiZeroCarrier z -
      suzukiXiReflectionWeight rho z * suzukiXiCircleProjection r z =
        if 1 ≤ r * ‖suzukiXiZeroCarrier z‖ then
          suzukiXiReflectionWeight rho z * suzukiXiZeroCarrier z else 0 := by
    linear_combination density_split rho r z
  simp only [he] at hl
  rw [← intervalIntegral.integral_add hp hl]
  apply intervalIntegral.integral_congr
  intro y _hy
  exact density_split rho r _

/-- The retained large-value correction, with both original strip
orientations, all complex phases and the whole threshold interface. -/
def suzukiXiLargeReflectionStripSides (rho : NontrivialZetaZero) (r l v : ℝ) : ℂ :=
  I * (∫ y : ℝ in 0..(1 / 2), if 1 ≤ r * ‖suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I)‖ then
    suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
      suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I) else 0) -
  I * (∫ y : ℝ in 0..(1 / 2), if 1 ≤ r * ‖suzukiXiZeroCarrier ((l : ℂ) + (y : ℂ) * I)‖ then
    suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
      suzukiXiZeroCarrier ((l : ℂ) + (y : ℂ) * I) else 0)

/-- The original mixed strip correction is exactly the bounded
projection plus the retained large-value correction. Neither side,
mixed reflection term, nor pole contribution is implicitly dropped. -/
theorem suzukiXiReflection_strip_eq_projected_add_large
    (rho : NontrivialZetaZero) {r R l v : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hl : R ≤ |l|) (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hladm : SuzukiXiEtaVerticalAdmissible l) (hvadm : SuzukiXiEtaVerticalAdmissible v) :
    suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiMixedCarrierStripSides a b l v) =
      suzukiXiProjectedReflectionStripSides rho r l v +
        suzukiXiLargeReflectionStripSides rho r l v := by
  have hpath (x : ℝ) (hx : SuzukiXiEtaVerticalAdmissible x) :
      suzukiXiReflectionPairQuadratic rho (fun a b => ∫ y : ℝ in 0..(1 / 2),
        suzukiXiMixedCarrierChannel a b ((x : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((x : ℂ) + (y : ℂ) * I) *
        suzukiXiZeroCarrier ((x : ℂ) + (y : ℂ) * I) := by
    rw [suzukiXiReflectionPairQuadratic_intervalIntegral rho _ _ _ (fun a b => mixed_integrable a b hx)]
    change (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionCarrierChannel rho
      ((x : ℂ) + (y : ℂ) * I)) = _
    simp only [suzukiXiReflectionCarrierChannel_eq_weight_mul]
  calc
    _ = I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((v : ℂ) + (y : ℂ) * I) *
          suzukiXiZeroCarrier ((v : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in 0..(1 / 2), suzukiXiReflectionWeight rho ((l : ℂ) + (y : ℂ) * I) *
          suzukiXiZeroCarrier ((l : ℂ) + (y : ℂ) * I)) := by
      rw [← hpath v hvadm, ← hpath l hladm]
      unfold suzukiXiReflectionPairQuadratic suzukiXiMixedCarrierStripSides
      ring
    _ = _ := by
      rw [integral_suzukiXiReflection_vertical_eq_projection_add_large rho hr hR hv ha hvadm,
        integral_suzukiXiReflection_vertical_eq_projection_add_large rho hr hR hl ha hladm]
      unfold suzukiXiProjectedReflectionStripSides suzukiXiLargeReflectionStripSides
      ring

/-- Removing the bounded projection changes the complete original
pole-and-strip correction by at most the proved quartic error. The
right-hand retained expression contains every genuine pole residue
and both signed large-value strip integrals. -/
theorem suzukiXiReflectionStripCorrection_large_error_le
    (rho : NontrivialZetaZero) {r R l v u : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hl : R ≤ |l|) (hv : R ≤ |v|) (ha : 2 * |(zetaSpectralCoordinate rho.1).re| ≤ R)
    (hladm : SuzukiXiEtaVerticalAdmissible l) (hvadm : SuzukiXiEtaVerticalAdmissible v) :
    |suzukiXiReflectionStripCorrection rho l v u -
      (2 * Real.pi * (suzukiXiReflectionPairQuadratic rho (fun a b =>
        ∑ c ∈ suzukiXiCarrierGenuinePoleWindow l v 0 u, suzukiXiMixedCarrierPoleResidue a b c)).re -
          (suzukiXiLargeReflectionStripSides rho r l v).im)| ≤
      64 * (zetaSpectralCoordinate rho.1).im ^ 2 / (r * R ^ 4) := by
  have hproj (w : ℂ) : ((w - starRingEnd ℂ w) / (2 * I)).re = w.im := by
    have he : (w - starRingEnd ℂ w) / (2 * I) = (w.im : ℂ) := by
      rw [Complex.sub_conj]
      push_cast
      field_simp
    rw [he, ofReal_re]
  have hs : (suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiCarrierStripSidesGram a b l v)).re =
      (suzukiXiProjectedReflectionStripSides rho r l v).im +
        (suzukiXiLargeReflectionStripSides rho r l v).im := by
    unfold suzukiXiCarrierStripSidesGram
    rw [suzukiXiReflectionPairQuadratic_signedProjection, hproj,
      suzukiXiReflection_strip_eq_projected_add_large rho hr hR hl hv ha hladm hvadm, add_im]
  unfold suzukiXiReflectionStripCorrection
  rw [hs, show ∀ p a b : ℝ, p - (a + b) - (p - b) = -a by intros; ring, abs_neg]
  exact (Complex.abs_im_le_norm _).trans
    (norm_suzukiXiProjectedReflectionStripSides_le rho hr hR hl hv ha)

end
end RiemannGaussian
