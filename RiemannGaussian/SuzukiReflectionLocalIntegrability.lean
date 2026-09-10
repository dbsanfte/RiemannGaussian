/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassRegularity
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteAreaIntegrability

/-!
# Planar integrability through the actual reflection nodes

The full weighted reflection field has a smooth simple-pole numerator
at each selected node. Differentiating this local identity retains the
complete signed source. The complex inverse is locally integrable in
two real dimensions, so both actual fields are integrable on compact
planar sets without deleting the selected nodes.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The full Gaussian-reflection field has a smooth simple-pole numerator
at each selected node, retaining the exact inverse multiplicity. -/
theorem exists_suzukiXiSmoothReflectionField_node_numerator
    (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ p : ℂ → ℂ, ContDiffAt ℝ ∞ p (zetaSpectralCoordinate rho.1) ∧
      p (zetaSpectralCoordinate rho.1) =
        -suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
          (analyticZetaZeroMultiplicity rho : ℂ) ∧
      suzukiXiSmoothReflectionField rho r c tau =ᶠ[𝓝[≠] (zetaSpectralCoordinate rho.1)]
        fun z => p z / (z - zetaSpectralCoordinate rho.1) := by
  obtain ⟨q, hq, hq0, he⟩ := exists_suzukiXiSmoothCarrier_zero_chart rho r
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  let d := fun z => ((1 + r ^ 2 * normSq ((z - a) * q z) : ℝ) : ℂ)
  let t := fun z => (z - a) / (z - b) - 1
  let p := fun z => -(t z) ^ 2 * q z / d z * suzukiSmoothSpectralBoundaryHeat c tau z
  have hab : a ≠ b := by
    intro heq
    have hi := congrArg Complex.im heq
    change a.im = -a.im at hi
    exact him (by linarith)
  have hqR : ContDiffAt ℝ ∞ q a := hq.contDiffAt.restrict_scalars ℝ
  have hv : ContDiffAt ℝ ∞ (fun z : ℂ => (z - a) * q z) a :=
    (contDiffAt_id.sub contDiffAt_const).mul hqR
  have hn : ContDiffAt ℝ ∞ (fun z => normSq ((z - a) * q z)) a := by
    simpa only [normSq_eq_norm_sq] using hv.norm_sq (𝕜 := ℂ)
  have hd : ContDiffAt ℝ ∞ d a :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp a
      (contDiffAt_const.add (contDiffAt_const.mul hn))
  have ht : ContDiffAt ℝ ∞ t a := by
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => z - a) a := contDiffAt_id.sub contDiffAt_const
    have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => z - b) a := contDiffAt_id.sub contDiffAt_const
    simpa only [t, div_eq_mul_inv] using
      (h1.mul (h2.fun_inv (sub_ne_zero.mpr hab))).sub contDiffAt_const
  have hp : ContDiffAt ℝ ∞ p a := by
    have hd0 : d a ≠ 0 := by simp [d]
    simpa only [p, div_eq_mul_inv] using
      ((((ht.pow 2).neg.mul hqR).mul (hd.fun_inv hd0)).mul
        (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt)
  refine ⟨p, hp, ?_, ?_⟩
  · dsimp only [p, t, d, a]
    rw [hq0]
    simp
    ring
  · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
      (continuousAt_id.eventually_ne hab).filter_mono nhdsWithin_le_nhds] with z hz hza hzb
    change z ≠ a at hza
    have hza' := sub_ne_zero.mpr hza
    have hzb' := sub_ne_zero.mpr hzb
    rw [suzukiXiSmoothReflectionField, hz, complexSmoothQuotient_one_right]
    unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
    dsimp only [p, t, d, a, b] at hza' hzb' ⊢
    field_simp
    ring

private lemma cauchyGreen_contDiffAt {f : ℂ → ℂ} {a : ℂ} (hf : ContDiffAt ℝ ∞ f a) :
    ContDiffAt ℝ 0 (complexCauchyGreenSource f) a := by
  have hd : ContDiffAt ℝ 0 (fderiv ℝ f) a := hf.fderiv_right (by simp)
  exact (contDiffAt_const.mul (hd.clm_apply contDiffAt_const)).sub
    (hd.clm_apply contDiffAt_const)

/-- The actual signed density has a locally integrable simple-pole
model. The numerator includes both the carrier source and companion heat. -/
theorem exists_suzukiXiSmoothReflectionSource_node_numerator
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ p : ℂ → ℂ, ContDiffAt ℝ 0 p (zetaSpectralCoordinate rho.1) ∧
      suzukiXiSmoothReflectionSource rho r c tau =ᶠ[𝓝[≠] (zetaSpectralCoordinate rho.1)]
        fun z => p z / (z - zetaSpectralCoordinate rho.1) := by
  obtain ⟨p, hp, _hp0, he⟩ := exists_suzukiXiSmoothReflectionField_node_numerator rho r c tau him
  refine ⟨complexCauchyGreenSource p, cauchyGreen_contDiffAt hp, ?_⟩
  have he' : ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1),
      suzukiXiSmoothReflectionField rho r c tau =ᶠ[𝓝 z]
        fun w => p w / (w - zetaSpectralCoordinate rho.1) :=
    eventually_nhdsNE_eventually_nhds_iff.mpr he
  have hp' := (hp.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hab : zetaSpectralCoordinate rho.1 ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
    intro heq
    have hi := congrArg Complex.im heq
    simp only [conj_im] at hi
    exact him (by linarith)
  filter_upwards [he', hp'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
    (continuousAt_id.eventually_ne hab).filter_mono nhdsWithin_le_nhds] with z hz hpz hza hzb
  have hid : DifferentiableAt ℂ (fun w : ℂ => w - zetaSpectralCoordinate rho.1) z :=
    differentiableAt_id.sub_const _
  have hdiff : complexCauchyGreenSource (suzukiXiSmoothReflectionField rho r c tau) z =
      complexCauchyGreenSource (fun w => p w / (w - zetaSpectralCoordinate rho.1)) z := by
    unfold complexCauchyGreenSource
    rw [hz.fderiv_eq]
  change complexCauchyGreenSource (fun w =>
    (suzukiXiReflectionWeight rho w * suzukiXiSmoothCarrier r w) *
      suzukiSmoothSpectralBoundaryHeat c tau w) z = _ at hdiff
  rw [complexCauchyGreenSource_suzukiXiSmoothCarrier_reflection_heat rho hr c tau hza hzb] at hdiff
  change suzukiXiSmoothReflectionSource rho r c tau z = _ at hdiff
  rw [hdiff, complexCauchyGreenSource_div hpz.differentiableAt_one
    (hid.restrictScalars ℝ) (sub_ne_zero.mpr hza), complexCauchyGreenSource_eq_zero hid]
  simp only [mul_zero, sub_zero]
  field_simp

private lemma integrableAt_of_local_contDiff {g : ℂ → ℂ} {a : ℂ}
    (hg : ContDiffAt ℝ 0 g a) : IntegrableAtFilter g (𝓝 a) volume := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨K, hKa, hK, hKu⟩ := exists_mem_nhds_isCompact_mapsTo continuous_id hu
  exact ⟨K, hKa, (hgu.continuousOn.mono hKu).integrableOn_compact hK⟩

private lemma integrableAt_of_local_simplePole {g p : ℂ → ℂ} {a : ℂ}
    (hp : ContDiffAt ℝ 0 p a)
    (he : g =ᶠ[𝓝[≠] a] fun z => p z / (z - a)) :
    IntegrableAtFilter g (𝓝 a) volume := by
  obtain ⟨u, hu, hpu⟩ := hp.contDiffOn le_rfl (by simp)
  have he' : ∀ᶠ z in 𝓝 a, z ≠ a → g z = p z / (z - a) :=
    eventually_nhdsWithin_iff.mp he
  obtain ⟨K, hKa, hK, hKu⟩ := exists_mem_nhds_isCompact_mapsTo continuous_id (inter_mem hu he')
  have hpK : ContinuousOn p K := hpu.continuousOn.mono (fun z hz => (hKu hz).1)
  have hi : IntegrableOn (fun z : ℂ => p z / (z - a)) K volume := by
    simpa only [div_eq_mul_inv] using IntegrableOn.continuousOn_mul hpK
      (locallyIntegrable_complex_inv_sub a |>.integrableOn_isCompact hK) hK
  refine ⟨K, hKa, hi.congr ?_⟩
  filter_upwards [ae_restrict_mem hK.measurableSet,
    ae_restrict_of_ae (show ∀ᵐ z : ℂ ∂volume, z ≠ a by
      rw [ae_iff]
      simp)] with z hz hza
  exact ((hKu hz).2 hza).symm

private lemma field_zero_on_axis (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im = 0) :
    suzukiXiSmoothReflectionField rho r c tau = 0 ∧
      suzukiXiSmoothReflectionSource rho r c tau = 0 := by
  have hab := Complex.conj_eq_iff_im.mpr him
  constructor <;> funext z <;>
    simp [suzukiXiSmoothReflectionField, suzukiXiSmoothReflectionSource,
      suzukiXiReflectionWeight, suzukiXiReflectionCauchyDifference, hab]

/-- The literal full weighted field is locally Lebesgue integrable in
the plane, including both selected reflection nodes and every carrier pole. -/
theorem locallyIntegrable_suzukiXiSmoothReflectionField
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    LocallyIntegrable (suzukiXiSmoothReflectionField rho r c tau) volume := by
  by_cases him : (zetaSpectralCoordinate rho.1).im = 0
  · rw [(field_zero_on_axis rho r c tau him).1]
    exact continuous_zero.locallyIntegrable
  intro z
  by_cases ha : z = zetaSpectralCoordinate rho.1
  · subst z
    obtain ⟨p, hp, _hp0, he⟩ := exists_suzukiXiSmoothReflectionField_node_numerator rho r c tau him
    exact integrableAt_of_local_simplePole (hp.of_le (by simp)) he
  by_cases hb : z = starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  · subst z
    obtain ⟨p, hp, _hp0, he⟩ :=
      exists_suzukiXiSmoothReflectionField_node_numerator rho.conjugatePartner r c tau
        (by simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, neg_ne_zero] using him)
    have hi := integrableAt_of_local_simplePole (hp.of_le (by simp)) he
    have heq : suzukiXiSmoothReflectionField rho.conjugatePartner r c tau =
        suzukiXiSmoothReflectionField rho r c tau := by
      funext w
      simp only [suzukiXiSmoothReflectionField, suzukiXiReflectionWeight_conjugatePartner]
    rw [heq] at hi
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hi
  apply integrableAt_of_local_contDiff
  exact ((((analyticAt_suzukiXiReflectionWeight rho ha hb).contDiffAt.restrict_scalars ℝ).mul
    (contDiff_suzukiXiSmoothCarrier hr).contDiffAt).mul
      (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt).of_le (by simp)

/-- The complete signed density is locally Lebesgue integrable through
the reflection divisor. This is a two-dimensional statement, not a
claim of integrability on the exceptional horizontal lines. -/
theorem locallyIntegrable_suzukiXiSmoothReflectionSource
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    LocallyIntegrable (suzukiXiSmoothReflectionSource rho r c tau) volume := by
  by_cases him : (zetaSpectralCoordinate rho.1).im = 0
  · rw [(field_zero_on_axis rho r c tau him).2]
    exact continuous_zero.locallyIntegrable
  intro z
  by_cases ha : z = zetaSpectralCoordinate rho.1
  · subst z
    obtain ⟨p, hp, he⟩ := exists_suzukiXiSmoothReflectionSource_node_numerator rho hr c tau him
    exact integrableAt_of_local_simplePole hp he
  by_cases hb : z = starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  · subst z
    obtain ⟨p, hp, he⟩ :=
      exists_suzukiXiSmoothReflectionSource_node_numerator rho.conjugatePartner hr c tau
        (by simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, neg_ne_zero] using him)
    have hi := integrableAt_of_local_simplePole hp he
    have heq : suzukiXiSmoothReflectionSource rho.conjugatePartner r c tau =
        suzukiXiSmoothReflectionSource rho r c tau := by
      funext w
      simp only [suzukiXiSmoothReflectionSource, suzukiXiReflectionWeight_conjugatePartner]
    rw [heq] at hi
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hi
  apply integrableAt_of_local_contDiff
  exact ((analyticAt_suzukiXiReflectionWeight rho ha hb).contDiffAt.restrict_scalars ℝ).mul
    (contDiff_zero.mpr (continuous_suzukiXiSmoothBoundaryHeatBulk hr c tau)).contDiffAt

end
end RiemannGaussian
