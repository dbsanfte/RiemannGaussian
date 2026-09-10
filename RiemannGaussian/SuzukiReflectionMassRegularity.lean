/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassIntegral

/-!
# Removal of the reflection nodes from the exact mass current

The normalized mass times the carrier vanishes to third real order at
every xi zero. Keeping these factors together cancels the double pole of
the reflection weight. The resulting current is smooth at both selected
nodes and has an explicit conjugate-linear first term. All multiplicities
and the full complex Gaussian weight are retained.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The actual mass current as a function on the complex plane. -/
def suzukiXiPlanarReflectionMassCurrent (rho : NontrivialZetaZero)
    (r c tau : ℝ) (z : ℂ) : ℂ :=
  suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z *
    (suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z

/-- Restriction of the planar current is the original horizontal current. -/
theorem suzukiXiPlanarReflectionMassCurrent_horizontal (rho : NontrivialZetaZero)
    (r c tau y x : ℝ) :
    suzukiXiPlanarReflectionMassCurrent rho r c tau ((x : ℂ) + (y : ℂ) * I) =
      suzukiXiReflectionMassCurrent rho r c tau y x := rfl

/-- The original reflection weight is unchanged by exchanging its two nodes. -/
theorem suzukiXiReflectionWeight_conjugatePartner (rho : NontrivialZetaZero) (z : ℂ) :
    suzukiXiReflectionWeight rho.conjugatePartner z = suzukiXiReflectionWeight rho z := by
  simp only [suzukiXiReflectionWeight, suzukiXiReflectionCauchyDifference,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_conj]
  ring

/-- Exchanging the two nodes retains the complete complex mass current. -/
theorem suzukiXiPlanarReflectionMassCurrent_conjugatePartner (rho : NontrivialZetaZero)
    (r c tau : ℝ) :
    suzukiXiPlanarReflectionMassCurrent rho.conjugatePartner r c tau =
      suzukiXiPlanarReflectionMassCurrent rho r c tau := by
  funext z
  simp only [suzukiXiPlanarReflectionMassCurrent, suzukiXiReflectionWeight_conjugatePartner]

private lemma node_ne_conj (rho : NontrivialZetaZero)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    zetaSpectralCoordinate rho.1 ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
  intro he
  have hi := congrArg Complex.im he
  simp only [conj_im] at hi
  exact him (by linarith)

private lemma coupled_node_chart (rho : NontrivialZetaZero) (r : ℝ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      ∀ᶠ z in 𝓝 (zetaSpectralCoordinate rho.1),
        (suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z =
          (z - zetaSpectralCoordinate rho.1) ^ 2 *
            (q z ^ 2 * starRingEnd ℂ ((z - zetaSpectralCoordinate rho.1) * q z)) /
              ((1 + r ^ 2 * normSq ((z - zetaSpectralCoordinate rho.1) * q z) : ℝ) : ℂ) ^ 2 := by
  obtain ⟨q, p, hq, _hp, hq0, _hp0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz
  by_cases hza : z = zetaSpectralCoordinate rho.1
  · subst z
    rw [suzukiXiNormalizedMass_eq_zero r
      ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩)]
    simp
  · have hlocal := hz hza
    rw [suzukiXiNormalizedMass_eq_regular_chart r hlocal.1,
      suzukiXiSmoothCarrier_eq_radial r hlocal.1, hlocal.2.2.1, ofReal_div,
      ← mul_conj]
    ring

/-- The apparent node singularity has an actual smooth factorization,
including the central value. Its first conjugate-linear coefficient is
independent of the smoothing radius and keeps the inverse cubed multiplicity. -/
theorem exists_suzukiXiPlanarReflectionMassCurrent_node_factor
    (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ p : ℂ → ℂ, ContDiffAt ℝ ∞ p (zetaSpectralCoordinate rho.1) ∧
      p (zetaSpectralCoordinate rho.1) =
        -suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
          (analyticZetaZeroMultiplicity rho : ℂ) ^ 3 ∧
      suzukiXiPlanarReflectionMassCurrent rho r c tau =ᶠ[𝓝 (zetaSpectralCoordinate rho.1)]
        fun z => starRingEnd ℂ (z - zetaSpectralCoordinate rho.1) * p z := by
  obtain ⟨q, hq, hq0, he⟩ := coupled_node_chart rho r
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  let d := fun z => ((1 + r ^ 2 * normSq ((z - a) * q z) : ℝ) : ℂ)
  let p := fun z => (4 * (a.im : ℂ) ^ 2) * suzukiSmoothSpectralBoundaryHeat c tau z *
    q z ^ 2 * starRingEnd ℂ (q z) / ((z - b) ^ 2 * d z ^ 2)
  have hab : a ≠ b := node_ne_conj rho him
  have hqR : ContDiffAt ℝ ∞ q a := hq.contDiffAt.restrict_scalars ℝ
  have hv : ContDiffAt ℝ ∞ (fun z : ℂ => (z - a) * q z) a :=
    (contDiffAt_id.sub contDiffAt_const).mul hqR
  have hn : ContDiffAt ℝ ∞ (fun z => normSq ((z - a) * q z)) a := by
    simpa only [normSq_eq_norm_sq] using hv.norm_sq (𝕜 := ℂ)
  have hd : ContDiffAt ℝ ∞ d a :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp a
      (contDiffAt_const.add (contDiffAt_const.mul hn))
  have hnum : ContDiffAt ℝ ∞ (fun z : ℂ =>
      (4 * (a.im : ℂ) ^ 2) * suzukiSmoothSpectralBoundaryHeat c tau z *
        q z ^ 2 * starRingEnd ℂ (q z)) a :=
    (((contDiffAt_const.mul (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt).mul
      (hqR.pow 2)).mul (Complex.conjCLE.contDiff.contDiffAt.comp a hqR))
  have hden : ContDiffAt ℝ ∞ (fun z : ℂ => (z - b) ^ 2 * d z ^ 2) a :=
    ((contDiffAt_id.sub contDiffAt_const).pow 2).mul (hd.pow 2)
  have hp : ContDiffAt ℝ ∞ p a := by
    have hne : (a - b) ^ 2 * d a ^ 2 ≠ 0 := by
      simpa [d] using pow_ne_zero 2 (sub_ne_zero.mpr hab)
    simpa only [p, div_eq_mul_inv] using hnum.mul (hden.fun_inv hne)
  refine ⟨p, hp, ?_, ?_⟩
  · have hdiff : a - b = 2 * I * (a.im : ℂ) := by
      dsimp only [b]
      apply Complex.ext
      · simp
      · simp
        ring
    have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
      exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
    have hi : (a.im : ℂ) ≠ 0 := by exact_mod_cast him
    dsimp only [p, d]
    rw [show a = zetaSpectralCoordinate rho.1 from rfl, hq0]
    change 4 * (a.im : ℂ) ^ 2 * suzukiSmoothSpectralBoundaryHeat c tau a *
      (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ^ 2 *
        starRingEnd ℂ ((analyticZetaZeroMultiplicity rho : ℂ)⁻¹) /
          ((a - b) ^ 2 * ((1 + r ^ 2 * normSq ((a - a) *
            (analyticZetaZeroMultiplicity rho : ℂ)⁻¹) : ℝ) : ℂ) ^ 2) = _
    simp only [sub_self, zero_mul, map_zero, mul_zero, add_zero, ofReal_one,
      one_pow, mul_one, map_inv₀, map_natCast, hdiff, mul_pow, I_sq]
    field_simp
    ring
  · filter_upwards [he, continuousAt_id.eventually_ne hab] with z hz hzb
    by_cases hza : z = a
    · subst z
      have hz0 : (suzukiXiNormalizedMass r a : ℂ) * suzukiXiSmoothCarrier r a = 0 := by
        simpa [a] using hz
      rw [suzukiXiPlanarReflectionMassCurrent, mul_assoc, hz0]
      simp [a]
    · rw [suzukiXiPlanarReflectionMassCurrent, mul_assoc, hz,
        suzukiXiReflectionWeight_eq_quartic rho hza hzb]
      dsimp only [p, d]
      simp only [map_mul]
      have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
      have hzb' : z - b ≠ 0 := sub_ne_zero.mpr hzb
      dsimp only [a, b] at hza' hzb' ⊢
      field_simp

/-- The literal current, including its existing central value, is smooth
at the selected node for every smoothing radius. -/
theorem contDiffAt_suzukiXiPlanarReflectionMassCurrent_node
    (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ContDiffAt ℝ ∞ (suzukiXiPlanarReflectionMassCurrent rho r c tau)
      (zetaSpectralCoordinate rho.1) := by
  obtain ⟨p, hp, _hp0, he⟩ :=
    exists_suzukiXiPlanarReflectionMassCurrent_node_factor rho r c tau him
  have hconj : ContDiffAt ℝ ∞ (fun z : ℂ =>
      starRingEnd ℂ (z - zetaSpectralCoordinate rho.1)) (zetaSpectralCoordinate rho.1) :=
    Complex.conjCLE.contDiff.contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const)
  exact (hconj.mul hp).congr_of_eventuallyEq he

/-- Both reflection nodes are removable for the exact current. This
global smoothness also includes every carrier pole and repeated xi zero. -/
theorem contDiff_suzukiXiPlanarReflectionMassCurrent
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) (c tau : ℝ) :
    ContDiff ℝ ∞ (suzukiXiPlanarReflectionMassCurrent rho r c tau) := by
  by_cases him : (zetaSpectralCoordinate rho.1).im = 0
  · have hab : starRingEnd ℂ (zetaSpectralCoordinate rho.1) = zetaSpectralCoordinate rho.1 := by
      apply Complex.ext
      · exact conj_re _
      · rw [conj_im, him, neg_zero]
    have he : suzukiXiPlanarReflectionMassCurrent rho r c tau = fun _ => 0 := by
      funext z
      simp [suzukiXiPlanarReflectionMassCurrent, suzukiXiReflectionWeight,
        suzukiXiReflectionCauchyDifference, hab]
    rw [he]
    exact contDiff_const
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases ha : z = zetaSpectralCoordinate rho.1
  · subst z
    exact contDiffAt_suzukiXiPlanarReflectionMassCurrent_node rho r c tau him
  by_cases hb : z = starRingEnd ℂ (zetaSpectralCoordinate rho.1)
  · subst z
    have hp := contDiffAt_suzukiXiPlanarReflectionMassCurrent_node rho.conjugatePartner r c tau
      (by simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, neg_ne_zero] using him)
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
      suzukiXiPlanarReflectionMassCurrent_conjugatePartner] using hp
  exact ((((analyticAt_suzukiXiReflectionWeight rho ha hb).contDiffAt.restrict_scalars ℝ).mul
    (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_suzukiXiNormalizedMass hr)).contDiffAt).mul
        (contDiff_suzukiXiSmoothCarrier hr).contDiffAt

/-- The first real differential is exactly conjugate-linear. Its
coefficient does not shrink when the smoothing radius increases. -/
theorem fderiv_suzukiXiPlanarReflectionMassCurrent_node
    (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) (v : ℂ) :
    fderiv ℝ (suzukiXiPlanarReflectionMassCurrent rho r c tau)
        (zetaSpectralCoordinate rho.1) v =
      (-suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 3) * starRingEnd ℂ v := by
  obtain ⟨p, hp, hp0, he⟩ :=
    exists_suzukiXiPlanarReflectionMassCurrent_node_factor rho r c tau him
  have hlin : HasFDerivAt (fun z : ℂ => starRingEnd ℂ (z - zetaSpectralCoordinate rho.1))
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (zetaSpectralCoordinate rho.1) := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using! Complex.conjCLE.hasFDerivAt.comp _
      ((hasFDerivAt_id (𝕜 := ℝ) (zetaSpectralCoordinate rho.1)).sub_const
        (zetaSpectralCoordinate rho.1))
  have hd := (hlin.mul (hp.differentiableAt (by simp)).hasFDerivAt).congr_of_eventuallyEq he
  rw [hd.fderiv]
  simp [hp0]

/-- The current's Cauchy--Green density has a nonzero node coefficient
with the original inverse cubed multiplicity, for every smoothing radius. -/
theorem complexCauchyGreenSource_suzukiXiPlanarReflectionMassCurrent_node
    (rho : NontrivialZetaZero) (r c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    complexCauchyGreenSource (suzukiXiPlanarReflectionMassCurrent rho r c tau)
        (zetaSpectralCoordinate rho.1) =
      -2 * I * suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 3 := by
  unfold complexCauchyGreenSource
  rw [fderiv_suzukiXiPlanarReflectionMassCurrent_node rho r c tau him,
    fderiv_suzukiXiPlanarReflectionMassCurrent_node rho r c tau him]
  simp only [map_one, mul_one, conj_I]
  ring

end
end RiemannGaussian
