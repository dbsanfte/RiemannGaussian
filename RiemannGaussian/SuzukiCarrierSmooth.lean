/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexSmoothQuotient
import RiemannGaussian.SuzukiCarrierProjectedStrip

/-!
# Globally smooth regularization of the actual Suzuki carrier

The homogeneous formula uses the actual entire xi numerator and full
denominator. It is smooth across every genuine carrier pole, and the
existing local xi model also proves smoothness at their common zeros.
Its explicit signed Cauchy--Green source retains the full Wronskian.
This source is not dropped or assumed to have a favorable sign.
-/

open Complex Filter Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- Homogeneous regularization using both original entire factors.
Common zeros are assigned the value justified by the local model below. -/
def suzukiXiSmoothCarrier (r : ℝ) (z : ℂ) : ℂ :=
  complexSmoothQuotient r (I * riemannXiSpectral z) (suzukiXiEValue z)

/-- The full signed area source, keeping the entire Wronskian and its
phase. At common zeros its zero value is justified below. -/
def suzukiXiSmoothCarrierSource (r : ℝ) (z : ℂ) : ℂ :=
  2 * (r : ℂ) ^ 2 * riemannXiSpectral z ^ 2 *
    starRingEnd ℂ (deriv riemannXiSpectral z * suzukiXiEValue z -
      riemannXiSpectral z * deriv suzukiXiEValue z) /
      ((normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) ^ 2

/-- A genuine original denominator zero has regularized value zero;
this does not assert that the original meromorphic carrier is finite. -/
theorem suzukiXiSmoothCarrier_eq_zero_of_E_zero (r : ℝ) {z : ℂ} (hz : suzukiXiEValue z = 0) :
    suzukiXiSmoothCarrier r z = 0 := by
  rw [suzukiXiSmoothCarrier, hz, complexSmoothQuotient_zero_right]

/-- The value at every xi zero, including a shared multiple zero, is zero. -/
theorem suzukiXiSmoothCarrier_eq_zero_of_xi_zero (r : ℝ) {z : ℂ} (hz : riemannXiSpectral z = 0) :
    suzukiXiSmoothCarrier r z = 0 := by simp [suzukiXiSmoothCarrier, hz]

/-- Global boundedness has no exception at either zero divisor. -/
theorem norm_suzukiXiSmoothCarrier_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖suzukiXiSmoothCarrier r z‖ ≤ 1 / (2 * r) :=
  norm_complexSmoothQuotient_le hr _ _

/-- On the original regular domain the exact radial formula retains
the full complex carrier value. -/
theorem suzukiXiSmoothCarrier_eq_regular_chart (r : ℝ) {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiSmoothCarrier r z = complexSmoothQuotient r (suzukiXiZeroCarrier z) 1 := by
  rw [suzukiXiSmoothCarrier, complexSmoothQuotient_eq_div_chart r _ hE,
    ← suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]

/-- The usual bounded radial expression is used only where the
original denominator is genuinely nonzero. -/
theorem suzukiXiSmoothCarrier_eq_radial (r : ℝ) {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiSmoothCarrier r z = suzukiXiZeroCarrier z /
      ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ) := by
  rw [suzukiXiSmoothCarrier_eq_regular_chart r hE, complexSmoothQuotient_one_right]

/-- Every xi zero has an exact smooth local chart, with the original
analytic factor and inverse multiplicity retained. Unlike a punctured
quotient identity, this includes the central common-zero value. -/
theorem exists_suzukiXiSmoothCarrier_zero_chart (rho : NontrivialZetaZero) (r : ℝ) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      suzukiXiSmoothCarrier r =ᶠ[𝓝 (zetaSpectralCoordinate rho.1)]
        fun z => complexSmoothQuotient r ((z - zetaSpectralCoordinate rho.1) * q z) 1 := by
  obtain ⟨q, p, hq, _hp, hq0, _hp0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz
  by_cases hza : z = zetaSpectralCoordinate rho.1
  · subst z
    rw [suzukiXiSmoothCarrier_eq_zero_of_xi_zero r
      ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩)]
    simp
  · have hlocal := hz hza
    rw [suzukiXiSmoothCarrier_eq_regular_chart r hlocal.1, hlocal.2.2.1]

/-- The actual regularization is globally smooth. Genuine poles of
every order and common xi zeros are both included in the proof. -/
theorem contDiff_suzukiXiSmoothCarrier {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (suzukiXiSmoothCarrier r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hA : riemannXiSpectral z = 0
  · obtain ⟨rho, rfl⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mp hA
    obtain ⟨q, hq, _hq0, he⟩ := exists_suzukiXiSmoothCarrier_zero_chart rho r
    have hc : ContDiffAt ℝ ∞ (fun z =>
        complexSmoothQuotient r ((z - zetaSpectralCoordinate rho.1) * q z) 1)
        (zetaSpectralCoordinate rho.1) :=
      contDiffAt_complexSmoothQuotient hr
        ((contDiffAt_id.sub contDiffAt_const).mul (hq.contDiffAt.restrict_scalars ℝ))
        contDiffAt_const (Or.inr one_ne_zero)
    exact hc.congr_of_eventuallyEq he
  · exact contDiffAt_complexSmoothQuotient hr
      (contDiffAt_const.mul ((analyticAt_riemannXiSpectral z).contDiffAt.restrict_scalars ℝ))
      ((analyticAt_suzukiXiEValue z).contDiffAt.restrict_scalars ℝ)
      (Or.inl (mul_ne_zero I_ne_zero hA))

/-- The unchanged carrier is recovered with its exact complex
complement on the original regular domain. -/
theorem suzukiXiZeroCarrier_eq_smooth_add_complement (r : ℝ) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z = suzukiXiSmoothCarrier r z + (r : ℂ) ^ 2 *
      suzukiXiZeroCarrier z ^ 2 * starRingEnd ℂ (suzukiXiSmoothCarrier r z) := by
  rw [suzukiXiSmoothCarrier_eq_regular_chart r hE]
  exact (complexSmoothQuotient_radial_identity r _).symm

/-- The diagonal xi source has the original coefficient `1/m` after
smoothing, and its complete remainder is real-smooth at the zero.
No zero simplicity or omitted common-zero value is assumed. -/
theorem exists_suzukiXiSmoothCarrier_source_model (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) :
    ∃ p : ℂ → ℂ, ContDiffAt ℝ ∞ p (zetaSpectralCoordinate rho.1) ∧
      ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
        suzukiXiSmoothCarrier r z / (z - zetaSpectralCoordinate rho.1) ^ 2 =
          (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ / (z - zetaSpectralCoordinate rho.1) + p z := by
  obtain ⟨q, hq, hq0, he⟩ := exists_suzukiXiSmoothCarrier_zero_chart rho r
  let a := zetaSpectralCoordinate rho.1
  let p := fun z => dslope q a z - (r : ℂ) ^ 2 * q z ^ 2 * starRingEnd ℂ (suzukiXiSmoothCarrier r z)
  have hp : ContDiffAt ℝ ∞ p a :=
    ((analyticAt_dslope_of_analyticAt hq hq).contDiffAt.restrict_scalars ℝ).sub
      ((contDiffAt_const.mul ((hq.contDiffAt.restrict_scalars ℝ).pow 2)).mul
        (Complex.conjCLE.contDiff.contDiffAt.comp a (contDiff_suzukiXiSmoothCarrier hr).contDiffAt))
  refine ⟨p, hp, ?_⟩
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hrad := complexSmoothQuotient_radial_identity r ((z - a) * q z)
  rw [← hz] at hrad
  change suzukiXiSmoothCarrier r z / (z - a) ^ 2 = _
  rw [← hq0]
  dsimp only [p]
  rw [dslope_of_ne q hza, slope_def_field]
  change _ = q a / (z - a) + ((q z - q a) / (z - a) - _)
  field_simp
  linear_combination hrad

private lemma source_at_xi_zero {r : ℝ} (hr : 0 < r) {z : ℂ} (hA : riemannXiSpectral z = 0) :
    complexCauchyGreenSource (suzukiXiSmoothCarrier r) z = 0 := by
  obtain ⟨rho, rfl⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mp hA
  obtain ⟨q, hq, _hq0, he⟩ := exists_suzukiXiSmoothCarrier_zero_chart rho r
  have hf : DifferentiableAt ℂ (fun z => (z - zetaSpectralCoordinate rho.1) * q z)
      (zetaSpectralCoordinate rho.1) :=
    (differentiableAt_id.sub_const _).mul hq.differentiableAt
  have hsource := complexCauchyGreenSource_complexSmoothQuotient hr hf
    (differentiableAt_const (1 : ℂ)) (Or.inr one_ne_zero)
  have heq : complexCauchyGreenSource (suzukiXiSmoothCarrier r) (zetaSpectralCoordinate rho.1) =
      complexCauchyGreenSource (fun z => complexSmoothQuotient r
        ((z - zetaSpectralCoordinate rho.1) * q z) 1) (zetaSpectralCoordinate rho.1) := by
    unfold complexCauchyGreenSource
    rw [he.fderiv_eq]
  rw [heq, hsource]
  simp

/-- The globally valid Cauchy--Green source is exactly the displayed
Wronskian formula, including all original poles and common zeros. -/
theorem complexCauchyGreenSource_suzukiXiSmoothCarrier {r : ℝ} (hr : 0 < r) (z : ℂ) :
    complexCauchyGreenSource (suzukiXiSmoothCarrier r) z = suzukiXiSmoothCarrierSource r z := by
  by_cases hA : riemannXiSpectral z = 0
  · rw [source_at_xi_zero hr hA]
    simp [suzukiXiSmoothCarrierSource, hA]
  · have hf := (analyticAt_riemannXiSpectral z).differentiableAt.hasDerivAt.const_mul I
    have hg := (analyticAt_suzukiXiEValue z).differentiableAt
    change complexCauchyGreenSource (fun w => complexSmoothQuotient r
      (I * riemannXiSpectral w) (suzukiXiEValue w)) z = _
    rw [complexCauchyGreenSource_complexSmoothQuotient hr hf.differentiableAt hg
      (Or.inl (mul_ne_zero I_ne_zero hA)), hf.deriv]
    unfold suzukiXiSmoothCarrierSource
    simp only [map_mul, map_sub, Complex.conj_I, normSq_I, one_mul, mul_pow, I_sq]
    congr 1
    ring_nf
    simp only [I_sq]
    ring

/-- The explicit signed source is continuous everywhere; apparent
common-zero divisions have been discharged by the local xi model. -/
theorem continuous_suzukiXiSmoothCarrierSource {r : ℝ} (hr : 0 < r) :
    Continuous (suzukiXiSmoothCarrierSource r) := by
  have hf := (contDiff_suzukiXiSmoothCarrier hr).continuous_fderiv (by simp)
  have hsource : suzukiXiSmoothCarrierSource r = fun z =>
      I * fderiv ℝ (suzukiXiSmoothCarrier r) z 1 - fderiv ℝ (suzukiXiSmoothCarrier r) z I := by
    funext z
    rw [← complexCauchyGreenSource_suzukiXiSmoothCarrier hr]
    rfl
  rw [hsource]
  fun_prop

/-- Removing smoothing recovers the original carrier pointwise on its
regular domain. This is not an interchange with an area or pole sum. -/
theorem tendsto_suzukiXiSmoothCarrier_zero_radius {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    Tendsto (fun r : ℝ => suzukiXiSmoothCarrier r z) (𝓝 0) (𝓝 (suzukiXiZeroCarrier z)) := by
  have hd : ContinuousAt (fun r : ℝ => ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ)) 0 := by
    fun_prop
  have hc : ContinuousAt (fun r : ℝ => suzukiXiZeroCarrier z /
      ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ)) 0 :=
    continuousAt_const.div hd (by norm_num)
  have he : (fun r : ℝ => suzukiXiSmoothCarrier r z) =
      fun r : ℝ => suzukiXiZeroCarrier z / ((1 + r ^ 2 * normSq (suzukiXiZeroCarrier z) : ℝ) : ℂ) :=
    funext (fun r => suzukiXiSmoothCarrier_eq_radial r hE)
  rw [he]
  simpa using hc.tendsto

/-- Away from the original denominator zeros, the area source tends
pointwise to zero. No uniform domination near poles is concluded. -/
theorem tendsto_suzukiXiSmoothCarrierSource_zero_radius {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    Tendsto (fun r : ℝ => suzukiXiSmoothCarrierSource r z) (𝓝 0) (𝓝 0) := by
  have hns : ((normSq (suzukiXiEValue z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (normSq_pos.mpr hE).ne'
  have hd : (((normSq (suzukiXiEValue z) + (0 : ℝ) ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) ^ 2) ≠ 0 := by
    simpa using pow_ne_zero 2 hns
  have hc : ContinuousAt (fun r : ℝ => suzukiXiSmoothCarrierSource r z) 0 := by
    unfold suzukiXiSmoothCarrierSource
    exact (by fun_prop : ContinuousAt (fun r : ℝ => 2 * (r : ℂ) ^ 2 * riemannXiSpectral z ^ 2 *
      starRingEnd ℂ (deriv riemannXiSpectral z * suzukiXiEValue z -
        riemannXiSpectral z * deriv suzukiXiEValue z)) 0).div (by fun_prop) hd
  convert hc.tendsto using 1
  simp [suzukiXiSmoothCarrierSource]

/-- At an actual carrier pole the source instead retains its exact
inverse-square parameter scale and the full complex derivative ratio.
Higher-order poles are included; their central derivative may vanish. -/
theorem suzukiXiSmoothCarrierSource_at_genuine_pole {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    suzukiXiSmoothCarrierSource r z =
      -2 / (r : ℂ) ^ 2 * starRingEnd ℂ (deriv suzukiXiEValue z / riemannXiSpectral z) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hAc : starRingEnd ℂ (riemannXiSpectral z) ≠ 0 := by simpa using hA
  unfold suzukiXiSmoothCarrierSource
  rw [hE]
  simp only [normSq_zero, zero_add, mul_zero, zero_sub, map_neg, map_mul, map_div₀,
    ofReal_mul, ofReal_pow]
  rw [← mul_conj (riemannXiSpectral z)]
  field_simp

end
end RiemannGaussian
