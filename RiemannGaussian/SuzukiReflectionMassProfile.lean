/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassNodeChart

/-!
# The rescaled profile of the actual signed mass variation

At distance w/r from a selected xi node, the actual mass variation has
an explicit universal profile. The local analytic coefficient derivative
vanishes in this limit only after the exact node chart has retained it.
The profile keeps the full complex angular dependence and multiplicity.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

private lemma rescaled_chart_algebra {r : ℝ} (hr : r ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (g q : ℂ) (D : ℝ) :
    g*q*((2*(w/(r:ℂ)).re*normSq q+normSq (w/(r:ℂ))*D : ℝ) : ℂ) /
      ((w/(r:ℂ))*((1+r^2*normSq (w/(r:ℂ))*normSq q : ℝ) : ℂ)^3) =
    g*q*((2*w.re*normSq q+(normSq w/r)*D : ℝ) : ℂ) /
      (w*((1+normSq w*normSq q : ℝ) : ℂ)^3) := by
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [div_ofReal_re, normSq_div, normSq_ofReal, ofReal_add, ofReal_mul,
    ofReal_div, ofReal_pow, ofReal_ofNat, ofReal_one]
  field_simp

/-- The actual mass variation at distance w/r has an exact rescaled
limit at every noncentral w. All multiplicities are retained. -/
theorem tendsto_suzukiXiReflectionMassVariation_rescaled_node
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => suzukiXiPlanarReflectionMassVariation rho r c tau
      (zetaSpectralCoordinate rho.1+w/(r:ℂ))) atTop
      (𝓝 (-2*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1)*(w.re:ℂ) /
        ((analyticZetaZeroMultiplicity rho : ℂ)^3*w*
          ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^3))) := by
  obtain ⟨q, g, hq, hg, hq0, hg0, he⟩ :=
    exists_suzukiXiReflectionMassVariation_node_chart rho c tau him
  let a := zetaSpectralCoordinate rho.1
  let z := fun r : ℝ => a+w/(r:ℂ)
  let Q := fun v : ℂ => normSq (q v)
  let Qx := fun v : ℂ => fderiv ℝ Q v 1
  have hinv : Tendsto (fun r : ℝ => 1/r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hdiv : Tendsto (fun r : ℝ => w/(r:ℂ)) atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp hinv).const_mul w
    simpa only [Function.comp_def, ofReal_div, ofReal_one, ofReal_zero, mul_zero,
      one_div, div_eq_mul_inv, one_mul, ofReal_inv] using! h
  have hz : Tendsto z atTop (𝓝 a) := by simpa only [add_zero] using hdiv.const_add a
  have hzNE : Tendsto z atTop (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    change a+w/(r:ℂ) ≠ a
    have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    intro heq
    apply div_ne_zero hw hrC
    exact add_left_cancel (show a+w/(r:ℂ) = a+0 by simpa only [add_zero] using heq)
  have hQ : ContDiffAt ℝ ∞ Q a := by
    simpa only [Q, normSq_eq_norm_sq] using (hq.contDiffAt.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)
  have hQx : ContinuousAt Qx a :=
    (hQ.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hqz := hq.continuousAt.tendsto.comp hz
  have hgz := hg.continuousAt.tendsto.comp hz
  have hQz := hQ.continuousAt.tendsto.comp hz
  have hQxz := hQx.tendsto.comp hz
  have hsmall : Tendsto (fun r : ℝ => (normSq w/r)*Qx (z r)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using!
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun r : ℝ => normSq w/r) atTop (𝓝 0)).mul hQxz
  have hnum : Tendsto (fun r : ℝ => ((2*w.re*Q (z r)+(normSq w/r)*Qx (z r) : ℝ) : ℂ)) atTop
      (𝓝 ((2*w.re*Q a : ℝ) : ℂ)) := by
    have ht := (hQz.const_mul (2*w.re)).add hsmall
    simp only [add_zero] at ht
    simpa only [Function.comp_def] using! (Complex.continuous_ofReal.tendsto _).comp ht
  have hden : Tendsto (fun r : ℝ => ((1+normSq w*Q (z r) : ℝ) : ℂ)) atTop
      (𝓝 ((1+normSq w*Q a : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((hQz.const_mul (normSq w)).const_add 1)
  have hd0 : ((1+normSq w*Q a : ℝ) : ℂ) ≠ 0 := by
    have hp : 0 < 1+normSq w*Q a := by
      have hw0 := normSq_nonneg w
      have hqa := normSq_nonneg (q a)
      dsimp only [Q]
      positivity
    exact_mod_cast hp.ne'
  have ht := ((hgz.mul hqz).mul hnum).div ((hden.pow 3).const_mul w)
    (mul_ne_zero hw (pow_ne_zero 3 hd0))
  have hlim : g a*q a*((2*w.re*Q a : ℝ) : ℂ) /
      (w*((1+normSq w*Q a : ℝ) : ℂ)^3) =
      -2*suzukiSmoothSpectralBoundaryHeat c tau a*(w.re:ℂ) /
        ((analyticZetaZeroMultiplicity rho : ℂ)^3*w*
          ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^3) := by
    have hm : (analyticZetaZeroMultiplicity rho : ℝ) ≠ 0 := by
      exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
    have hmC : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by exact_mod_cast hm
    dsimp only [Q, a]
    rw [hq0, hg0]
    simp only [map_inv₀, normSq_natCast, ofReal_mul, ofReal_inv, ofReal_natCast,
      ofReal_add, ofReal_div, ofReal_one, ofReal_pow, ofReal_ofNat]
    field_simp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [hzNE.eventually he, eventually_gt_atTop (0 : ℝ)] with r her hr
  rw [her r]
  have hza : z r-a = w/(r:ℂ) := by dsimp [z]; ring
  change _ = g (z r)*q (z r)*
    ((2*(z r-a).re*normSq (q (z r))+normSq (z r-a)*Qx (z r) : ℝ) : ℂ) /
      ((z r-a)*((1+r^2*normSq (z r-a)*normSq (q (z r)) : ℝ) : ℂ)^3)
  rw [hza, rescaled_chart_algebra hr.ne' hw]
  rfl

/-- The rescaled signed density retains a constant angular component
as well as the second harmonic. This is the actual xi-field limit,
not an assertion that the variable local coefficients are constant. -/
theorem tendsto_suzukiXiReflectionMassVariation_angular_profile
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => -4*I*suzukiXiPlanarReflectionMassVariation rho r c tau
      (zetaSpectralCoordinate rho.1+w/(r:ℂ))) atTop
      (𝓝 ((4*I*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
        (analyticZetaZeroMultiplicity rho : ℂ)^3) * (1+starRingEnd ℂ w/w) /
          ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^3)) := by
  have h := (tendsto_suzukiXiReflectionMassVariation_rescaled_node rho c tau him hw).const_mul (-4*I)
  convert h using 1
  rw [Complex.re_eq_add_conj]
  field_simp

/-- Exchanging the two reflection nodes preserves the complete signed
mass variation, including the original horizontal mass derivative. -/
theorem suzukiXiPlanarReflectionMassVariation_conjugatePartner
    (rho : NontrivialZetaZero) (r c tau : ℝ) :
    suzukiXiPlanarReflectionMassVariation rho.conjugatePartner r c tau =
      suzukiXiPlanarReflectionMassVariation rho r c tau := by
  funext z
  simp only [suzukiXiPlanarReflectionMassVariation, suzukiXiReflectionMassVariation,
    suzukiXiHorizontalReflectionHeat, suzukiXiReflectionWeight_conjugatePartner]

/-- Every hypothetical right-half zero has this same complete angular
profile at its upper reflected node. The inverse-cubed multiplicity and
positive Gaussian source weight are kept in the complex limit. -/
theorem tendsto_suzukiXiReflectionMassVariation_reflected_profile
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => -4*I*suzukiXiPlanarReflectionMassVariation rho r c tau
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+w/(r:ℂ))) atTop
      (𝓝 ((4*I*suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) /
        (analyticZetaZeroMultiplicity rho : ℂ)^3) * (1+starRingEnd ℂ w/w) /
          ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^3)) := by
  have him : (zetaSpectralCoordinate rho.conjugatePartner.1).im ≠ 0 := by
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, zetaSpectralCoordinate_im]
    linarith
  simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    analyticZetaZeroMultiplicity_conjugatePartner, suzukiXiPlanarReflectionMassVariation_conjugatePartner] using
      tendsto_suzukiXiReflectionMassVariation_angular_profile rho.conjugatePartner c tau him hw

/-- Coupling two perpendicular rescaled directions cancels the second
harmonic but leaves twice the constant angular component. The limit is
for the actual pair of signed mass-variation values. -/
theorem tendsto_suzukiXiReflectionMassVariation_quarter_turn_pair
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => -4*I*(
      suzukiXiPlanarReflectionMassVariation rho r c tau
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+w/(r:ℂ)) +
      suzukiXiPlanarReflectionMassVariation rho r c tau
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(I*w)/(r:ℂ)))) atTop
      (𝓝 (8*I*suzukiSmoothSpectralBoundaryHeat c tau (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) /
        ((analyticZetaZeroMultiplicity rho : ℂ)^3*
          ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^3))) := by
  have h1 := tendsto_suzukiXiReflectionMassVariation_reflected_profile rho hzero c tau hw
  have h2 := tendsto_suzukiXiReflectionMassVariation_reflected_profile rho hzero c tau (mul_ne_zero I_ne_zero hw)
  have h := h1.add h2
  simp only [map_mul, normSq_I, one_mul, conj_I] at h
  convert h using 1
  · funext r
    ring
  · congr 1
    field_simp
    ring

end
end RiemannGaussian
