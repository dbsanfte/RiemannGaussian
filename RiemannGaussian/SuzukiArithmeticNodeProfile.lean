/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionMassProfile
import RiemannGaussian.SuzukiGammaNormalizedGaussianDecay

/-!
# The actual weighted arithmetic source at a reflected zero

The uniform analytic node chart retains the variable carrier coefficient,
its derivative, and the first differentiated Gamma correction. The latter
enters quadratically in displacement. After rescaling, the full complex
arithmetic source has a radial leading profile with its original signed
Gaussian value and multiplicity. No angular channel is discarded.
-/

open Complex Filter Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

private lemma source_of_uniform_chart {a : ℂ} {q : ℂ → ℂ}
    (hq : AnalyticAt ℂ q a)
    (he : ∀ᶠ z in 𝓝 a, ∀ r : ℝ, suzukiXiSmoothCarrier r z =
      ((z-a)*q z) / ((1+r^2*normSq ((z-a)*q z) : ℝ) : ℂ)) :
    ∀ᶠ z in 𝓝 a, ∀ r : ℝ, 0 < r → suzukiXiSmoothCarrierSource r z =
      -2*I*(r:ℂ)^2*((z-a)*q z)^2*starRingEnd ℂ (q z+(z-a)*deriv q z) /
        ((1+r^2*normSq ((z-a)*q z) : ℝ) : ℂ)^2 := by
  filter_upwards [eventually_eventually_nhds.mpr he, hq.eventually_analyticAt] with z hz hqz r hr
  have hf : HasDerivAt (fun w => (w-a)*q w) (q z+(z-a)*deriv q z) z := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id z).sub_const a).fun_mul hqz.differentiableAt.hasDerivAt
  have hfield : suzukiXiSmoothCarrier r =ᶠ[𝓝 z]
      fun w => complexSmoothQuotient r ((w-a)*q w) 1 := by
    filter_upwards [hz] with w hw
    rw [hw r, complexSmoothQuotient_one_right]
  have heq : complexCauchyGreenSource (suzukiXiSmoothCarrier r) z =
      complexCauchyGreenSource (fun w => complexSmoothQuotient r ((w-a)*q w) 1) z := by
    unfold complexCauchyGreenSource
    rw [hfield.fderiv_eq]
  rw [← complexCauchyGreenSource_suzukiXiSmoothCarrier hr, heq,
    complexCauchyGreenSource_complexSmoothQuotient hr hf.differentiableAt
      (differentiableAt_const (1:ℂ)) (Or.inr one_ne_zero), hf.deriv]
  simp only [deriv_const, mul_zero, one_mul, zero_sub, map_neg, normSq_one]
  ring

/-- The actual weighted arithmetic source has one uniform node chart.
It keeps the analytic coefficient derivative and the exact Gamma term,
whose displacement factor is quadratic. Every zero multiplicity is included. -/
theorem exists_suzukiGammaShiftWeightedArithmeticSource_node_chart
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ (q g : ℂ → ℂ), AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      ContDiffAt ℝ ∞ g (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      g (zetaSpectralCoordinate rho.1) = -suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) ∧
      ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ, 0 < r →
        suzukiGammaShiftWeightedArithmeticSource rho r c tau z =
          -2*I*(r:ℂ)^2*g z*q z^2 * starRingEnd ℂ
            (q z+(z-zetaSpectralCoordinate rho.1)*deriv q z -
              (z-zetaSpectralCoordinate rho.1)^2*q z^2*
                deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)) /
            ((1+r^2*normSq (z-zetaSpectralCoordinate rho.1)*normSq (q z) : ℝ) : ℂ)^2 := by
  let a := zetaSpectralCoordinate rho.1
  obtain ⟨q, hq, hq0, he⟩ := exists_suzukiXiMass_and_carrier_uniform_chart rho
  obtain ⟨g, hg, hg0, heg⟩ := exists_suzukiXiReflectionHeat_node_numerator rho c tau him
  have hV := source_of_uniform_chart hq (he.mono fun z hz r => (hz r).2)
  have hs0 : 0 < (suzukiArithmeticZetaArgument a).re := by
    rw [suzukiArithmeticZetaArgument_re, zetaSpectralCoordinate_im]
    have hh := rho.re_lt_one
    linarith
  have hs : ∀ᶠ z in 𝓝 a, 0 < (suzukiArithmeticZetaArgument z).re := by
    apply (show ContinuousAt (fun z => (suzukiArithmeticZetaArgument z).re) a by
      unfold suzukiArithmeticZetaArgument
      fun_prop).eventually
    exact lt_mem_nhds hs0
  refine ⟨q, g, hq, hg, hq0, hg0, ?_⟩
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, hV.filter_mono nhdsWithin_le_nhds,
    heg, hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfields hv hweight hsz hza r hr
  have hsplit := suzukiXiSmoothCarrierSource_eq_gammaShift hr hsz
  rw [suzukiGammaShiftSpectralSource_eq_add hsz, suzukiGammaShiftCompletionSource_eq_mass,
    ← suzukiXiNormalizedMass_eq_gammaShift r hsz] at hsplit
  have heq : suzukiGammaShiftArithmeticSource r (suzukiArithmeticZetaArgument z) =
      suzukiXiSmoothCarrierSource r z + 2*I*(r:ℂ)^2*(suzukiXiNormalizedMass r z:ℂ)^2*
        starRingEnd ℂ (deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument z)) := by
    linear_combination -hsplit
  unfold suzukiGammaShiftWeightedArithmeticSource
  rw [heq, hweight, hv r hr, (hfields r).1]
  simp only [map_mul, ofReal_div, ofReal_mul, ofReal_add, ofReal_pow, ofReal_one,
    map_sub, map_add, map_pow]
  rw [← mul_conj (z-zetaSpectralCoordinate rho.1), ← mul_conj (q z)]
  simp only [map_sub]
  have hza0 : z-a ≠ 0 := sub_ne_zero.mpr hza
  dsimp only [a] at *
  field_simp
  ring

/-- The radial leading profile of the actual weighted arithmetic
source near a selected node. Its Gaussian sign and multiplicity remain explicit. -/
def suzukiGammaArithmeticNodeProfile (rho : NontrivialZetaZero) (c tau : ℝ) (w : ℂ) : ℂ :=
  2*I*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
    ((analyticZetaZeroMultiplicity rho : ℂ)^3 *
      ((1+normSq w/(analyticZetaZeroMultiplicity rho : ℝ)^2 : ℝ) : ℂ)^2)

private lemma approach_node {w : ℂ} (hw : w ≠ 0) (a : ℂ) :
    Tendsto (fun r : ℝ => a+w/(r:ℂ)) atTop (𝓝[≠] a) := by
  have hinv : Tendsto (fun r : ℝ => 1/r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hdiv : Tendsto (fun r : ℝ => w/(r:ℂ)) atTop (𝓝 0) := by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp hinv).const_mul w
    simpa only [Function.comp_def, ofReal_div, ofReal_one, ofReal_zero, mul_zero,
      one_div, div_eq_mul_inv, one_mul, ofReal_inv] using! h
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨by simpa only [add_zero] using hdiv.const_add a, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  change a+w/(r:ℂ) ≠ a
  intro he
  apply div_ne_zero hw hrC
  exact add_left_cancel (show a+w/(r:ℂ) = a+0 by simpa only [add_zero] using he)

private lemma exists_radial_model
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) (w : ℂ) :
    ∃ f : ℂ → ℂ, ContinuousAt f (zetaSpectralCoordinate rho.1) ∧
      f (zetaSpectralCoordinate rho.1) = suzukiGammaArithmeticNodeProfile rho c tau w ∧
      ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ, 0 < r →
        r^2*normSq (z-zetaSpectralCoordinate rho.1) = normSq w →
        suzukiGammaShiftWeightedArithmeticSource rho r c tau z/(r:ℂ)^2 = f z := by
  obtain ⟨q, g, hq, hg, hq0, hg0, he⟩ :=
    exists_suzukiGammaShiftWeightedArithmeticSource_node_chart rho c tau him
  let a := zetaSpectralCoordinate rho.1
  let k := fun v : ℂ => q v+(v-a)*deriv q v - (v-a)^2*q v^2*
    deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument v)
  have hs0 : 0 < (suzukiArithmeticZetaArgument a).re := by
    rw [suzukiArithmeticZetaArgument_re, zetaSpectralCoordinate_im]
    have hh := rho.re_lt_one
    linarith
  have hQ : ContinuousAt (fun v => deriv suzukiGammaShiftCorrection (suzukiArithmeticZetaArgument v)) a :=
    (analyticAt_suzukiGammaShiftCorrection hs0).deriv.continuousAt.comp (by
      unfold suzukiArithmeticZetaArgument
      fun_prop)
  have hk : ContinuousAt k a :=
    (hq.continuousAt.add ((continuousAt_id.sub continuousAt_const).mul hq.deriv.continuousAt)).sub
      ((((continuousAt_id.sub continuousAt_const).pow 2).mul (hq.continuousAt.pow 2)).mul hQ)
  have hk0 : k a = q a := by simp [k]
  have hnorm : ContinuousAt (fun v => normSq (q v)) a := by
    simpa only [normSq_eq_norm_sq, a] using! hq.continuousAt.norm.pow 2
  let f := fun v : ℂ => -2*I*g v*q v^2*starRingEnd ℂ (k v) /
    ((1+normSq w*normSq (q v) : ℝ) : ℂ)^2
  have hp : 0 < 1+normSq w*normSq (q a) := by positivity [normSq_nonneg w, normSq_nonneg (q a)]
  have hd : ((1+normSq w*normSq (q a) : ℝ) : ℂ)^2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast hp.ne')
  have hf : ContinuousAt f a :=
    (((continuousAt_const.mul hg.continuousAt).mul (hq.continuousAt.pow 2)).mul
      (Complex.continuous_conj.continuousAt.comp hk)).div
        ((Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_const.add (continuousAt_const.mul hnorm))).pow 2) hd
  have hvalue : f a = suzukiGammaArithmeticNodeProfile rho c tau w := by
    dsimp only [f]
    rw [hk0, hq0, hg0]
    unfold suzukiGammaArithmeticNodeProfile
    simp only [map_inv₀, conj_natCast, normSq_natCast, ofReal_add, ofReal_mul,
      ofReal_inv, ofReal_pow, ofReal_natCast, ofReal_div, ofReal_one]
    field_simp
  refine ⟨f, hf, hvalue, ?_⟩
  filter_upwards [he] with z her r hr hrad
  rw [her r hr]
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hnormr : r^2*normSq (z-a)*normSq (q z) = normSq w*normSq (q z) :=
    congrArg (fun t => t*normSq (q z)) hrad
  change (-2*I*(r:ℂ)^2*g z*q z^2*starRingEnd ℂ (k z) /
    ((1+r^2*normSq (z-a)*normSq (q z) : ℝ) : ℂ)^2)/(r:ℂ)^2 = f z
  rw [hnormr]
  dsimp only [f]
  field_simp

/-- The complete normalized arithmetic density, with its original
complex reflection weight, has a radial rescaled limit at every
noncentral displacement. The local coefficient derivative and Gamma
correction vanish only after their exact chart terms have been retained. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_rescaled_node
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => suzukiGammaShiftWeightedArithmeticSource rho r c tau
      (zetaSpectralCoordinate rho.1+w/(r:ℂ))/(r:ℂ)^2) atTop
        (𝓝 (suzukiGammaArithmeticNodeProfile rho c tau w)) := by
  obtain ⟨f, hf, hvalue, he⟩ := exists_radial_model rho c tau him w
  have hzNE := approach_node hw (zetaSpectralCoordinate rho.1)
  have ht := hf.tendsto.comp (hzNE.mono_right nhdsWithin_le_nhds)
  rw [hvalue] at ht
  apply ht.congr'
  filter_upwards [hzNE.eventually he, eventually_gt_atTop (0 : ℝ)] with r her hr
  apply (her r hr ?_).symm
  simp only [add_sub_cancel_left, normSq_div, normSq_ofReal]
  field_simp

/-- One smoothing threshold controls every angular direction at the
same rescaled radius. The error is for the full complex arithmetic
source with the singular reflection weight retained. -/
theorem eventually_uniform_suzukiGammaShiftWeightedArithmeticSource_node_profile
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) {w : ℂ} (hw : w ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℝ in atTop, ∀ u : ℂ, normSq u = 1 →
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau
        (zetaSpectralCoordinate rho.1+(u*w)/(r:ℂ))/(r:ℂ)^2 -
          suzukiGammaArithmeticNodeProfile rho c tau w‖ < epsilon := by
  obtain ⟨f, hf, hvalue, he⟩ := exists_radial_model rho c tau him w
  let a := zetaSpectralCoordinate rho.1
  have hb : ∀ᶠ z in 𝓝 a, ‖f z-suzukiGammaArithmeticNodeProfile rho c tau w‖ < epsilon := by
    have hcont := (hf.sub_const (suzukiGammaArithmeticNodeProfile rho c tau w)).norm
    have hv : ‖f a-suzukiGammaArithmeticNodeProfile rho c tau w‖ < epsilon := by
      rw [hvalue, sub_self, norm_zero]
      exact hepsilon
    exact hcont.eventually (gt_mem_nhds hv)
  obtain ⟨delta, hdelta, hlocal⟩ := Metric.eventually_nhds_iff.mp
    ((eventually_nhdsWithin_iff.mp he).and hb)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (‖w‖/delta)] with r hr hlarge
  intro u hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, normSq_zero] at hu
    exact zero_ne_one hu
  have hun : ‖u‖ = 1 := by
    rw [normSq_eq_norm_sq] at hu
    nlinarith [norm_nonneg u]
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hd : dist (a+(u*w)/(r:ℂ)) a < delta := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_div, norm_mul, hun,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    apply (div_lt_iff₀ hr).mpr
    have hh := (div_lt_iff₀ hdelta).mp hlarge
    nlinarith
  obtain ⟨hmodel, hsmall⟩ := hlocal hd
  have hne : a+(u*w)/(r:ℂ) ≠ a := by
    intro h
    exact div_ne_zero (mul_ne_zero hu0 hw) hrC (add_left_cancel
      (show a+(u*w)/(r:ℂ) = a+0 by simpa only [add_zero] using h))
  have hrad : r^2*normSq (a+(u*w)/(r:ℂ)-a) = normSq w := by
    simp only [add_sub_cancel_left, normSq_div, map_mul, hu, one_mul, normSq_ofReal]
    field_simp
  rw [hmodel hne r hr hrad]
  exact hsmall

/-- Exchanging the two selected nodes leaves the entire weighted
arithmetic source unchanged, before any projection or limit. -/
theorem suzukiGammaShiftWeightedArithmeticSource_conjugatePartner
    (rho : NontrivialZetaZero) (r c tau : ℝ) :
    suzukiGammaShiftWeightedArithmeticSource rho.conjugatePartner r c tau =
      suzukiGammaShiftWeightedArithmeticSource rho r c tau := by
  funext z
  simp only [suzukiGammaShiftWeightedArithmeticSource, suzukiXiReflectionWeight_conjugatePartner]

/-- Every hypothetical right-half zero has this radial leading
profile at its upper reflected node, with the full complex weight present. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_reflected_profile
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => suzukiGammaShiftWeightedArithmeticSource rho r c tau
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+w/(r:ℂ))/(r:ℂ)^2) atTop
        (𝓝 (suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w)) := by
  have him : (zetaSpectralCoordinate rho.conjugatePartner.1).im ≠ 0 := by
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, zetaSpectralCoordinate_im]
    linarith
  simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    suzukiGammaShiftWeightedArithmeticSource_conjugatePartner] using
      tendsto_suzukiGammaShiftWeightedArithmeticSource_rescaled_node rho.conjugatePartner c tau him hw

/-- Rotating the rescaled displacement by any unit complex phase
preserves the entire leading arithmetic profile, not just its norm. -/
theorem suzukiGammaArithmeticNodeProfile_mul_phase (rho : NontrivialZetaZero)
    (c tau : ℝ) {u : ℂ} (hu : normSq u = 1) (w : ℂ) :
    suzukiGammaArithmeticNodeProfile rho c tau (u*w) = suzukiGammaArithmeticNodeProfile rho c tau w := by
  simp only [suzukiGammaArithmeticNodeProfile, map_mul, hu, one_mul]

/-- The actual reflected arithmetic core converges uniformly over all
angles at the fixed nonzero rescaled radius. This supplies one threshold
for phase families whose size and directions can vary with smoothing. -/
theorem eventually_uniform_suzukiGammaShiftWeightedArithmeticSource_reflected_profile
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) {w : ℂ} (hw : w ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℝ in atTop, ∀ u : ℂ, normSq u = 1 →
      ‖suzukiGammaShiftWeightedArithmeticSource rho r c tau
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(u*w)/(r:ℂ))/(r:ℂ)^2 -
          suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w‖ < epsilon := by
  have him : (zetaSpectralCoordinate rho.conjugatePartner.1).im ≠ 0 := by
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_im, zetaSpectralCoordinate_im]
    linarith
  simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    suzukiGammaShiftWeightedArithmeticSource_conjugatePartner] using
      eventually_uniform_suzukiGammaShiftWeightedArithmeticSource_node_profile
        rho.conjugatePartner c tau him hw hepsilon

/-- The radial profile at the upper reflected node has strictly
positive imaginary part. This retains the original Gaussian and all
zero multiplicities, without a simplicity hypothesis. -/
theorem suzukiGammaArithmeticNodeProfile_reflected_im_pos
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ) (w : ℂ) :
    0 < (suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w).im := by
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) :=
    Nat.cast_pos.mpr (analyticZetaZeroMultiplicity_positive rho)
  have hc : 0 < (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im := by
    rw [conj_im, zetaSpectralCoordinate_im]
    linarith
  unfold suzukiGammaArithmeticNodeProfile
  rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner, analyticZetaZeroMultiplicity_conjugatePartner,
    show (analyticZetaZeroMultiplicity rho : ℂ) = ((analyticZetaZeroMultiplicity rho : ℝ) : ℂ) by simp,
    ← ofReal_pow, ← ofReal_pow, ← ofReal_mul, div_ofReal_im, suzukiSmoothSpectralBoundaryHeat_eq]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, re_ofNat, im_ofNat, I_re, I_im,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  positivity [normSq_nonneg w]

/-- Every finite complex phase mixture has the same radial leading
source multiplied by the sum of its coefficients. Cross-phase data are
kept in the actual finite sum; the theorem does not assume positivity
or optimize a chosen coefficient family. -/
theorem tendsto_suzukiGammaShiftWeightedArithmeticSource_phase_sum
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ)
    {ι : Type*} (J : Finset ι) (v p : ι → ℂ) (hv : ∀ j ∈ J, normSq (v j) = 1)
    {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => ∑ j ∈ J, p j *
      (suzukiGammaShiftWeightedArithmeticSource rho r c tau
        (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(v j*w)/(r:ℂ))/(r:ℂ)^2)) atTop
          (𝓝 ((∑ j ∈ J, p j)*suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w)) := by
  have hv0 (j : ι) (hj : j ∈ J) : v j ≠ 0 := by
    intro he
    have hh := hv j hj
    rw [he, normSq_zero] at hh
    exact zero_ne_one hh
  have ht := tendsto_finsetSum J (fun j hj =>
    (tendsto_suzukiGammaShiftWeightedArithmeticSource_reflected_profile rho hzero c tau
      (mul_ne_zero (hv0 j hj) hw)).const_mul (p j))
  have hsum : (∑ j ∈ J, p j*suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau (v j*w)) =
      (∑ j ∈ J, p j)*suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [suzukiGammaArithmeticNodeProfile_mul_phase _ _ _ (hv j hj)]
  rwa [hsum] at ht

/-- No fixed finite phase mixture whose complex coefficients sum to
one removes the positive rescaled arithmetic core. This is a lower bound
on the actual mixture, not an independent ceiling for the RH argument. -/
theorem eventually_suzukiGammaShiftWeightedArithmeticSource_phase_sum_im_gt_half_profile
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ)
    {ι : Type*} (J : Finset ι) (v p : ι → ℂ) (hv : ∀ j ∈ J, normSq (v j) = 1)
    (hp : ∑ j ∈ J, p j = 1) {w : ℂ} (hw : w ≠ 0) :
    ∀ᶠ r : ℝ in atTop,
      (suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w).im/2 <
        (∑ j ∈ J, p j*(suzukiGammaShiftWeightedArithmeticSource rho r c tau
          (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(v j*w)/(r:ℂ))/(r:ℂ)^2)).im := by
  have ht := tendsto_suzukiGammaShiftWeightedArithmeticSource_phase_sum rho hzero c tau J v p hv hw
  rw [hp, one_mul] at ht
  have hi := Complex.continuous_im.continuousAt.tendsto.comp ht
  have hpos := suzukiGammaArithmeticNodeProfile_reflected_im_pos rho hzero c tau w
  exact hi.eventually (eventually_gt_nhds (by linarith))

/-- Even a growing number of phases and changing complex coefficients
cannot remove the positive core when their sum is one and their total
absolute weight is uniformly bounded. One threshold works for every such
finite mixture, with the full actual reflection weight retained. -/
theorem eventually_all_suzukiGammaShiftWeightedArithmeticSource_phase_mixtures_positive
    (rho : NontrivialZetaZero) (hzero : 1/2 < rho.1.re) (c tau : ℝ)
    {w : ℂ} (hw : w ≠ 0) {C : ℝ} (hC : 0 < C) {ι : Type*} :
    ∀ᶠ r : ℝ in atTop, ∀ (J : Finset ι) (v p : ι → ℂ),
      (∀ j ∈ J, normSq (v j) = 1) → (∑ j ∈ J, p j) = 1 → (∑ j ∈ J, ‖p j‖) ≤ C →
        (suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w).im/2 <
          (∑ j ∈ J, p j*(suzukiGammaShiftWeightedArithmeticSource rho r c tau
            (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(v j*w)/(r:ℂ))/(r:ℂ)^2)).im := by
  let L := suzukiGammaArithmeticNodeProfile rho.conjugatePartner c tau w
  have hL : 0 < L.im := suzukiGammaArithmeticNodeProfile_reflected_im_pos rho hzero c tau w
  let epsilon := L.im/(4*C)
  have hepsilon : 0 < epsilon := div_pos hL (by positivity)
  filter_upwards [eventually_uniform_suzukiGammaShiftWeightedArithmeticSource_reflected_profile
    rho hzero c tau hw hepsilon] with r hr
  intro J v p hv hp hnorm
  let V := fun j => suzukiGammaShiftWeightedArithmeticSource rho r c tau
    (starRingEnd ℂ (zetaSpectralCoordinate rho.1)+(v j*w)/(r:ℂ))/(r:ℂ)^2
  have heq : (∑ j ∈ J, p j*V j)-L = ∑ j ∈ J, p j*(V j-L) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  have hb : ‖(∑ j ∈ J, p j*V j)-L‖ ≤ L.im/4 := by
    rw [heq]
    calc
      _ ≤ ∑ j ∈ J, ‖p j*(V j-L)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, ‖p j‖*epsilon := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hr (v j) (hv j hj)).le (norm_nonneg _)
      _ = (∑ j ∈ J, ‖p j‖)*epsilon := (Finset.sum_mul J _ epsilon).symm
      _ ≤ C*epsilon := mul_le_mul_of_nonneg_right hnorm hepsilon.le
      _ = L.im/4 := by dsimp [epsilon]; field_simp
  have hi := (abs_le.mp ((Complex.abs_im_le_norm ((∑ j ∈ J, p j*V j)-L)).trans hb)).1
  simp only [sub_im] at hi
  change L.im/2 < (∑ j ∈ J, p j*V j).im
  linarith

end
end RiemannGaussian
