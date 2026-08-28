import RiemannGaussian.RiemannXiSuzukiCarrierHerglotzAnalytic
import Mathlib.MeasureTheory.Measure.ResolventTransform

/-!
# The finite Nevanlinna measure of Suzuki's xi carrier

The arithmetic carrier density itself is merely bounded and may have infinite
Lebesgue mass.  Dividing it by `1 + x^2` produces a finite positive measure.
This file constructs that measure and identifies the normalized carrier
Herglotz transform with an affine multiple of its standard finite-measure
resolvent transform.

No coefficient-tail decay, rigidity theorem, or RH conclusion is asserted
here.
-/

open Asymptotics Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The real Radon--Nikodym weight that turns the bounded carrier density into
a finite Nevanlinna measure. -/
def suzukiXiCarrierNevanlinnaWeight (x : ℝ) : ℝ :=
  suzukiXiRealAxisArithmeticCarrierDensity x / (1 + x ^ 2)

/-- The Nevanlinna weight is nonnegative pointwise. -/
theorem suzukiXiCarrierNevanlinnaWeight_nonneg (x : ℝ) :
    0 ≤ suzukiXiCarrierNevanlinnaWeight x := by
  unfold suzukiXiCarrierNevanlinnaWeight
  exact div_nonneg
    (suzukiXiRealAxisArithmeticCarrierDensity_nonneg x) (by positivity)

/-- The Nevanlinna weight is bounded by the standard Cauchy density. -/
theorem suzukiXiCarrierNevanlinnaWeight_le_inv_one_add_sq (x : ℝ) :
    suzukiXiCarrierNevanlinnaWeight x ≤ (1 + x ^ 2)⁻¹ := by
  unfold suzukiXiCarrierNevanlinnaWeight
  rw [div_eq_mul_inv]
  calc
    suzukiXiRealAxisArithmeticCarrierDensity x * (1 + x ^ 2)⁻¹ ≤
        1 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (suzukiXiRealAxisArithmeticCarrierDensity_le_one x) (by positivity)
    _ = (1 + x ^ 2)⁻¹ := one_mul _

/-- The Nevanlinna weight is Borel measurable. -/
theorem measurable_suzukiXiCarrierNevanlinnaWeight :
    Measurable suzukiXiCarrierNevanlinnaWeight := by
  unfold suzukiXiCarrierNevanlinnaWeight
  exact measurable_suzukiXiRealAxisArithmeticCarrierDensity.div
    (measurable_const.add (measurable_id.pow_const 2))

/-- The Nevanlinna weight has finite Lebesgue integral. -/
theorem integrable_suzukiXiCarrierNevanlinnaWeight :
    Integrable suzukiXiCarrierNevanlinnaWeight := by
  refine integrable_inv_one_add_sq.mono
    measurable_suzukiXiCarrierNevanlinnaWeight.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x ↦ by
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (suzukiXiCarrierNevanlinnaWeight_nonneg x),
      abs_of_nonneg (by positivity : 0 ≤ (1 + x ^ 2)⁻¹)]
    exact suzukiXiCarrierNevanlinnaWeight_le_inv_one_add_sq x

/-- The finite positive measure canonically associated to the arithmetic
carrier density. -/
def suzukiXiCarrierNevanlinnaMeasure : Measure ℝ :=
  volume.withDensity fun x ↦
    ENNReal.ofReal (suzukiXiCarrierNevanlinnaWeight x)

/-- The carrier Nevanlinna measure is finite, unconditionally. -/
instance isFiniteMeasure_suzukiXiCarrierNevanlinnaMeasure :
    IsFiniteMeasure suzukiXiCarrierNevanlinnaMeasure := by
  unfold suzukiXiCarrierNevanlinnaMeasure
  exact isFiniteMeasure_withDensity_ofReal
    integrable_suzukiXiCarrierNevanlinnaWeight.hasFiniteIntegral

/-- Integration against the carrier Nevanlinna measure is exactly weighted
Lebesgue integration by its real Radon--Nikodym density. -/
theorem integral_suzukiXiCarrierNevanlinnaMeasure_eq_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ x, g x ∂suzukiXiCarrierNevanlinnaMeasure =
      ∫ x, suzukiXiCarrierNevanlinnaWeight x • g x := by
  unfold suzukiXiCarrierNevanlinnaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by
      change (ENNReal.ofReal
        (suzukiXiCarrierNevanlinnaWeight x)).toReal • g x =
          suzukiXiCarrierNevanlinnaWeight x • g x
      rw [ENNReal.toReal_ofReal
        (suzukiXiCarrierNevanlinnaWeight_nonneg x)]
  · exact measurable_suzukiXiCarrierNevanlinnaWeight.ennreal_ofReal
  · exact Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top

/-- The real total mass of the carrier Nevanlinna measure is the ordinary
Lebesgue integral of its Radon--Nikodym weight. -/
theorem suzukiXiCarrierNevanlinnaMeasure_real_univ_eq :
    suzukiXiCarrierNevanlinnaMeasure.real univ =
      ∫ x : ℝ, suzukiXiCarrierNevanlinnaWeight x := by
  have h := integral_suzukiXiCarrierNevanlinnaMeasure_eq_smul
    (fun _ : ℝ ↦ (1 : ℝ))
  simpa [smul_eq_mul] using h

/-- The total carrier Nevanlinna mass is nonnegative. -/
theorem suzukiXiCarrierNevanlinnaMeasure_real_univ_nonneg :
    0 ≤ suzukiXiCarrierNevanlinnaMeasure.real univ := by
  rw [suzukiXiCarrierNevanlinnaMeasure_real_univ_eq]
  exact integral_nonneg suzukiXiCarrierNevanlinnaWeight_nonneg

/-- Spectral xi is nonzero at some real spectral coordinate.  The proof is
fully internal: if it vanished on the whole real axis, finite analytic order
at the putative zero `0` would isolate that zero, contradicting the nearby
real zeros. -/
theorem exists_real_riemannXiSpectral_ne_zero :
    ∃ x : ℝ, riemannXiSpectral (x : ℂ) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hzero : riemannXiSpectral (0 : ℂ) = 0 := by
    simpa using hnone 0
  obtain ⟨rho, hzeroCoord⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero (0 : ℂ)).mp hzero
  have hfinite : analyticOrderAt riemannXiSpectral (0 : ℂ) ≠ ⊤ := by
    rw [hzeroCoord,
      analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hpunctured : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      riemannXiSpectral z ≠ 0 :=
    (analyticAt_riemannXiSpectral (0 : ℂ)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun heq ↦ hfinite (analyticOrderAt_eq_top.mpr heq)
  rw [eventually_nhdsWithin_iff] at hpunctured
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hpunctured
  have hhalfPos : 0 < delta / 2 := by linarith
  have hhalfLt : |delta / 2| < delta := by
    rw [abs_of_pos hhalfPos]
    linarith
  have hhalfBall : ((delta / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) delta := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs] using
      hhalfLt
  have hhalfNe : ((delta / 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hhalfPos.ne'
  exact (hball hhalfBall hhalfNe) (hnone (delta / 2))

/-- Away from a real spectral-xi zero, the Nevanlinna weight is strictly
positive. -/
theorem suzukiXiCarrierNevanlinnaWeight_pos_of_xi_ne_zero
    {x : ℝ} (hxi : riemannXiSpectral (x : ℂ) ≠ 0) :
    0 < suzukiXiCarrierNevanlinnaWeight x := by
  have hE : suzukiXiEValue (x : ℂ) ≠ 0 := by
    intro hEzero
    exact hxi ((suzukiXiEValue_ofReal_eq_zero_iff x).mp hEzero).1
  have hxiRe : (riemannXiSpectral (x : ℂ)).re ≠ 0 := by
    intro hre
    apply hxi
    apply Complex.ext
    · simpa using hre
    · simpa using riemannXiSpectral_ofReal_im x
  have hdensity : 0 < suzukiXiRealAxisArithmeticCarrierDensity x := by
    unfold suzukiXiRealAxisArithmeticCarrierDensity
    rw [if_neg hE]
    exact div_pos (sq_pos_of_ne_zero hxiRe)
      (suzukiXiRealAxisSpectralEnergy_pos_of_E_ne_zero x hE)
  unfold suzukiXiCarrierNevanlinnaWeight
  exact div_pos hdensity (by positivity)

/-- The carrier Nevanlinna measure has strictly positive total mass. -/
theorem suzukiXiCarrierNevanlinnaMeasure_real_univ_pos :
    0 < suzukiXiCarrierNevanlinnaMeasure.real univ := by
  obtain ⟨x0, hx0⟩ := exists_real_riemannXiSpectral_ne_zero
  have hcontinuous : Continuous (fun x : ℝ ↦
      riemannXiSpectral (x : ℂ)) :=
    differentiable_riemannXiSpectral.continuous.comp
      Complex.continuous_ofReal
  have hnear : ∀ᶠ x : ℝ in 𝓝 x0,
      riemannXiSpectral (x : ℂ) ≠ 0 :=
    hcontinuous.continuousAt.eventually_ne hx0
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsubset : ball x0 delta ⊆
      Function.support suzukiXiCarrierNevanlinnaWeight := by
    intro x hx
    change suzukiXiCarrierNevanlinnaWeight x ≠ 0
    exact (suzukiXiCarrierNevanlinnaWeight_pos_of_xi_ne_zero
      (hball hx)).ne'
  have hballMeasure : 0 < volume (ball x0 delta) :=
    isOpen_ball.measure_pos volume ⟨x0, mem_ball_self hdelta⟩
  rw [suzukiXiCarrierNevanlinnaMeasure_real_univ_eq,
    integral_pos_iff_support_of_nonneg
      suzukiXiCarrierNevanlinnaWeight_nonneg
      integrable_suzukiXiCarrierNevanlinnaWeight]
  exact hballMeasure.trans_le (measure_mono hsubset)

/-- The total carrier Nevanlinna mass is bounded above by `pi`. -/
theorem suzukiXiCarrierNevanlinnaMeasure_real_univ_le_pi :
    suzukiXiCarrierNevanlinnaMeasure.real univ ≤ Real.pi := by
  rw [suzukiXiCarrierNevanlinnaMeasure_real_univ_eq]
  calc
    (∫ x : ℝ, suzukiXiCarrierNevanlinnaWeight x) ≤
        ∫ x : ℝ, (1 + x ^ 2)⁻¹ := by
      exact integral_mono integrable_suzukiXiCarrierNevanlinnaWeight
        integrable_inv_one_add_sq
        suzukiXiCarrierNevanlinnaWeight_le_inv_one_add_sq
    _ = Real.pi := integral_univ_inv_one_add_sq

/-- A nonreal complex parameter cannot belong to the complex image of the
support of a measure on the real axis. -/
theorem nonreal_not_mem_carrierNevanlinnaMeasure_support_image
    {z : ℂ} (hz : z.im ≠ 0) :
    z ∉ algebraMap ℝ ℂ '' suzukiXiCarrierNevanlinnaMeasure.support := by
  rintro ⟨x, _, hzx⟩
  apply hz
  rw [← hzx]
  simp

/-- The standard resolvent is integrable against the finite carrier
Nevanlinna measure at every nonreal parameter. -/
theorem integrable_resolvent_suzukiXiCarrierNevanlinnaMeasure
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (resolvent z) suzukiXiCarrierNevanlinnaMeasure :=
  integrable_resolvent
    (nonreal_not_mem_carrierNevanlinnaMeasure_support_image hz)

/-- The standard finite-measure resolvent transform is analytic throughout
the complement of the real axis. -/
theorem analyticOn_suzukiXiCarrierNevanlinnaResolventTransform :
    AnalyticOn ℂ
      (resolventTransform suzukiXiCarrierNevanlinnaMeasure)
      {z : ℂ | z.im ≠ 0} :=
  (analyticOn_resolventTransform
    (μ := suzukiXiCarrierNevanlinnaMeasure)).mono fun _ hz ↦
      nonreal_not_mem_carrierNevanlinnaMeasure_support_image hz

/-- Mathlib's finite-measure resolvent derivative specialized to the exact
xi-carrier Nevanlinna measure. -/
theorem hasDerivAt_suzukiXiCarrierNevanlinnaResolventTransform
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (resolventTransform suzukiXiCarrierNevanlinnaMeasure)
      (∫ x : ℝ, resolvent z x ^ 2
        ∂suzukiXiCarrierNevanlinnaMeasure) z :=
  hasDerivAt_resolventTransform z
    (nonreal_not_mem_carrierNevanlinnaMeasure_support_image hz)

/-- The finite-measure integrand naturally produced by the normalization
`dμ = density(x) dx / (1 + x^2)`. -/
def suzukiXiCarrierNevanlinnaIntegrand (z : ℂ) (x : ℝ) : ℂ :=
  (1 + (x : ℂ) * z) / ((x : ℂ) - z)

/-- Multiplication by the Nevanlinna weight converts its finite-measure
integrand exactly into the original normalized carrier Herglotz integrand. -/
theorem suzukiXiCarrierNevanlinnaWeight_smul_integrand
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    suzukiXiCarrierNevanlinnaWeight x •
        suzukiXiCarrierNevanlinnaIntegrand z x =
      suzukiXiCarrierHerglotzIntegrand z x := by
  rw [Complex.real_smul]
  unfold suzukiXiCarrierNevanlinnaWeight
    suzukiXiCarrierNevanlinnaIntegrand
    suzukiXiCarrierHerglotzIntegrand
    suzukiXiNormalizedCauchyKernel
  push_cast
  have hxz := ofReal_sub_ne_zero_of_im_ne_zero hz x
  have hquad := one_add_sq_ofReal_ne_zero x
  field_simp [hxz, hquad]
  ring

/-- The original normalized carrier Herglotz transform is literally the
integral of the finite-measure integrand against the carrier Nevanlinna
measure. -/
theorem suzukiXiCarrierHerglotzTransform_eq_nevanlinnaMeasure_integral
    {z : ℂ} (hz : z.im ≠ 0) :
    suzukiXiCarrierHerglotzTransform z =
      ∫ x : ℝ, suzukiXiCarrierNevanlinnaIntegrand z x
        ∂suzukiXiCarrierNevanlinnaMeasure := by
  unfold suzukiXiCarrierHerglotzTransform
  rw [integral_suzukiXiCarrierNevanlinnaMeasure_eq_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦
    (suzukiXiCarrierNevanlinnaWeight_smul_integrand hz x).symm

/-- Pointwise affine-resolvent decomposition of the finite-measure
Nevanlinna integrand. -/
theorem suzukiXiCarrierNevanlinnaIntegrand_eq_resolvent
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    suzukiXiCarrierNevanlinnaIntegrand z x =
      z + (1 + z ^ 2) * resolvent z x := by
  unfold suzukiXiCarrierNevanlinnaIntegrand resolvent
  rw [Ring.inverse_eq_inv]
  change (1 + (x : ℂ) * z) / ((x : ℂ) - z) =
    z + (1 + z ^ 2) * (((x : ℂ) - z)⁻¹)
  have hxz := ofReal_sub_ne_zero_of_im_ne_zero hz x
  field_simp [hxz]
  ring

/-- The finite-measure Nevanlinna integrand is integrable at every nonreal
parameter. -/
theorem integrable_suzukiXiCarrierNevanlinnaIntegrand
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (suzukiXiCarrierNevanlinnaIntegrand z)
      suzukiXiCarrierNevanlinnaMeasure := by
  have haffine : Integrable (fun x : ℝ ↦
      z + (1 + z ^ 2) * resolvent z x)
      suzukiXiCarrierNevanlinnaMeasure :=
    (integrable_const z).add
      ((integrable_resolvent_suzukiXiCarrierNevanlinnaMeasure hz).const_mul _)
  apply haffine.congr
  exact Eventually.of_forall fun x ↦
    (suzukiXiCarrierNevanlinnaIntegrand_eq_resolvent hz x).symm

/-- The imaginary part of the finite-measure Nevanlinna integrand is an
everywhere-positive Poisson density in the upper half-plane. -/
theorem suzukiXiCarrierNevanlinnaIntegrand_im
    (z : ℂ) (x : ℝ) :
    (suzukiXiCarrierNevanlinnaIntegrand z x).im =
      z.im * (1 + x ^ 2) /
        Complex.normSq ((x : ℂ) - z) := by
  unfold suzukiXiCarrierNevanlinnaIntegrand
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.sub_im, zero_mul, add_zero, zero_sub]
  ring

/-- Strict positivity of one finite-measure Nevanlinna integrand in the open
upper half-plane. -/
theorem suzukiXiCarrierNevanlinnaIntegrand_im_pos
    {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    0 < (suzukiXiCarrierNevanlinnaIntegrand z x).im := by
  rw [suzukiXiCarrierNevanlinnaIntegrand_im]
  exact div_pos (mul_pos hz (by positivity))
    (Complex.normSq_pos.mpr
      (ofReal_sub_ne_zero_of_im_ne_zero hz.ne' x))

/-- Canonical finite-measure resolvent representation of the arithmetic
carrier Herglotz transform. -/
theorem suzukiXiCarrierHerglotzTransform_eq_resolventTransform
    {z : ℂ} (hz : z.im ≠ 0) :
    suzukiXiCarrierHerglotzTransform z =
      z * (suzukiXiCarrierNevanlinnaMeasure.real univ : ℂ) +
        (1 + z ^ 2) *
          resolventTransform suzukiXiCarrierNevanlinnaMeasure z := by
  rw [suzukiXiCarrierHerglotzTransform_eq_nevanlinnaMeasure_integral hz]
  calc
    (∫ x : ℝ, suzukiXiCarrierNevanlinnaIntegrand z x
        ∂suzukiXiCarrierNevanlinnaMeasure) =
        ∫ x : ℝ, (z + (1 + z ^ 2) * resolvent z x)
          ∂suzukiXiCarrierNevanlinnaMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦
        suzukiXiCarrierNevanlinnaIntegrand_eq_resolvent hz x
    _ = (∫ _ : ℝ, z ∂suzukiXiCarrierNevanlinnaMeasure) +
        ∫ x : ℝ, (1 + z ^ 2) * resolvent z x
          ∂suzukiXiCarrierNevanlinnaMeasure := by
      rw [integral_add (integrable_const z)
        ((integrable_resolvent_suzukiXiCarrierNevanlinnaMeasure hz).const_mul _)]
    _ = z * (suzukiXiCarrierNevanlinnaMeasure.real univ : ℂ) +
        (1 + z ^ 2) *
          resolventTransform suzukiXiCarrierNevanlinnaMeasure z := by
      rw [integral_const, integral_const_mul,
        resolventTransform_apply, Complex.real_smul]
      ring

/-- The normalization point `i` reads off the complete real mass of the
carrier Nevanlinna measure exactly. -/
theorem suzukiXiCarrierHerglotzTransform_I :
    suzukiXiCarrierHerglotzTransform Complex.I =
      Complex.I *
        (suzukiXiCarrierNevanlinnaMeasure.real univ : ℂ) := by
  simpa [Complex.I_sq] using
    (suzukiXiCarrierHerglotzTransform_eq_resolventTransform
      (z := Complex.I) (by simp))

/-- The imaginary value at `i` is exactly the finite Nevanlinna mass. -/
theorem suzukiXiCarrierHerglotzTransform_I_im :
    (suzukiXiCarrierHerglotzTransform Complex.I).im =
      suzukiXiCarrierNevanlinnaMeasure.real univ := by
  rw [suzukiXiCarrierHerglotzTransform_I]
  simp

/-- The arithmetic carrier transform maps the open upper half-plane into the
open upper half-plane.  This strengthens the earlier nonnegative statement;
strictness follows from the newly proved positive total carrier mass. -/
theorem suzukiXiCarrierHerglotzTransform_im_pos
    {z : ℂ} (hz : 0 < z.im) :
    0 < (suzukiXiCarrierHerglotzTransform z).im := by
  rw [suzukiXiCarrierHerglotzTransform_eq_nevanlinnaMeasure_integral hz.ne']
  have hint := integrable_suzukiXiCarrierNevanlinnaIntegrand hz.ne'
  rw [show
    (∫ x : ℝ, suzukiXiCarrierNevanlinnaIntegrand z x
      ∂suzukiXiCarrierNevanlinnaMeasure).im =
      ∫ x : ℝ, (suzukiXiCarrierNevanlinnaIntegrand z x).im
        ∂suzukiXiCarrierNevanlinnaMeasure by
    simpa using (integral_im hint).symm]
  rw [integral_pos_iff_support_of_nonneg
    (fun x ↦ (suzukiXiCarrierNevanlinnaIntegrand_im_pos hz x).le)
    hint.im]
  have hsupport : Function.support
      (fun x : ℝ ↦ (suzukiXiCarrierNevanlinnaIntegrand z x).im) = univ := by
    ext x
    simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
    exact (suzukiXiCarrierNevanlinnaIntegrand_im_pos hz x).ne'
  rw [hsupport]
  exact (ENNReal.toReal_pos_iff.mp (by
    simpa only [measureReal_def] using
      suzukiXiCarrierNevanlinnaMeasure_real_univ_pos)).1

end

end RiemannGaussian
