import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalized

/-!
# Quantitative phase control for the localized infinite eta Gram

The localized arithmetic kernel differs from its positive zero-centered
envelope only through `cos (gamma * (u - t))`.  This module combines the
global quadratic cosine bound with the Gaussian second-moment bound to
control that phase loss uniformly over the fixed infinite eta measure.

The resulting estimate proves that, at every fixed horizontal tilt and
ordinate, the localized and zero-centered Gaussian norms differ by
`O(sqrt tau)` as `tau → 0+`.  This is unconditional phase control, not a
zero-location theorem.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Global quadratic control of the loss from one in the real cosine. -/
theorem abs_cos_sub_one_le_sq_div_two (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

/-- The quadratic factor in a Gaussian is uniformly bounded by four times
its proper-time parameter. -/
theorem sq_mul_exp_neg_sq_div_four_mul_le
    {tau : ℝ} (htau : 0 < tau) (d : ℝ) :
    d ^ 2 * Real.exp (-d ^ 2 / (4 * tau)) ≤ 4 * tau := by
  let q : ℝ := d ^ 2 / (4 * tau)
  have hq : q * Real.exp (-q) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one q).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  calc
    d ^ 2 * Real.exp (-d ^ 2 / (4 * tau)) =
        (4 * tau) * (q * Real.exp (-q)) := by
      dsimp only [q]
      field_simp [htau.ne']
    _ ≤ (4 * tau) * 1 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 4 * tau := by ring

/-- The product integral of the undamped horizontal tilt is the square of
the total tilted eta mass. -/
theorem integral_exp_neg_sigma_sum_pairedEtaLogMeasure_prod
    {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ p : ℝ × ℝ, Real.exp (-sigma * (p.1 + p.2))
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      pairedEtaTiltedCosineMoment sigma 0 ^ 2 := by
  have hsigmaInt :=
    integrable_rexp_neg_mul_pairedEtaLogMeasure hsigma
  rw [show
    (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2))) =
      (fun p : ℝ × ℝ ↦
        Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2)) by
      funext p
      rw [← Real.exp_add]
      congr 1
      ring]
  rw [integral_prod_mul
    (μ := pairedEtaLogMeasure) (ν := pairedEtaLogMeasure)
    (fun t : ℝ ↦ Real.exp (-sigma * t))
    (fun u : ℝ ↦ Real.exp (-sigma * u))]
  unfold pairedEtaTiltedCosineMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  ring

/-- Pointwise phase error: the Gaussian converts the quadratic cosine loss
into a uniform factor `2 * gamma^2 * tau` times the undamped product tilt. -/
theorem abs_pairedEtaLocalizedGaussianLaplaceKernel_sub_le
    (sigma gamma : ℝ) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    |pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p -
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p| ≤
      2 * gamma ^ 2 * tau *
        Real.exp (-sigma * (p.1 + p.2)) := by
  have hcos := abs_cos_sub_one_le_sq_div_two
    (gamma * (p.2 - p.1))
  have hdamp := sq_mul_exp_neg_sq_div_four_mul_le htau (p.1 - p.2)
  have htilt : 0 ≤ Real.exp (-sigma * (p.1 + p.2)) :=
    (Real.exp_pos _).le
  have hgauss : 0 ≤ Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) :=
    (Real.exp_pos _).le
  unfold pairedEtaLocalizedGaussianLaplaceKernel
    pairedEtaFiniteGaussianLaplaceKernel
  rw [show
    Real.exp (-sigma * (p.1 + p.2)) *
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) *
          Real.cos (gamma * (p.2 - p.1)) -
        Real.exp (-sigma * (p.1 + p.2)) *
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) =
      (Real.exp (-sigma * (p.1 + p.2)) *
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau))) *
        (Real.cos (gamma * (p.2 - p.1)) - 1) by ring]
  simp only [abs_mul, abs_of_nonneg htilt, abs_of_nonneg hgauss]
  calc
    Real.exp (-sigma * (p.1 + p.2)) *
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) *
          |Real.cos (gamma * (p.2 - p.1)) - 1| ≤
        Real.exp (-sigma * (p.1 + p.2)) *
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) *
          ((gamma * (p.2 - p.1)) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hcos (mul_nonneg htilt hgauss)
    _ = Real.exp (-sigma * (p.1 + p.2)) * (gamma ^ 2 / 2) *
          ((p.1 - p.2) ^ 2 *
            Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau))) := by ring
    _ ≤ Real.exp (-sigma * (p.1 + p.2)) * (gamma ^ 2 / 2) *
          (4 * tau) := by
      exact mul_le_mul_of_nonneg_left hdamp
        (mul_nonneg htilt (by positivity))
    _ = 2 * gamma ^ 2 * tau *
          Real.exp (-sigma * (p.1 + p.2)) := by ring

/-- The product-measure envelope for the localized phase error is genuinely
integrable. -/
theorem integrable_pairedEtaLocalizedGaussianLaplacePhaseErrorEnvelope
    {sigma : ℝ} (hsigma : 0 < sigma) (tau gamma : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      2 * gamma ^ 2 * tau * Real.exp (-sigma * (p.1 + p.2)))
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  have hsigmaInt :=
    integrable_rexp_neg_mul_pairedEtaLogMeasure hsigma
  have hprod := hsigmaInt.mul_prod hsigmaInt
  have hsum : Integrable (fun p : ℝ × ℝ ↦
      Real.exp (-sigma * (p.1 + p.2)))
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
    apply hprod.congr
    exact Eventually.of_forall fun p => by
      change Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) =
        Real.exp (-sigma * (p.1 + p.2))
      rw [← Real.exp_add]
      congr 1
      ring
  exact hsum.const_mul (2 * gamma ^ 2 * tau)

/-- Integrated phase-error estimate over the fixed infinite eta product
measure. -/
theorem abs_integral_pairedEtaLocalizedGaussianLaplaceKernel_sub_le
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    |∫ p : ℝ × ℝ,
        (pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p -
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p)
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)| ≤
      2 * gamma ^ 2 * tau *
        pairedEtaTiltedCosineMoment sigma 0 ^ 2 := by
  have hbound := norm_integral_le_of_norm_le
    (integrable_pairedEtaLocalizedGaussianLaplacePhaseErrorEnvelope
      hsigma tau gamma)
    (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact abs_pairedEtaLocalizedGaussianLaplaceKernel_sub_le
        sigma gamma htau p)
  rw [Real.norm_eq_abs, integral_const_mul,
    integral_exp_neg_sigma_sum_pairedEtaLogMeasure_prod hsigma] at hbound
  exact hbound

/-- Explicit phase-control bound for the actual localized infinite eta norm.
The right side is `O(sqrt tau)` at fixed `sigma` and `gamma`. -/
theorem abs_pairedEtaLocalizedGaussianLaplaceNorm_sub_le
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    |pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
        pairedEtaGaussianLaplaceNorm sigma tau| ≤
      Real.sqrt (Real.pi / tau) *
        (2 * gamma ^ 2 * tau *
          pairedEtaTiltedCosineMoment sigma 0 ^ 2) := by
  rw [pairedEtaLocalizedGaussianLaplaceNorm_eq_gram hsigma htau gamma,
    pairedEtaGaussianLaplaceNorm_eq_gram hsigma htau]
  unfold pairedEtaLocalizedGaussianLaplaceGram
    pairedEtaGaussianLaplaceGram
  rw [← mul_sub, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _),
    ← integral_sub
      (integrable_pairedEtaLocalizedGaussianLaplaceKernel
        hsigma htau gamma)
      (integrable_pairedEtaGaussianLaplaceKernel hsigma htau)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_pairedEtaLocalizedGaussianLaplaceKernel_sub_le
      hsigma htau gamma)
    (Real.sqrt_nonneg _)

/-- Elementary normalization of the Gaussian prefactor at positive proper
time. -/
theorem sqrt_pi_div_mul_self
    {tau : ℝ} (htau : 0 < tau) :
    Real.sqrt (Real.pi / tau) * tau =
      Real.sqrt Real.pi * Real.sqrt tau := by
  rw [Real.sqrt_div Real.pi_pos.le]
  calc
    Real.sqrt Real.pi / Real.sqrt tau * tau =
        Real.sqrt Real.pi / Real.sqrt tau *
          (Real.sqrt tau * Real.sqrt tau) := by
      rw [Real.mul_self_sqrt htau.le]
    _ = Real.sqrt Real.pi * Real.sqrt tau := by
      field_simp [(Real.sqrt_pos.2 htau).ne']

/-- At every fixed positive horizontal tilt and ordinate, localization is an
`O(sqrt tau)` perturbation of the positive zero-centered Gram as proper time
tends to zero from the right. -/
theorem tendsto_pairedEtaLocalizedGaussianLaplaceNorm_sub_zeroCentered
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
        pairedEtaGaussianLaplaceNorm sigma tau)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let C : ℝ := 2 * Real.sqrt Real.pi * gamma ^ 2 *
    pairedEtaTiltedCosineMoment sigma 0 ^ 2
  have hid : Tendsto (fun tau : ℝ ↦ tau)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hsqrt : Tendsto (fun tau : ℝ ↦ Real.sqrt tau)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hid.sqrt
  have hmajor : Tendsto (fun tau : ℝ ↦ C * Real.sqrt tau)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  apply squeeze_zero_norm' (a := fun tau : ℝ ↦ C * Real.sqrt tau)
  · filter_upwards [self_mem_nhdsWithin] with tau htau
    rw [Real.norm_eq_abs]
    calc
      |pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
          pairedEtaGaussianLaplaceNorm sigma tau| ≤
          Real.sqrt (Real.pi / tau) *
            (2 * gamma ^ 2 * tau *
              pairedEtaTiltedCosineMoment sigma 0 ^ 2) :=
        abs_pairedEtaLocalizedGaussianLaplaceNorm_sub_le
          hsigma htau gamma
      _ = C * Real.sqrt tau := by
        dsimp only [C]
        rw [show
          Real.sqrt (Real.pi / tau) *
              (2 * gamma ^ 2 * tau *
                pairedEtaTiltedCosineMoment sigma 0 ^ 2) =
            (2 * gamma ^ 2 *
                pairedEtaTiltedCosineMoment sigma 0 ^ 2) *
              (Real.sqrt (Real.pi / tau) * tau) by ring,
          sqrt_pi_div_mul_self htau]
        ring
  · exact hmajor

/-- Explicit short-time phase-error bound for the localized complementary
completion distortion itself. -/
theorem abs_pairedEtaLocalizedCompletionWeightDistortionIntegral_sub_le
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) (gamma : ℝ) :
    |pairedEtaLocalizedCompletionWeightDistortionIntegral sigma tau gamma -
        pairedEtaCompletionWeightDistortionIntegral sigma tau| ≤
      Real.sqrt (Real.pi / tau) *
        (2 * gamma ^ 2 * tau *
          (pairedEtaTiltedCosineMoment sigma 0 ^ 2 +
            pairedEtaTiltedCosineMoment (1 - sigma) 0 ^ 2)) := by
  rw [
    pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
      hsigma hsigmaOne htau gamma,
    pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
      hsigma hsigmaOne htau]
  have hleft := abs_pairedEtaLocalizedGaussianLaplaceNorm_sub_le
    hsigma htau gamma
  have hright := abs_pairedEtaLocalizedGaussianLaplaceNorm_sub_le
    (sub_pos.mpr hsigmaOne) htau gamma
  calc
    |(pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
          pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma) -
        (pairedEtaGaussianLaplaceNorm sigma tau -
          pairedEtaGaussianLaplaceNorm (1 - sigma) tau)| =
      |(pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
          pairedEtaGaussianLaplaceNorm sigma tau) -
        (pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma -
          pairedEtaGaussianLaplaceNorm (1 - sigma) tau)| := by
        congr 1
        ring
    _ ≤ |pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
          pairedEtaGaussianLaplaceNorm sigma tau| +
        |-(pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma -
          pairedEtaGaussianLaplaceNorm (1 - sigma) tau)| := by
      rw [sub_eq_add_neg]
      exact abs_add_le _ _
    _ = |pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
          pairedEtaGaussianLaplaceNorm sigma tau| +
        |pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma -
          pairedEtaGaussianLaplaceNorm (1 - sigma) tau| := by
      rw [abs_neg]
    _ ≤ Real.sqrt (Real.pi / tau) *
          (2 * gamma ^ 2 * tau *
            pairedEtaTiltedCosineMoment sigma 0 ^ 2) +
        Real.sqrt (Real.pi / tau) *
          (2 * gamma ^ 2 * tau *
            pairedEtaTiltedCosineMoment (1 - sigma) 0 ^ 2) :=
      add_le_add hleft hright
    _ = Real.sqrt (Real.pi / tau) *
        (2 * gamma ^ 2 * tau *
          (pairedEtaTiltedCosineMoment sigma 0 ^ 2 +
            pairedEtaTiltedCosineMoment (1 - sigma) 0 ^ 2)) := by
      ring

/-- The localized complementary completion distortion converges to the
strictly signed zero-centered distortion at short proper time. -/
theorem
    tendsto_pairedEtaLocalizedCompletionWeightDistortionIntegral_sub_zeroCentered
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (gamma : ℝ) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedCompletionWeightDistortionIntegral sigma tau gamma -
        pairedEtaCompletionWeightDistortionIntegral sigma tau)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hleft :=
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_sub_zeroCentered
      hsigma gamma
  have hright :=
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_sub_zeroCentered
      (sub_pos.mpr hsigmaOne) gamma
  refine (tendsto_congr' (f₂ := fun tau : ℝ ↦
    (pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
      pairedEtaGaussianLaplaceNorm sigma tau) -
    (pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma -
      pairedEtaGaussianLaplaceNorm (1 - sigma) tau)) (by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    rw [
      pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
        hsigma hsigmaOne htau gamma,
      pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
        hsigma hsigmaOne htau]
    ring)).2 ?_
  simpa using hleft.sub hright

end

end RiemannGaussian
