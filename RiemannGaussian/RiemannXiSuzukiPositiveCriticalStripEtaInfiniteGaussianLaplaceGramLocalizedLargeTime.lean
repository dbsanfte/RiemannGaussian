import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalizedPhaseControl

/-!
# Large-proper-time limit of the localized infinite eta Gram

After removing the explicit Gaussian Fourier prefactor, the localized
arithmetic kernel converges as proper time tends to infinity to the full
oscillatory product kernel.  Dominated convergence identifies its integral
with the squared norm of the infinite eta Laplace partition at the center
ordinate.

Thus the normalized localized Gram has a genuinely zero-sensitive limit: it
vanishes at every nontrivial zeta zero.  This is an exact bridge to the zero
condition, not yet an estimate excluding an off-critical zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The undamped oscillatory product kernel obtained from the localized Gram
at infinite proper time. -/
def pairedEtaUndampedLocalizedLaplaceKernel
    (sigma gamma : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-sigma * (p.1 + p.2)) *
    Real.cos (gamma * (p.2 - p.1))

/-- The undamped product tilt is integrable over the fixed eta product
measure. -/
theorem integrable_exp_neg_sigma_sum_pairedEtaLogMeasure_prod
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun p : ℝ × ℝ ↦
      Real.exp (-sigma * (p.1 + p.2)))
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  have hsigmaInt :=
    integrable_rexp_neg_mul_pairedEtaLogMeasure hsigma
  have hprod := hsigmaInt.mul_prod hsigmaInt
  apply hprod.congr
  exact Eventually.of_forall fun p => by
    change Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) =
      Real.exp (-sigma * (p.1 + p.2))
    rw [← Real.exp_add]
    congr 1
    ring

/-- The undamped oscillatory kernel is integrable. -/
theorem integrable_pairedEtaUndampedLocalizedLaplaceKernel
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Integrable (pairedEtaUndampedLocalizedLaplaceKernel sigma gamma)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  apply (integrable_exp_neg_sigma_sum_pairedEtaLogMeasure_prod hsigma).mono
  · exact (show Continuous
      (pairedEtaUndampedLocalizedLaplaceKernel sigma gamma) by
        unfold pairedEtaUndampedLocalizedLaplaceKernel
        fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun p => by
      unfold pairedEtaUndampedLocalizedLaplaceKernel
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.abs_cos_le_one _)

/-- The undamped product integral is exactly the squared norm of the infinite
eta Laplace partition at the center ordinate. -/
theorem integral_pairedEtaUndampedLocalizedLaplaceKernel_eq_normSq
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    (∫ p : ℝ × ℝ,
        pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      Complex.normSq (pairedEtaLaplacePartition
        ((sigma : ℂ) + (gamma : ℂ) * Complex.I)) := by
  have hcos := integrable_pairedEtaTiltedCosineKernel
    sigma gamma hsigma
  have hsin := integrable_pairedEtaTiltedSineKernel
    sigma gamma hsigma
  rw [show
    pairedEtaUndampedLocalizedLaplaceKernel sigma gamma =
      (fun p : ℝ × ℝ ↦
        (Real.exp (-sigma * p.1) * Real.cos (gamma * p.1)) *
            (Real.exp (-sigma * p.2) * Real.cos (gamma * p.2)) +
          (Real.exp (-sigma * p.1) * Real.sin (gamma * p.1)) *
            (Real.exp (-sigma * p.2) * Real.sin (gamma * p.2))) by
      funext p
      unfold pairedEtaUndampedLocalizedLaplaceKernel
      rw [show gamma * (p.2 - p.1) =
          gamma * p.2 - gamma * p.1 by ring,
        Real.cos_sub]
      rw [show -sigma * (p.1 + p.2) =
          -sigma * p.1 + -sigma * p.2 by ring,
        Real.exp_add]
      ring]
  rw [integral_add (hcos.mul_prod hcos) (hsin.mul_prod hsin),
    integral_prod_mul
      (μ := pairedEtaLogMeasure) (ν := pairedEtaLogMeasure)
      (fun t : ℝ ↦ Real.exp (-sigma * t) * Real.cos (gamma * t))
      (fun u : ℝ ↦ Real.exp (-sigma * u) * Real.cos (gamma * u)),
    integral_prod_mul
      (μ := pairedEtaLogMeasure) (ν := pairedEtaLogMeasure)
      (fun t : ℝ ↦ Real.exp (-sigma * t) * Real.sin (gamma * t))
      (fun u : ℝ ↦ Real.exp (-sigma * u) * Real.sin (gamma * u))]
  rw [pairedEtaLaplacePartition_eq_cosine_sub_I_sine
    sigma gamma hsigma]
  unfold pairedEtaTiltedCosineMoment pairedEtaTiltedSineMoment
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

/-- Pointwise, the localized kernel tends to the full oscillatory product
kernel as proper time tends to infinity. -/
theorem tendsto_pairedEtaLocalizedGaussianLaplaceKernel_atTop
    (sigma gamma : ℝ) (p : ℝ × ℝ) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p)
      atTop
      (nhds (pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p)) := by
  have hden : Tendsto (fun tau : ℝ ↦ 4 * tau) atTop atTop := by
    simpa [mul_comm] using
      (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 4))
  have hquot : Tendsto (fun tau : ℝ ↦
      -(p.1 - p.2) ^ 2 / (4 * tau)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hexp : Tendsto (fun tau : ℝ ↦
      Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)))
      atTop (nhds 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hquot
    convert h using 1 <;> simp [Function.comp_def]
  unfold pairedEtaLocalizedGaussianLaplaceKernel
    pairedEtaFiniteGaussianLaplaceKernel
    pairedEtaUndampedLocalizedLaplaceKernel
  simpa using (tendsto_const_nhds.mul hexp).mul tendsto_const_nhds

/-- At positive proper time, the localized kernel is dominated by the
integrable undamped product tilt. -/
theorem norm_pairedEtaLocalizedGaussianLaplaceKernel_le_tilt
    (sigma gamma : ℝ) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    ‖pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p‖ ≤
      Real.exp (-sigma * (p.1 + p.2)) := by
  unfold pairedEtaLocalizedGaussianLaplaceKernel
    pairedEtaFiniteGaussianLaplaceKernel
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hquad : -(p.1 - p.2) ^ 2 / (4 * tau) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hdamp : Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquad
  have hphase :
      Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) *
          |Real.cos (gamma * (p.2 - p.1))| ≤ 1 := by
    calc
      Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) *
          |Real.cos (gamma * (p.2 - p.1))| ≤
          Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) :=
        mul_le_of_le_one_right (Real.exp_pos _).le
          (Real.abs_cos_le_one _)
      _ ≤ 1 := hdamp
  simpa [mul_assoc] using
    (mul_le_of_le_one_right (Real.exp_pos _).le hphase)

/-- Dominated convergence for the localized eta product kernel at large
proper time. -/
theorem tendsto_integral_pairedEtaLocalizedGaussianLaplaceKernel_atTop
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Tendsto (fun tau : ℝ ↦
      ∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))
      atTop
      (nhds (∫ p : ℝ × ℝ,
        pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2)))
  · exact Eventually.of_forall fun tau =>
      (show Continuous
        (pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma) by
          unfold pairedEtaLocalizedGaussianLaplaceKernel
            pairedEtaFiniteGaussianLaplaceKernel
          fun_prop).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    exact Eventually.of_forall fun p =>
      norm_pairedEtaLocalizedGaussianLaplaceKernel_le_tilt
        sigma gamma htau p
  · exact integrable_exp_neg_sigma_sum_pairedEtaLogMeasure_prod hsigma
  · exact Eventually.of_forall fun p =>
      tendsto_pairedEtaLocalizedGaussianLaplaceKernel_atTop sigma gamma p

/-- The localized kernel integral converges exactly to the squared partition
norm at its center ordinate. -/
theorem
    tendsto_integral_pairedEtaLocalizedGaussianLaplaceKernel_atTop_normSq
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Tendsto (fun tau : ℝ ↦
      ∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure))
      atTop
      (nhds (Complex.normSq (pairedEtaLaplacePartition
        ((sigma : ℂ) + (gamma : ℂ) * Complex.I)))) := by
  simpa [integral_pairedEtaUndampedLocalizedLaplaceKernel_eq_normSq
    hsigma gamma] using
    tendsto_integral_pairedEtaLocalizedGaussianLaplaceKernel_atTop
      hsigma gamma

/-- After dividing out the explicit Gaussian Fourier prefactor, the
localized infinite eta norm converges to the exact pointwise partition
energy at its center. -/
theorem tendsto_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop
    {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma /
        Real.sqrt (Real.pi / tau))
      atTop
      (nhds (Complex.normSq (pairedEtaLaplacePartition
        ((sigma : ℂ) + (gamma : ℂ) * Complex.I)))) := by
  refine (tendsto_congr' (f₂ := fun tau : ℝ ↦
    ∫ p : ℝ × ℝ,
      pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p
      ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    rw [pairedEtaLocalizedGaussianLaplaceNorm_eq_gram hsigma htau gamma]
    unfold pairedEtaLocalizedGaussianLaplaceGram
    field_simp [(Real.sqrt_pos.2 (div_pos Real.pi_pos htau)).ne'])).2 ?_
  exact tendsto_integral_pairedEtaLocalizedGaussianLaplaceKernel_atTop_normSq
    hsigma gamma

/-- At every nontrivial zeta zero, the normalized localized infinite eta
Gaussian norm tends to zero at large proper time. -/
theorem
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianLaplaceNorm rho.1.re tau rho.1.im /
        Real.sqrt (Real.pi / tau))
      atTop (nhds 0) := by
  have h := tendsto_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop
    (NontrivialZetaZero.zero_lt_re rho) rho.1.im
  rw [Complex.re_add_im rho.1,
    pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho] at h
  simpa using h

/-- The same large-time normalized vanishing holds at the complementary
horizontal tilt of every nontrivial zero. -/
theorem
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_complementary_div_sqrt_atTop_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedGaussianLaplaceNorm
          (1 - rho.1.re) tau rho.1.im /
        Real.sqrt (Real.pi / tau))
      atTop (nhds 0) := by
  have hsigma : 0 < 1 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := tendsto_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop
    hsigma rho.1.im
  have hmoments :=
    pairedEtaTiltedMoments_eq_zero_at_complementary_tilt rho
  rw [pairedEtaLaplacePartition_eq_cosine_sub_I_sine
    (1 - rho.1.re) rho.1.im hsigma,
    hmoments.1, hmoments.2] at h
  norm_num at h
  exact h

/-- Consequently, at every nontrivial zeta zero the normalized localized
completion-weight distortion itself tends to zero at large proper time. -/
theorem
    tendsto_pairedEtaLocalizedCompletionWeightDistortionIntegral_div_sqrt_atTop_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    Tendsto (fun tau : ℝ ↦
      pairedEtaLocalizedCompletionWeightDistortionIntegral
          rho.1.re tau rho.1.im /
        Real.sqrt (Real.pi / tau))
      atTop (nhds 0) := by
  have hleft :=
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_div_sqrt_atTop_zero_of_nontrivialZetaZero
      rho
  have hright :=
    tendsto_pairedEtaLocalizedGaussianLaplaceNorm_complementary_div_sqrt_atTop_zero_of_nontrivialZetaZero
      rho
  refine (tendsto_congr' (f₂ := fun tau : ℝ ↦
    pairedEtaLocalizedGaussianLaplaceNorm rho.1.re tau rho.1.im /
        Real.sqrt (Real.pi / tau) -
      pairedEtaLocalizedGaussianLaplaceNorm
          (1 - rho.1.re) tau rho.1.im /
        Real.sqrt (Real.pi / tau)) (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    rw [
      pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
        (NontrivialZetaZero.zero_lt_re rho)
        (NontrivialZetaZero.re_lt_one rho) htau rho.1.im]
    ring)).2 ?_
  simpa using hleft.sub hright

end

end RiemannGaussian
