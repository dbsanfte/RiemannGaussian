import RiemannGaussian.EtaSupportGapGaussianCross

/-!
# The literal eta spectral formula for support/gap Gaussian transfer

The actual support and gap measures give the two factors of a mixed Laplace
product. A joint Gaussian majorant justifies both Fubini exchanges. Taking
the real part only after the complex identity yields the exact eta formula
with gap transform `1/s - pairedEtaLaplacePartition s`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exponential integrability on the literal logarithmic gap measure. -/
theorem integrable_rexp_neg_mul_pairedEtaLogGapMeasure {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ ↦ Real.exp (-sigma * t)) pairedEtaLogGapMeasure :=
  Integrable.mono_measure (integrableOn_exp_mul_Ioi (a := -sigma) (by linarith) 0)
    pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero

/-- The full complex Gaussian-localized mixed eta/gap spectral kernel. -/
def pairedEtaSupportGapSpectralKernel (sigma tau gamma y : ℝ) : ℂ :=
  (translatedGaussian tau gamma y : ℂ) *
    pairedEtaLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I) *
    starRingEnd ℂ (pairedEtaGapLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I))

private def pairedEtaSupportGapGaussianJoint (sigma tau gamma : ℝ) (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (Real.exp (-sigma * (z.2.1 + z.2.2)) : ℂ) *
    complexTranslatedGaussianOscillation tau gamma (z.2.2 - z.2.1) z.1

private theorem pairedEtaSupportGapGaussianJoint_eq_laplaceProduct
    (sigma tau gamma y t u : ℝ) :
    pairedEtaSupportGapGaussianJoint sigma tau gamma (y, (t, u)) =
      (translatedGaussian tau gamma y : ℂ) *
        Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t) *
        starRingEnd ℂ (Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * u)) := by
  unfold pairedEtaSupportGapGaussianJoint complexTranslatedGaussianOscillation translatedGaussian
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, neg_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrable_pairedEtaSupportGapGaussianJoint {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (gamma : ℝ) :
    Integrable (pairedEtaSupportGapGaussianJoint sigma tau gamma)
      (volume.prod (pairedEtaLogMeasure.prod pairedEtaLogGapMeasure)) := by
  have hy := integrable_translatedGaussian htau gamma
  have hA := integrable_rexp_neg_mul_pairedEtaLogMeasure hsigma
  have hG := integrable_rexp_neg_mul_pairedEtaLogGapMeasure hsigma
  apply (hy.mul_prod (hA.mul_prod hG)).mono
  · exact (show Continuous (pairedEtaSupportGapGaussianJoint sigma tau gamma) by
      unfold pairedEtaSupportGapGaussianJoint complexTranslatedGaussianOscillation
      fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun z ↦ by
      apply le_of_eq
      unfold pairedEtaSupportGapGaussianJoint complexTranslatedGaussianOscillation translatedGaussian
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num [Complex.mul_im]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private theorem integral_pairedEtaSupportGapGaussianJoint_prod {sigma : ℝ}
    (hsigma : 0 < sigma) (tau gamma y : ℝ) :
    (∫ p : ℝ × ℝ, pairedEtaSupportGapGaussianJoint sigma tau gamma (y, p)
      ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure)) =
      pairedEtaSupportGapSpectralKernel sigma tau gamma y := by
  have hline : 0 < ((sigma : ℂ) + (y : ℂ) * Complex.I).re := by norm_num; exact hsigma
  have hfun : (fun p : ℝ × ℝ ↦ pairedEtaSupportGapGaussianJoint sigma tau gamma (y, p)) =
      (fun p ↦ (translatedGaussian tau gamma y : ℂ) *
        (Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * p.1) *
          starRingEnd ℂ (Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * p.2)))) := by
    funext p
    rw [pairedEtaSupportGapGaussianJoint_eq_laplaceProduct]
    ring
  rw [hfun, integral_const_mul,
    integral_prod_mul (μ := pairedEtaLogMeasure) (ν := pairedEtaLogGapMeasure)
      (fun t : ℝ ↦ Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      (fun u : ℝ ↦ starRingEnd ℂ (Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * u))),
    integral_conj,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hline,
    integral_exp_neg_mul_pairedEtaLogGapMeasure_eq_laplacePartition hline]
  unfold pairedEtaSupportGapSpectralKernel
  ring

private theorem integral_pairedEtaSupportGapGaussianJoint_volume
    (sigma gamma : ℝ) {tau : ℝ} (htau : 0 < tau) (p : ℝ × ℝ) :
    (∫ y : ℝ, pairedEtaSupportGapGaussianJoint sigma tau gamma (y, p)) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
        Complex.exp (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ)) := by
  unfold pairedEtaSupportGapGaussianJoint
  change (∫ y : ℝ, (Real.exp (-sigma * (p.1 + p.2)) : ℂ) *
    complexTranslatedGaussianOscillation tau gamma (p.2 - p.1) y) = _
  rw [integral_const_mul, integral_complexTranslatedGaussianOscillation htau]
  unfold pairedEtaFiniteGaussianLaplaceKernel
  rw [Complex.exp_add]
  norm_num
  ring_nf

/-- Genuine absolute integrability of the complex localized eta/gap product. -/
theorem integrable_pairedEtaSupportGapSpectralKernel {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (gamma : ℝ) :
    Integrable (pairedEtaSupportGapSpectralKernel sigma tau gamma) := by
  apply (integrable_pairedEtaSupportGapGaussianJoint hsigma htau gamma).integral_prod_left.congr
  exact Eventually.of_forall fun y ↦ integral_pairedEtaSupportGapGaussianJoint_prod hsigma tau gamma y

/-- The exact complex mixed Fourier--Laplace identity, before discarding
the oriented imaginary cross channel. -/
theorem pairedEtaSupportGapSpectralKernel_integral_eq_cross {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (gamma : ℝ) :
    (∫ y : ℝ, pairedEtaSupportGapSpectralKernel sigma tau gamma y) =
      ∫ p : ℝ × ℝ, (Real.sqrt (Real.pi / tau) : ℂ) *
        (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
        Complex.exp (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))
        ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
  have hjoint := integrable_pairedEtaSupportGapGaussianJoint hsigma htau gamma
  calc
    (∫ y : ℝ, pairedEtaSupportGapSpectralKernel sigma tau gamma y) =
        ∫ y : ℝ, ∫ p : ℝ × ℝ, pairedEtaSupportGapGaussianJoint sigma tau gamma (y, p)
          ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦
        (integral_pairedEtaSupportGapGaussianJoint_prod hsigma tau gamma y).symm
    _ = ∫ p : ℝ × ℝ, ∫ y : ℝ, pairedEtaSupportGapGaussianJoint sigma tau gamma (y, p)
          ∂volume ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := integral_integral_swap hjoint
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p ↦ integral_pairedEtaSupportGapGaussianJoint_volume sigma gamma htau p

/-- The real spectral correlation is the localized Gaussian cross integral
of the literal eta and gap measures, with the exact Fourier constant. -/
theorem pairedEtaSupportGapSpectralKernel_re_integral_eq_cross {sigma tau : ℝ}
    (hsigma : 0 < sigma) (htau : 0 < tau) (gamma : ℝ) :
    (∫ y : ℝ, (pairedEtaSupportGapSpectralKernel sigma tau gamma y).re) =
      Real.sqrt (Real.pi / tau) *
        ∫ p, pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
  let K : ℝ × ℝ → ℂ := fun p ↦ (Real.sqrt (Real.pi / tau) : ℂ) *
    (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
    Complex.exp (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))
  have hiK : Integrable K (pairedEtaLogMeasure.prod pairedEtaLogGapMeasure) := by
    apply (integrable_pairedEtaSupportGapGaussianJoint hsigma htau gamma).integral_prod_right.congr
    exact Eventually.of_forall fun p ↦ integral_pairedEtaSupportGapGaussianJoint_volume sigma gamma htau p
  have hre := integral_re (integrable_pairedEtaSupportGapSpectralKernel hsigma htau gamma)
  rw [RCLike.re_eq_complex_re] at hre
  rw [hre, pairedEtaSupportGapSpectralKernel_integral_eq_cross hsigma htau gamma]
  have hreK := integral_re hiK
  rw [RCLike.re_eq_complex_re] at hreK
  change (∫ p, K p ∂(pairedEtaLogMeasure.prod pairedEtaLogGapMeasure)).re = _
  rw [← hreK, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [K]
  unfold pairedEtaLocalizedGaussianLaplaceKernel
  rw [show Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ) =
      ((gamma * (p.2 - p.1) : ℝ) : ℂ) * Complex.I by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  ring

/-- The continuous heat transfer equals the normalized real part of the
complete mixed spectral carrier. -/
theorem pairedEtaSupportGapGaussianLeakage_eq_spectralKernel {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (gamma : ℝ) :
    pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) =
      (1 / Real.pi) * ∫ y : ℝ, (pairedEtaSupportGapSpectralKernel sigma (h ^ 2) gamma y).re := by
  rw [pairedEtaSupportGapSpectralKernel_re_integral_eq_cross hsigma (sq_pos_of_pos hh),
    pairedEtaSupportGapGaussianLeakage_linear_eq_localized_cross hsigma hh,
    Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hh.le]
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsquare : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp
  rw [hsquare]
  ring

/-- Exact spectral bridge from continuous eta support/gap heat transfer to
the genuine eta transform and its literal complementary gap transform. -/
theorem pairedEtaSupportGapGaussianLeakage_eq_eta_spectral {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (gamma : ℝ) :
    pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ gamma * t) =
      (1 / Real.pi) * ∫ y : ℝ, Real.exp (-(h ^ 2) * (y - gamma) ^ 2) *
        (pairedEtaLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I) *
          starRingEnd ℂ ((((sigma : ℂ) + (y : ℂ) * Complex.I)⁻¹) -
            pairedEtaLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I))).re := by
  have hfun : (fun y : ℝ ↦ Real.exp (-(h ^ 2) * (y - gamma) ^ 2) *
      (pairedEtaLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I) *
        starRingEnd ℂ ((((sigma : ℂ) + (y : ℂ) * Complex.I)⁻¹) -
          pairedEtaLaplacePartition ((sigma : ℂ) + (y : ℂ) * Complex.I))).re) =
      (fun y ↦ (pairedEtaSupportGapSpectralKernel sigma (h ^ 2) gamma y).re) := by
    funext y
    have hline : 0 < ((sigma : ℂ) + (y : ℂ) * Complex.I).re := by norm_num; exact hsigma
    rw [pairedEtaSupportGapSpectralKernel,
      pairedEtaGapLaplacePartition_eq_inv_sub_pairedEtaLaplacePartition hline]
    simp only [translatedGaussian, mul_assoc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [hfun]
  exact pairedEtaSupportGapGaussianLeakage_eq_spectralKernel hsigma hh gamma

/-- The critical estimate is an unconditional bound on the literal mixed
eta spectral integral, uniform over every real Gaussian centre. -/
theorem pairedEtaSupportGapSpectralKernel_uniform_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) (gamma : ℝ) :
    |(1 / Real.pi) * (∫ y : ℝ, (pairedEtaSupportGapSpectralKernel (1 / 2) (h ^ 2) gamma y).re) -
      h * Real.log (1 / h) * pairedEtaHeatPhaseProfile (h * gamma)| ≤ 32 * h := by
  rw [← pairedEtaSupportGapGaussianLeakage_eq_spectralKernel (by norm_num) hh gamma]
  exact pairedEtaSupportGapGaussianLeakage_uniform_error_le hh hhone gamma

end

end RiemannGaussian
