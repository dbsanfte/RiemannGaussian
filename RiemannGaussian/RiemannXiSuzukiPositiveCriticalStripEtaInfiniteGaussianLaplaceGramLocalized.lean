import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramMonotonicity

/-!
# Phase-sensitive localization of the infinite eta Gaussian Gram

The zero-centered infinite eta Gram has a positive double kernel and is
strictly decreasing in its horizontal tilt.  A Gaussian centered at an
arbitrary ordinate has a different exact arithmetic representation: the same
positive envelope is multiplied by the Fourier phase
`cos (gamma * (u - t))`.

This module derives that localized identity directly for the fixed infinite
eta measure, including integrability and both Fubini exchanges.  It also
formalizes the precise loss of pointwise monotonicity: positive phase keeps
the old direction, while negative phase reverses it.  No phase-coercivity
estimate is assumed or claimed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Gaussian vertical-line norm of the fixed infinite eta Laplace partition,
localized at the ordinate `gamma`. -/
def pairedEtaLocalizedGaussianLaplaceNorm
    (sigma tau gamma : ℝ) : ℝ :=
  ∫ y : ℝ, translatedGaussian tau gamma y *
    Complex.normSq (pairedEtaLaplacePartition
      ((sigma : ℂ) + (y : ℂ) * Complex.I))

/-- The real localized arithmetic kernel.  Its first two factors form the
positive zero-centered kernel; its final cosine is the localization phase. -/
def pairedEtaLocalizedGaussianLaplaceKernel
    (sigma tau gamma : ℝ) (p : ℝ × ℝ) : ℝ :=
  pairedEtaFiniteGaussianLaplaceKernel sigma tau p *
    Real.cos (gamma * (p.2 - p.1))

/-- The localized double-measure Gram representation. -/
def pairedEtaLocalizedGaussianLaplaceGram
    (sigma tau gamma : ℝ) : ℝ :=
  Real.sqrt (Real.pi / tau) *
    ∫ p : ℝ × ℝ,
      pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p
      ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)

/-- At ordinate zero, the localized norm is definitionally the previously
constructed positive Gram norm. -/
theorem pairedEtaLocalizedGaussianLaplaceNorm_zero
    (sigma tau : ℝ) :
    pairedEtaLocalizedGaussianLaplaceNorm sigma tau 0 =
      pairedEtaGaussianLaplaceNorm sigma tau := by
  rfl

/-- At ordinate zero, the localized kernel reduces to the positive kernel. -/
theorem pairedEtaLocalizedGaussianLaplaceKernel_zero
    (sigma tau : ℝ) (p : ℝ × ℝ) :
    pairedEtaLocalizedGaussianLaplaceKernel sigma tau 0 p =
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p := by
  simp [pairedEtaLocalizedGaussianLaplaceKernel]

/-- The localized kernel is dominated in absolute value by the positive
zero-centered kernel. -/
theorem abs_pairedEtaLocalizedGaussianLaplaceKernel_le
    (sigma tau gamma : ℝ) (p : ℝ × ℝ) :
    |pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p| ≤
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p := by
  rw [pairedEtaLocalizedGaussianLaplaceKernel, abs_mul,
    abs_of_pos (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p)]
  exact mul_le_of_le_one_right
    (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p).le
    (Real.abs_cos_le_one _)

/-- The localized kernel is integrable whenever the positive infinite kernel
is integrable. -/
theorem integrable_pairedEtaLocalizedGaussianLaplaceKernel
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    Integrable (pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  apply (integrable_pairedEtaGaussianLaplaceKernel hsigma htau).mono
  · exact (show Continuous
      (pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma) by
        unfold pairedEtaLocalizedGaussianLaplaceKernel
          pairedEtaFiniteGaussianLaplaceKernel
        fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p)]
      exact abs_pairedEtaLocalizedGaussianLaplaceKernel_le sigma tau gamma p

private def pairedEtaLocalizedGaussianLaplaceJoint
    (sigma tau gamma : ℝ) (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (Real.exp (-sigma * (z.2.1 + z.2.2)) : ℂ) *
    complexTranslatedGaussianOscillation tau gamma
      (z.2.2 - z.2.1) z.1

private theorem pairedEtaLocalizedGaussianLaplaceJoint_eq_laplaceProduct
    (sigma tau gamma y t u : ℝ) :
    pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, (t, u)) =
      (translatedGaussian tau gamma y : ℂ) *
        Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t) *
        starRingEnd ℂ
          (Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * u)) := by
  unfold pairedEtaLocalizedGaussianLaplaceJoint
    complexTranslatedGaussianOscillation translatedGaussian
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_add, Complex.conj_ofReal,
    Complex.conj_I, neg_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrable_pairedEtaLocalizedGaussianLaplaceJoint
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    Integrable (pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma)
      (volume.prod (pairedEtaLogMeasure.prod pairedEtaLogMeasure)) := by
  have hy := integrable_translatedGaussian htau gamma
  have hsigmaInt :=
    integrable_rexp_neg_mul_pairedEtaLogMeasure hsigma
  have hmajor := hy.mul_prod (hsigmaInt.mul_prod hsigmaInt)
  apply hmajor.mono
  · exact (show Continuous
      (pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma) by
        unfold pairedEtaLocalizedGaussianLaplaceJoint
          complexTranslatedGaussianOscillation
        fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      apply le_of_eq
      unfold pairedEtaLocalizedGaussianLaplaceJoint
        complexTranslatedGaussianOscillation translatedGaussian
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_exp,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im,
        mul_zero, zero_mul, sub_zero]
      norm_num [Complex.mul_im]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private theorem integral_pairedEtaLocalizedGaussianLaplaceJoint_prod
    {sigma : ℝ} (hsigma : 0 < sigma) (tau gamma y : ℝ) :
    (∫ p : ℝ × ℝ,
        pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      (translatedGaussian tau gamma y : ℂ) *
        pairedEtaLaplacePartition
          ((sigma : ℂ) + (y : ℂ) * Complex.I) *
        starRingEnd ℂ
          (pairedEtaLaplacePartition
            ((sigma : ℂ) + (y : ℂ) * Complex.I)) := by
  have hline : 0 < ((sigma : ℂ) + (y : ℂ) * Complex.I).re := by
    norm_num
    exact hsigma
  rw [show
    (fun p : ℝ × ℝ ↦
      pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)) =
      (fun p : ℝ × ℝ ↦
        (translatedGaussian tau gamma y : ℂ) *
          (Complex.exp
              (-((sigma : ℂ) + (y : ℂ) * Complex.I) * p.1) *
            starRingEnd ℂ
              (Complex.exp
                (-((sigma : ℂ) + (y : ℂ) * Complex.I) * p.2)))) by
      funext p
      rw [pairedEtaLocalizedGaussianLaplaceJoint_eq_laplaceProduct]
      ring]
  rw [integral_const_mul]
  rw [integral_prod_mul
    (μ := pairedEtaLogMeasure)
    (ν := pairedEtaLogMeasure)
    (fun t : ℝ ↦ Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
    (fun u : ℝ ↦ starRingEnd ℂ (Complex.exp
      (-((sigma : ℂ) + (y : ℂ) * Complex.I) * u)))]
  rw [integral_conj]
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hline]
  ring

private theorem integral_pairedEtaLocalizedGaussianLaplaceJoint_volume
    (sigma gamma : ℝ) {tau : ℝ} (htau : 0 < tau)
    (p : ℝ × ℝ) :
    (∫ y : ℝ,
        pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)) =
      (Real.sqrt (Real.pi / tau) : ℂ) *
        (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
        Complex.exp
          (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ)) := by
  unfold pairedEtaLocalizedGaussianLaplaceJoint
  change (∫ y : ℝ,
      (Real.exp (-sigma * (p.1 + p.2)) : ℂ) *
        complexTranslatedGaussianOscillation tau gamma
          (p.2 - p.1) y) = _
  rw [integral_const_mul,
    integral_complexTranslatedGaussianOscillation htau]
  unfold pairedEtaFiniteGaussianLaplaceKernel
  rw [Complex.exp_add]
  norm_num
  ring_nf

/-- The localized Gaussian norm is genuinely integrable at every positive
horizontal tilt and Gaussian time. -/
theorem integrable_pairedEtaLocalizedGaussianLaplaceNorm
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    Integrable (fun y : ℝ ↦ translatedGaussian tau gamma y *
      Complex.normSq (pairedEtaLaplacePartition
        ((sigma : ℂ) + (y : ℂ) * Complex.I))) := by
  have hjoint :=
    integrable_pairedEtaLocalizedGaussianLaplaceJoint hsigma htau gamma
  have houter := hjoint.integral_prod_left
  have hcomplex : Integrable (fun y : ℝ ↦
      ((translatedGaussian tau gamma y *
        Complex.normSq (pairedEtaLaplacePartition
          ((sigma : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ)) := by
    apply houter.congr
    exact Eventually.of_forall fun y => by
      change (∫ p : ℝ × ℝ,
          pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
        ((translatedGaussian tau gamma y *
          Complex.normSq (pairedEtaLaplacePartition
            ((sigma : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ)
      rw [integral_pairedEtaLocalizedGaussianLaplaceJoint_prod hsigma]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
  have hre := hcomplex.re
  rw [RCLike.re_eq_complex_re] at hre
  simpa using hre

/-- Exact phase-sensitive Gaussian--Laplace Gram identity for the fixed
infinite eta measure. -/
theorem pairedEtaLocalizedGaussianLaplaceNorm_eq_gram
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma =
      pairedEtaLocalizedGaussianLaplaceGram sigma tau gamma := by
  let complexKernel : ℝ × ℝ → ℂ := fun p ↦
    (Real.sqrt (Real.pi / tau) : ℂ) *
      (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
      Complex.exp
        (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))
  have hjoint :=
    integrable_pairedEtaLocalizedGaussianLaplaceJoint hsigma htau gamma
  have hcomplexKernel : Integrable complexKernel
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
    apply hjoint.integral_prod_right.congr
    exact Eventually.of_forall fun p => by
      exact integral_pairedEtaLocalizedGaussianLaplaceJoint_volume
        sigma gamma htau p
  have hcomplex :
      (pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma : ℂ) =
        ∫ p : ℝ × ℝ, complexKernel p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
    calc
      (pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma : ℂ) =
          ∫ y : ℝ, ∫ p : ℝ × ℝ,
            pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)
            ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
        unfold pairedEtaLocalizedGaussianLaplaceNorm
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          change ((translatedGaussian tau gamma y *
              Complex.normSq (pairedEtaLaplacePartition
                ((sigma : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ) =
            ∫ p : ℝ × ℝ,
              pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)
              ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)
          rw [integral_pairedEtaLocalizedGaussianLaplaceJoint_prod hsigma]
          push_cast
          rw [Complex.normSq_eq_conj_mul_self]
          ring
      _ = ∫ z : ℝ × (ℝ × ℝ),
            pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma z
            ∂volume.prod (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
        exact integral_integral hjoint
      _ = ∫ p : ℝ × ℝ, ∫ y : ℝ,
            pairedEtaLocalizedGaussianLaplaceJoint sigma tau gamma (y, p)
            ∂volume
            ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
        exact integral_prod_symm _ hjoint
      _ = ∫ p : ℝ × ℝ, complexKernel p
            ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p =>
          integral_pairedEtaLocalizedGaussianLaplaceJoint_volume
            sigma gamma htau p
  calc
    pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma =
        ((pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma : ℂ)).re := by
      simp
    _ = (∫ p : ℝ × ℝ, complexKernel p
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)).re := by
      rw [hcomplex]
    _ = ∫ p : ℝ × ℝ, (complexKernel p).re
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
      have hre := integral_re hcomplexKernel
      rw [RCLike.re_eq_complex_re] at hre
      exact hre.symm
    _ = pairedEtaLocalizedGaussianLaplaceGram sigma tau gamma := by
      unfold pairedEtaLocalizedGaussianLaplaceGram
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only [complexKernel]
        unfold pairedEtaLocalizedGaussianLaplaceKernel
        change
          ((Real.sqrt (Real.pi / tau) : ℂ) *
            (pairedEtaFiniteGaussianLaplaceKernel sigma tau p : ℂ) *
            Complex.exp
              (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))).re =
            Real.sqrt (Real.pi / tau) *
              (pairedEtaFiniteGaussianLaplaceKernel sigma tau p *
                Real.cos (gamma * (p.2 - p.1)))
        rw [show Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ) =
            ((gamma * (p.2 - p.1) : ℝ) : ℂ) * Complex.I by ring]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
          zero_mul, sub_zero]
        ring

/-- The localized infinite Gram is nonnegative even though its arithmetic
kernel need not be pointwise nonnegative. -/
theorem pairedEtaLocalizedGaussianLaplaceGram_nonneg
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (gamma : ℝ) :
    0 ≤ pairedEtaLocalizedGaussianLaplaceGram sigma tau gamma := by
  rw [← pairedEtaLocalizedGaussianLaplaceNorm_eq_gram hsigma htau gamma]
  unfold pairedEtaLocalizedGaussianLaplaceNorm
  apply integral_nonneg
  intro y
  exact mul_nonneg (by
    unfold translatedGaussian
    positivity) (Complex.normSq_nonneg _)

/-- The localized raw energy is the completed symmetric energy divided by
its local completion weight. -/
theorem pairedEtaLocalizedGaussianLaplaceNorm_eq_completedEnergy_div_weight
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (tau gamma : ℝ) :
    pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma =
      ∫ y : ℝ, translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            ((sigma : ℂ) + (y : ℂ) * Complex.I)) := by
  unfold pairedEtaLocalizedGaussianLaplaceNorm
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change translatedGaussian tau gamma y *
        Complex.normSq (pairedEtaLaplacePartition
          ((sigma : ℂ) + (y : ℂ) * Complex.I)) =
      translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            ((sigma : ℂ) + (y : ℂ) * Complex.I))
    rw [normSq_pairedEtaLaplacePartition_eq_completedEnergy_div_weight
      (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- The complementary localized raw energy uses the same completed energy
and the reflected completion weight. -/
theorem
    pairedEtaLocalizedGaussianLaplaceNorm_complementary_eq_completedEnergy_div_weight
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (tau gamma : ℝ) :
    pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma =
      ∫ y : ℝ, translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            (((1 - sigma : ℝ) : ℂ) +
              (y : ℂ) * Complex.I)) := by
  rw [pairedEtaLocalizedGaussianLaplaceNorm_eq_completedEnergy_div_weight
    (sigma := 1 - sigma) (sub_pos.mpr hsigmaOne) (by linarith) tau gamma]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I))
    rw [← one_sub_conj_vertical]
    rw [pairedEtaCompletedLaplaceEnergy_one_sub_conj
      (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- The localized completed-energy-over-weight integrand is genuinely
integrable. -/
theorem integrable_pairedEtaLocalizedCompletedEnergy_div_weight
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) (gamma : ℝ) :
    Integrable (fun y : ℝ ↦ translatedGaussian tau gamma y *
      (pairedEtaCompletedLaplaceEnergy
          ((sigma : ℂ) + (y : ℂ) * Complex.I) /
        pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I))) := by
  apply (integrable_pairedEtaLocalizedGaussianLaplaceNorm
    hsigma htau gamma).congr
  exact Eventually.of_forall fun y => by
    change translatedGaussian tau gamma y *
        Complex.normSq (pairedEtaLaplacePartition
          ((sigma : ℂ) + (y : ℂ) * Complex.I)) =
      translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            ((sigma : ℂ) + (y : ℂ) * Complex.I))
    rw [normSq_pairedEtaLaplacePartition_eq_completedEnergy_div_weight
      (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- The localized completed energy divided by the complementary weight is
also genuinely integrable. -/
theorem integrable_pairedEtaLocalizedCompletedEnergy_div_complementaryWeight
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) (gamma : ℝ) :
    Integrable (fun y : ℝ ↦ translatedGaussian tau gamma y *
      (pairedEtaCompletedLaplaceEnergy
          ((sigma : ℂ) + (y : ℂ) * Complex.I) /
        pairedEtaCompletedLaplaceWeight
          (((1 - sigma : ℝ) : ℂ) +
            (y : ℂ) * Complex.I))) := by
  have hraw := integrable_pairedEtaLocalizedGaussianLaplaceNorm
    (sub_pos.mpr hsigmaOne) htau gamma
  apply hraw.congr
  exact Eventually.of_forall fun y => by
    change translatedGaussian tau gamma y *
        Complex.normSq (pairedEtaLaplacePartition
          (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      translatedGaussian tau gamma y *
        (pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) /
          pairedEtaCompletedLaplaceWeight
            (((1 - sigma : ℝ) : ℂ) + (y : ℂ) * Complex.I))
    rw [normSq_pairedEtaLaplacePartition_eq_completedEnergy_div_weight
      (by simpa using sub_pos.mpr hsigmaOne)
      (by norm_num; linarith)]
    rw [← one_sub_conj_vertical]
    rw [pairedEtaCompletedLaplaceEnergy_one_sub_conj
      (by simpa using hsigma) (by simpa using hsigmaOne)]

/-- Localized reciprocal-completion-weight distortion against the common
completed energy. -/
def pairedEtaLocalizedCompletionWeightDistortionIntegral
    (sigma tau gamma : ℝ) : ℝ :=
  ∫ y : ℝ, translatedGaussian tau gamma y *
    pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I) *
      ((pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I))⁻¹ -
        (pairedEtaCompletedLaplaceWeight
          (((1 - sigma : ℝ) : ℂ) +
            (y : ℂ) * Complex.I))⁻¹)

/-- At center zero, localized distortion is the previously signed global
distortion. -/
theorem pairedEtaLocalizedCompletionWeightDistortionIntegral_zero
    (sigma tau : ℝ) :
    pairedEtaLocalizedCompletionWeightDistortionIntegral sigma tau 0 =
      pairedEtaCompletionWeightDistortionIntegral sigma tau := by
  rfl

/-- The localized completion distortion is exactly the difference of the
two complementary localized raw norms. -/
theorem
    pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) (gamma : ℝ) :
    pairedEtaLocalizedCompletionWeightDistortionIntegral sigma tau gamma =
      pairedEtaLocalizedGaussianLaplaceNorm sigma tau gamma -
        pairedEtaLocalizedGaussianLaplaceNorm (1 - sigma) tau gamma := by
  rw [pairedEtaLocalizedGaussianLaplaceNorm_eq_completedEnergy_div_weight
      hsigma hsigmaOne tau gamma,
    pairedEtaLocalizedGaussianLaplaceNorm_complementary_eq_completedEnergy_div_weight
      hsigma hsigmaOne tau gamma,
    ← integral_sub
      (integrable_pairedEtaLocalizedCompletedEnergy_div_weight
        hsigma hsigmaOne htau gamma)
      (integrable_pairedEtaLocalizedCompletedEnergy_div_complementaryWeight
        hsigma hsigmaOne htau gamma)]
  unfold pairedEtaLocalizedCompletionWeightDistortionIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    change translatedGaussian tau gamma y *
        pairedEtaCompletedLaplaceEnergy
            ((sigma : ℂ) + (y : ℂ) * Complex.I) *
          ((pairedEtaCompletedLaplaceWeight
              ((sigma : ℂ) + (y : ℂ) * Complex.I))⁻¹ -
            (pairedEtaCompletedLaplaceWeight
              (((1 - sigma : ℝ) : ℂ) +
                (y : ℂ) * Complex.I))⁻¹) =
      translatedGaussian tau gamma y *
          (pairedEtaCompletedLaplaceEnergy
              ((sigma : ℂ) + (y : ℂ) * Complex.I) /
            pairedEtaCompletedLaplaceWeight
              ((sigma : ℂ) + (y : ℂ) * Complex.I)) -
        translatedGaussian tau gamma y *
          (pairedEtaCompletedLaplaceEnergy
              ((sigma : ℂ) + (y : ℂ) * Complex.I) /
            pairedEtaCompletedLaplaceWeight
              (((1 - sigma : ℝ) : ℂ) +
                (y : ℂ) * Complex.I))
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring

/-- Exact arithmetic form of the localized completion distortion: it is the
difference of two oscillatory kernels over the fixed positive product
measure. -/
theorem
    pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_kernelDifference
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) (gamma : ℝ) :
    pairedEtaLocalizedCompletionWeightDistortionIntegral sigma tau gamma =
      Real.sqrt (Real.pi / tau) *
        ∫ p : ℝ × ℝ,
          (pairedEtaLocalizedGaussianLaplaceKernel sigma tau gamma p -
            pairedEtaLocalizedGaussianLaplaceKernel
              (1 - sigma) tau gamma p)
          ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  rw [
    pairedEtaLocalizedCompletionWeightDistortionIntegral_eq_norm_sub_complementary
      hsigma hsigmaOne htau gamma,
    pairedEtaLocalizedGaussianLaplaceNorm_eq_gram hsigma htau gamma,
    pairedEtaLocalizedGaussianLaplaceNorm_eq_gram
      (sub_pos.mpr hsigmaOne) htau gamma]
  unfold pairedEtaLocalizedGaussianLaplaceGram
  rw [← mul_sub, ← integral_sub
    (integrable_pairedEtaLocalizedGaussianLaplaceKernel hsigma htau gamma)
    (integrable_pairedEtaLocalizedGaussianLaplaceKernel
      (sub_pos.mpr hsigmaOne) htau gamma)]

/-- On a strictly positive Fourier phase, increasing the horizontal tilt
strictly decreases the localized kernel. -/
theorem pairedEtaLocalizedGaussianLaplaceKernel_strictAnti_sigma_of_cos_pos
    {sigma₁ sigma₂ tau gamma : ℝ} (hsigma : sigma₁ < sigma₂)
    {p : ℝ × ℝ} (hp : 0 < p.1 + p.2)
    (hcos : 0 < Real.cos (gamma * (p.2 - p.1))) :
    pairedEtaLocalizedGaussianLaplaceKernel sigma₂ tau gamma p <
      pairedEtaLocalizedGaussianLaplaceKernel sigma₁ tau gamma p := by
  unfold pairedEtaLocalizedGaussianLaplaceKernel
  exact mul_lt_mul_of_pos_right
    (pairedEtaGaussianLaplaceKernel_strictAnti_sigma hsigma hp) hcos

/-- On a strictly negative Fourier phase, increasing the horizontal tilt
strictly increases the localized kernel: the zero-centered monotonicity
direction reverses pointwise. -/
theorem pairedEtaLocalizedGaussianLaplaceKernel_strictMono_sigma_of_cos_neg
    {sigma₁ sigma₂ tau gamma : ℝ} (hsigma : sigma₁ < sigma₂)
    {p : ℝ × ℝ} (hp : 0 < p.1 + p.2)
    (hcos : Real.cos (gamma * (p.2 - p.1)) < 0) :
    pairedEtaLocalizedGaussianLaplaceKernel sigma₁ tau gamma p <
      pairedEtaLocalizedGaussianLaplaceKernel sigma₂ tau gamma p := by
  unfold pairedEtaLocalizedGaussianLaplaceKernel
  exact mul_lt_mul_of_neg_right
    (pairedEtaGaussianLaplaceKernel_strictAnti_sigma hsigma hp) hcos

/-- At a nontrivial zeta zero, the localized vertical energy integrand
vanishes at the center ordinate itself. -/
theorem pairedEtaLocalizedGaussianLaplaceIntegrand_center_eq_zero
    (rho : NontrivialZetaZero) (tau : ℝ) :
    translatedGaussian tau rho.1.im rho.1.im *
        Complex.normSq (pairedEtaLaplacePartition
          ((rho.1.re : ℂ) + (rho.1.im : ℂ) * Complex.I)) = 0 := by
  rw [Complex.re_add_im rho.1]
  rw [pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho]
  simp

end

end RiemannGaussian
