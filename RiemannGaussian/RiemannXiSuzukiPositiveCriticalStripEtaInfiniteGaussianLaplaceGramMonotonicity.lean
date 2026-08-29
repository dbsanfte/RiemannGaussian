import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGram

/-!
# Monotonicity and the global completion-distortion sign

The fixed eta logarithmic measure lives in strictly positive time.  Therefore
the infinite positive Gaussian Gram kernel is antitone in its horizontal
Laplace tilt.  Combining this unconditional order with the exact
completion-weight distortion identity proves the global distortion integral
has the expected sign on each side of the critical line.

This sign is not a zero-location theorem.  It uses the Gaussian centered at
ordinate zero.  Translating the Gaussian to a zero's ordinate inserts an
oscillatory Fourier phase into the arithmetic double kernel, where positivity
is no longer automatic.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The fixed eta logarithmic measure is concentrated in strictly positive
time. -/
theorem ae_pairedEtaLogMeasure_pos :
    ∀ᵐ t : ℝ ∂pairedEtaLogMeasure, 0 < t := by
  rw [pairedEtaLogMeasure]
  filter_upwards [ae_restrict_mem measurableSet_pairedEtaLogSupport]
    with t ht
  exact pairedEtaLogSupport_subset_Ioi_zero ht

/-- The fixed eta logarithmic measure is nonzero. -/
theorem pairedEtaLogMeasure_ne_zero : pairedEtaLogMeasure ≠ 0 := by
  intro hzero
  have hmass := pairedEtaTiltedCosineMoment_zero_pos 1 (by norm_num)
  unfold pairedEtaTiltedCosineMoment at hmass
  rw [hzero] at hmass
  simp at hmass

/-- The fixed eta logarithmic measure has nontrivial almost-everywhere
filter. -/
instance pairedEtaLogMeasure.instNeZero : NeZero pairedEtaLogMeasure :=
  ⟨pairedEtaLogMeasure_ne_zero⟩

/-- The product of the fixed eta logarithmic measure with itself is
nonzero. -/
theorem pairedEtaLogMeasure_prod_ne_zero :
    pairedEtaLogMeasure.prod pairedEtaLogMeasure ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, ← univ_prod_univ, Measure.prod_prod]
  exact mul_ne_zero
    (Measure.measure_univ_ne_zero.2 pairedEtaLogMeasure_ne_zero)
    (Measure.measure_univ_ne_zero.2 pairedEtaLogMeasure_ne_zero)

/-- The product eta measure has nontrivial almost-everywhere filter. -/
instance instNeZeroPairedEtaLogMeasureProd :
    NeZero (pairedEtaLogMeasure.prod pairedEtaLogMeasure) :=
  ⟨pairedEtaLogMeasure_prod_ne_zero⟩

/-- The product eta measure is concentrated where both logarithmic times are
strictly positive. -/
theorem ae_pairedEtaLogMeasure_prod_pos :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure),
      0 < p.1 ∧ 0 < p.2 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
    change MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
    exact measurableSet_Ioi.prod measurableSet_Ioi
  apply (Measure.ae_prod_iff_ae_ae hmeas).2
  filter_upwards [ae_pairedEtaLogMeasure_pos] with t ht
  filter_upwards [ae_pairedEtaLogMeasure_pos] with u hu
  exact ⟨ht, hu⟩

/-- At nonnegative total logarithmic time, increasing the horizontal tilt
decreases the positive Gaussian--Laplace kernel. -/
theorem pairedEtaGaussianLaplaceKernel_antitone_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma : sigma₁ ≤ sigma₂)
    {p : ℝ × ℝ} (hp : 0 ≤ p.1 + p.2) :
    pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p ≤
      pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p := by
  unfold pairedEtaFiniteGaussianLaplaceKernel
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    calc
      -sigma₂ * (p.1 + p.2) = -(sigma₂ * (p.1 + p.2)) := by ring
      _ ≤ -(sigma₁ * (p.1 + p.2)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hsigma hp)
      _ = -sigma₁ * (p.1 + p.2) := by ring
  · exact (Real.exp_pos _).le

/-- At strictly positive total logarithmic time, increasing the horizontal
tilt strictly decreases the positive Gaussian--Laplace kernel. -/
theorem pairedEtaGaussianLaplaceKernel_strictAnti_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma : sigma₁ < sigma₂)
    {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p <
      pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p := by
  unfold pairedEtaFiniteGaussianLaplaceKernel
  apply mul_lt_mul_of_pos_right
  · apply Real.exp_lt_exp.mpr
    calc
      -sigma₂ * (p.1 + p.2) = -(sigma₂ * (p.1 + p.2)) := by ring
      _ < -(sigma₁ * (p.1 + p.2)) :=
        neg_lt_neg (mul_lt_mul_of_pos_right hsigma hp)
      _ = -sigma₁ * (p.1 + p.2) := by ring
  · exact Real.exp_pos _

/-- The infinite positive-kernel integral is antitone in every positive
horizontal tilt. -/
theorem integral_pairedEtaGaussianLaplaceKernel_antitone_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma₁ : 0 < sigma₁)
    (hsigma : sigma₁ ≤ sigma₂) (htau : 0 < tau) :
    (∫ p : ℝ × ℝ,
        pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) ≤
      ∫ p : ℝ × ℝ,
        pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  have hsigma₂ : 0 < sigma₂ := hsigma₁.trans_le hsigma
  apply integral_mono_ae
    (integrable_pairedEtaGaussianLaplaceKernel hsigma₂ htau)
    (integrable_pairedEtaGaussianLaplaceKernel hsigma₁ htau)
  filter_upwards [ae_pairedEtaLogMeasure_prod_pos] with p hp
  exact pairedEtaGaussianLaplaceKernel_antitone_sigma hsigma
    (add_nonneg hp.1.le hp.2.le)

/-- The infinite positive-kernel integral is strictly antitone in every
positive horizontal tilt. -/
theorem integral_pairedEtaGaussianLaplaceKernel_strictAnti_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma₁ : 0 < sigma₁)
    (hsigma : sigma₁ < sigma₂) (htau : 0 < tau) :
    (∫ p : ℝ × ℝ,
        pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) <
      ∫ p : ℝ × ℝ,
        pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  have hsigma₂ : 0 < sigma₂ := hsigma₁.trans hsigma
  have hf := integrable_pairedEtaGaussianLaplaceKernel hsigma₂ htau
  have hg := integrable_pairedEtaGaussianLaplaceKernel hsigma₁ htau
  have hle : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure),
      pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p ≤
        pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p := by
    filter_upwards [ae_pairedEtaLogMeasure_prod_pos] with p hp
    exact (pairedEtaGaussianLaplaceKernel_strictAnti_sigma hsigma
      (add_pos hp.1 hp.2)).le
  have hlt : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure),
      pairedEtaFiniteGaussianLaplaceKernel sigma₂ tau p <
        pairedEtaFiniteGaussianLaplaceKernel sigma₁ tau p := by
    filter_upwards [ae_pairedEtaLogMeasure_prod_pos] with p hp
    exact pairedEtaGaussianLaplaceKernel_strictAnti_sigma hsigma
      (add_pos hp.1 hp.2)
  have hmono := integral_mono_ae hf hg hle
  apply lt_of_le_of_ne hmono
  intro heq
  have haeEq := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  have hfalse : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure), False := by
    filter_upwards [haeEq, hlt] with p heqP hltP
    exact (ne_of_lt hltP) heqP
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- The raw infinite eta Gaussian Gram norm is antitone in its positive
horizontal tilt. -/
theorem pairedEtaGaussianLaplaceNorm_antitone_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma₁ : 0 < sigma₁)
    (hsigma : sigma₁ ≤ sigma₂) (htau : 0 < tau) :
    pairedEtaGaussianLaplaceNorm sigma₂ tau ≤
      pairedEtaGaussianLaplaceNorm sigma₁ tau := by
  have hsigma₂ : 0 < sigma₂ := hsigma₁.trans_le hsigma
  rw [pairedEtaGaussianLaplaceNorm_eq_gram hsigma₂ htau,
    pairedEtaGaussianLaplaceNorm_eq_gram hsigma₁ htau]
  unfold pairedEtaGaussianLaplaceGram
  exact mul_le_mul_of_nonneg_left
    (integral_pairedEtaGaussianLaplaceKernel_antitone_sigma
      hsigma₁ hsigma htau)
    (Real.sqrt_nonneg _)

/-- The raw infinite eta Gaussian Gram norm is strictly antitone in every
positive horizontal tilt. -/
theorem pairedEtaGaussianLaplaceNorm_strictAnti_sigma
    {sigma₁ sigma₂ tau : ℝ} (hsigma₁ : 0 < sigma₁)
    (hsigma : sigma₁ < sigma₂) (htau : 0 < tau) :
    pairedEtaGaussianLaplaceNorm sigma₂ tau <
      pairedEtaGaussianLaplaceNorm sigma₁ tau := by
  have hsigma₂ : 0 < sigma₂ := hsigma₁.trans hsigma
  rw [pairedEtaGaussianLaplaceNorm_eq_gram hsigma₂ htau,
    pairedEtaGaussianLaplaceNorm_eq_gram hsigma₁ htau]
  unfold pairedEtaGaussianLaplaceGram
  apply mul_lt_mul_of_pos_left
  · exact integral_pairedEtaGaussianLaplaceKernel_strictAnti_sigma
      hsigma₁ hsigma htau
  · exact Real.sqrt_pos.2 (div_pos Real.pi_pos htau)

/-- The reciprocal-completion-weight distortion against the common completed
energy. -/
def pairedEtaCompletionWeightDistortionIntegral
    (sigma tau : ℝ) : ℝ :=
  ∫ y : ℝ, translatedGaussian tau 0 y *
    pairedEtaCompletedLaplaceEnergy
        ((sigma : ℂ) + (y : ℂ) * Complex.I) *
      ((pairedEtaCompletedLaplaceWeight
          ((sigma : ℂ) + (y : ℂ) * Complex.I))⁻¹ -
        (pairedEtaCompletedLaplaceWeight
          (((1 - sigma : ℝ) : ℂ) +
            (y : ℂ) * Complex.I))⁻¹)

/-- The distortion integral is exactly the raw complementary Gram
difference. -/
theorem pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    pairedEtaCompletionWeightDistortionIntegral sigma tau =
      pairedEtaGaussianLaplaceNorm sigma tau -
        pairedEtaGaussianLaplaceNorm (1 - sigma) tau := by
  exact
    (pairedEtaGaussianLaplaceNorm_sub_complementary_eq_completionWeightDistortion
      hsigma hsigmaOne htau).symm

/-- On the right of the critical line, the global completion-weight
distortion integral is nonpositive. -/
theorem pairedEtaCompletionWeightDistortionIntegral_nonpos_of_half_le
    {sigma tau : ℝ} (hhalf : 1 / 2 ≤ sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    pairedEtaCompletionWeightDistortionIntegral sigma tau ≤ 0 := by
  have hsigma : 0 < sigma := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hpartner : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have horder : 1 - sigma ≤ sigma := by linarith
  have hmono := pairedEtaGaussianLaplaceNorm_antitone_sigma
    hpartner horder htau
  rw [pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    hsigma hsigmaOne htau]
  exact sub_nonpos.mpr hmono

/-- On the left of the critical line, the global completion-weight
distortion integral is nonnegative. -/
theorem pairedEtaCompletionWeightDistortionIntegral_nonneg_of_le_half
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hhalf : sigma ≤ 1 / 2)
    (htau : 0 < tau) :
    0 ≤ pairedEtaCompletionWeightDistortionIntegral sigma tau := by
  have hsigmaOne : sigma < 1 := hhalf.trans_lt (by norm_num)
  have hpartner : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have horder : sigma ≤ 1 - sigma := by linarith
  have hmono := pairedEtaGaussianLaplaceNorm_antitone_sigma
    hsigma horder htau
  rw [pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    hsigma hsigmaOne htau]
  exact sub_nonneg.mpr hmono

/-- Strictly right of the critical line, the global completion-weight
distortion integral is negative. -/
theorem pairedEtaCompletionWeightDistortionIntegral_neg_of_half_lt
    {sigma tau : ℝ} (hhalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    pairedEtaCompletionWeightDistortionIntegral sigma tau < 0 := by
  have hsigma : 0 < sigma := (by norm_num : (0 : ℝ) < 1 / 2).trans hhalf
  have hpartner : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have horder : 1 - sigma < sigma := by linarith
  have hmono := pairedEtaGaussianLaplaceNorm_strictAnti_sigma
    hpartner horder htau
  rw [pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    hsigma hsigmaOne htau]
  exact sub_neg.mpr hmono

/-- Strictly left of the critical line, the global completion-weight
distortion integral is positive. -/
theorem pairedEtaCompletionWeightDistortionIntegral_pos_of_lt_half
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hhalf : sigma < 1 / 2)
    (htau : 0 < tau) :
    0 < pairedEtaCompletionWeightDistortionIntegral sigma tau := by
  have hsigmaOne : sigma < 1 := hhalf.trans (by norm_num)
  have horder : sigma < 1 - sigma := by linarith
  have hmono := pairedEtaGaussianLaplaceNorm_strictAnti_sigma
    hsigma horder htau
  rw [pairedEtaCompletionWeightDistortionIntegral_eq_norm_sub_complementary
    hsigma hsigmaOne htau]
  exact sub_pos.mpr hmono

/-- On the critical line, the global completion-weight distortion integral
vanishes identically. -/
theorem pairedEtaCompletionWeightDistortionIntegral_half (tau : ℝ) :
    pairedEtaCompletionWeightDistortionIntegral (1 / 2) tau = 0 := by
  norm_num [pairedEtaCompletionWeightDistortionIntegral]

/-- In the open critical strip, the global completion-weight distortion is
negative exactly to the right of the critical line. -/
theorem pairedEtaCompletionWeightDistortionIntegral_neg_iff_half_lt
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    pairedEtaCompletionWeightDistortionIntegral sigma tau < 0 ↔
      1 / 2 < sigma := by
  constructor
  · intro hneg
    by_contra hhalf
    exact (not_lt_of_ge
      (pairedEtaCompletionWeightDistortionIntegral_nonneg_of_le_half
        hsigma (le_of_not_gt hhalf) htau)) hneg
  · intro hhalf
    exact pairedEtaCompletionWeightDistortionIntegral_neg_of_half_lt
      hhalf hsigmaOne htau

/-- In the open critical strip, the global completion-weight distortion
vanishes exactly on the critical line. -/
theorem pairedEtaCompletionWeightDistortionIntegral_eq_zero_iff_eq_half
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    pairedEtaCompletionWeightDistortionIntegral sigma tau = 0 ↔
      sigma = 1 / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy sigma (1 / 2) with hleft | hhalf | hright
    · have hpos := pairedEtaCompletionWeightDistortionIntegral_pos_of_lt_half
        hsigma hleft htau
      linarith
    · exact hhalf
    · have hneg := pairedEtaCompletionWeightDistortionIntegral_neg_of_half_lt
        hright hsigmaOne htau
      linarith
  · rintro rfl
    exact pairedEtaCompletionWeightDistortionIntegral_half tau

/-- In the open critical strip, the global completion-weight distortion is
positive exactly to the left of the critical line. -/
theorem pairedEtaCompletionWeightDistortionIntegral_pos_iff_lt_half
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    0 < pairedEtaCompletionWeightDistortionIntegral sigma tau ↔
      sigma < 1 / 2 := by
  constructor
  · intro hpos
    by_contra hhalf
    exact (not_lt_of_ge
      (pairedEtaCompletionWeightDistortionIntegral_nonpos_of_half_le
        (le_of_not_gt hhalf) hsigmaOne htau)) hpos
  · intro hhalf
    exact pairedEtaCompletionWeightDistortionIntegral_pos_of_lt_half
      hsigma hhalf htau

/-- Complete sign characterization of the global infinite eta
completion-weight distortion in the open critical strip. -/
theorem pairedEtaCompletionWeightDistortionIntegral_sign_characterization
    {sigma tau : ℝ} (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (htau : 0 < tau) :
    (pairedEtaCompletionWeightDistortionIntegral sigma tau < 0 ↔
      1 / 2 < sigma) ∧
    (pairedEtaCompletionWeightDistortionIntegral sigma tau = 0 ↔
      sigma = 1 / 2) ∧
    (0 < pairedEtaCompletionWeightDistortionIntegral sigma tau ↔
      sigma < 1 / 2) := by
  exact ⟨
    pairedEtaCompletionWeightDistortionIntegral_neg_iff_half_lt
      hsigma hsigmaOne htau,
    pairedEtaCompletionWeightDistortionIntegral_eq_zero_iff_eq_half
      hsigma hsigmaOne htau,
    pairedEtaCompletionWeightDistortionIntegral_pos_iff_lt_half
      hsigma hsigmaOne htau⟩

end

end RiemannGaussian
