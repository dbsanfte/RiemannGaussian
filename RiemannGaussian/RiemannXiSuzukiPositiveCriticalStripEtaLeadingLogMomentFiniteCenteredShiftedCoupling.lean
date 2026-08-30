import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredCompletedResidual

/-!
# Shifted-measure coupling for the centered finite eta residual

Translate the discarded eta support at cutoff `N` by its first arithmetic
endpoint

`a_N = log (2N+1)`.

The resulting measure is supported on the positive half-line and is shared by
the two complementary horizontal tilts at a nontrivial zero.  This module
proves absolute integrability and factors every centered tail exactly into:

* real decay at the cutoff;
* a unit complex oscillation at the cutoff;
* a Fourier--Laplace moment of the translated positive measure.

Conjugation reverses the Fourier frequency.  Consequently the completed
partner residual is a unit phase times one explicit coupled core involving
the complementary tilts `rho.re` and `1-rho.re` on the same measure.  The only
remaining cutoff oscillation inside that core is the relative phase
`exp (2 * I * rho.im * a_N)`.  This is an exact symmetry-aware reduction, not
a zero-location theorem: controlling the coupled core still requires new
eta-specific arithmetic rigidity.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The first logarithmic endpoint `log (2N+1)` of the discarded eta support
at cutoff `N`. -/
def pairedEtaLogTailCutoff (N : ℕ) : ℝ :=
  Real.log (((2 * N + 1 : ℕ) : ℝ))

/-- The eta tail measure translated so that its first excluded arithmetic
endpoint is the origin. -/
def pairedEtaShiftedLogTailMeasure (N : ℕ) : Measure ℝ :=
  Measure.map (fun t : ℝ ↦ t - pairedEtaLogTailCutoff N)
    (pairedEtaLogTailMeasure N)

/-- The order-`k` complex Laplace moment of the translated eta tail measure. -/
def pairedEtaShiftedLogTailLaplaceMoment
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
    ∂pairedEtaShiftedLogTailMeasure N

/-- The translated order-`k` eta tail moment with its real decay and Fourier
oscillation displayed as separate factors. -/
def pairedEtaShiftedLogTailFourierMoment
    (k : ℕ) (sigma gamma : ℝ) (N : ℕ) : ℂ :=
  ∫ u : ℝ,
    (u : ℂ) ^ k * (Real.exp (-sigma * u) : ℂ) *
      Complex.exp (-((gamma * u : ℝ) : ℂ) * I)
    ∂pairedEtaShiftedLogTailMeasure N

/-- The unit oscillation contributed by the arithmetic cutoff itself. -/
def pairedEtaLogTailCutoffOscillation (gamma : ℝ) (N : ℕ) : ℂ :=
  Complex.exp
    (-((gamma * pairedEtaLogTailCutoff N : ℝ) : ℂ) * I)

/-- The relative cutoff oscillation left after conjugating one member of a
same-ordinate complementary pair and extracting the common unit phase. -/
def pairedEtaLogTailCutoffRelativeOscillation
    (gamma : ℝ) (N : ℕ) : ℂ :=
  Complex.exp
    (((2 * gamma * pairedEtaLogTailCutoff N : ℝ) : ℂ) * I)

/-- Translation by the negative cutoff is a measurable embedding. -/
theorem measurableEmbedding_sub_pairedEtaLogTailCutoff (N : ℕ) :
    MeasurableEmbedding
      (fun t : ℝ ↦ t - pairedEtaLogTailCutoff N) := by
  let e : ℝ ≃ₜ ℝ :=
    Homeomorph.addRight (-pairedEtaLogTailCutoff N)
  simpa [e, sub_eq_add_neg] using
    e.isClosedEmbedding.measurableEmbedding

/-- Almost every point of the shifted eta tail measure is strictly positive. -/
theorem ae_zero_lt_pairedEtaShiftedLogTailMeasure (N : ℕ) :
    ∀ᵐ u ∂pairedEtaShiftedLogTailMeasure N, 0 < u := by
  unfold pairedEtaShiftedLogTailMeasure
  rw [(measurableEmbedding_sub_pairedEtaLogTailCutoff N).ae_map_iff]
  filter_upwards
    [ae_restrict_mem (measurableSet_pairedEtaLogTailSupport N)] with t ht
  have hta : pairedEtaLogTailCutoff N < t := by
    simpa [pairedEtaLogTailCutoff] using
      (pairedEtaLogTailSupport_subset_Ioi_log_odd N ht)
  exact sub_pos.mpr hta

/-- The cutoff-centered complex tail integrand is absolutely integrable on
the original discarded eta support whenever the horizontal tilt is positive. -/
theorem integrable_pairedEtaLogLaplaceMomentCutoffCenteredTail_integrand
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun t : ℝ ↦
      (((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k) *
        Complex.exp (-s * t))
      (pairedEtaLogTailMeasure N) := by
  let a := pairedEtaLogTailCutoff N
  have hsum : Integrable (fun t : ℝ ↦
      ∑ j ∈ Finset.range (k + 1),
        (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j)) *
          ((t : ℂ) ^ j * Complex.exp (-s * t)))
      (pairedEtaLogTailMeasure N) := by
    apply integrable_finsetSum
    intro j hj
    exact (integrable_pairedEtaLogLaplaceMoment_tail j hs N).const_mul
      (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j))
  apply hsum.congr
  filter_upwards with t
  have hpoly : (((t - a : ℝ) : ℂ) ^ k) =
      ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          (t : ℂ) ^ j := by
    rw [show ((t - a : ℝ) : ℂ) = (t : ℂ) + -(a : ℂ) by
      push_cast
      ring, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hpoly, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The complex Laplace integrand is absolutely integrable on the shifted eta
tail measure throughout the positive half-plane. -/
theorem integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun u : ℝ ↦
      (u : ℂ) ^ k * Complex.exp (-s * u))
      (pairedEtaShiftedLogTailMeasure N) := by
  rw [pairedEtaShiftedLogTailMeasure,
    (measurableEmbedding_sub_pairedEtaLogTailCutoff N).integrable_map_iff]
  have hcenter :=
    integrable_pairedEtaLogLaplaceMomentCutoffCenteredTail_integrand k hs N
  have hscaled := hcenter.const_mul
    (Complex.exp (s * (pairedEtaLogTailCutoff N : ℂ)))
  apply hscaled.congr
  filter_upwards with t
  change Complex.exp (s * (pairedEtaLogTailCutoff N : ℂ)) *
      ((((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k) *
        Complex.exp (-s * t)) =
    (((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k) *
      Complex.exp
        (-s * ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ))
  rw [show -s * ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) =
      s * (pairedEtaLogTailCutoff N : ℂ) + -s * (t : ℂ) by
    push_cast
    ring,
    Complex.exp_add]
  ring

/-- Translating the discarded support factors the cutoff exponential out of
the literal centered eta tail exactly. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted
    (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail k s N =
      Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
        pairedEtaShiftedLogTailLaplaceMoment k s N := by
  unfold pairedEtaLogLaplaceMomentCutoffCenteredTail
    pairedEtaShiftedLogTailLaplaceMoment pairedEtaShiftedLogTailMeasure
  change (∫ t : ℝ,
      (((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k) *
        Complex.exp (-s * t)
        ∂pairedEtaLogTailMeasure N) =
    Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
      ∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
        ∂Measure.map
          (fun t : ℝ ↦ t - pairedEtaLogTailCutoff N)
          (pairedEtaLogTailMeasure N)
  rw [(measurableEmbedding_sub_pairedEtaLogTailCutoff N).integral_map]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hexp : Complex.exp (-s * (t : ℂ)) =
      Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
        Complex.exp
          (-s * ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ)) := by
    rw [show -s * (t : ℂ) =
        -s * (pairedEtaLogTailCutoff N : ℂ) +
          -s * ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) by
      push_cast
      ring,
      Complex.exp_add]
  rw [hexp]
  ring

/-- A complex exponential at a real argument is its real decay times its
unit imaginary oscillation. -/
theorem complex_exp_neg_mul_real_eq_decay_mul_oscillation
    (s : ℂ) (a : ℝ) :
    Complex.exp (-s * (a : ℂ)) =
      (Real.exp (-s.re * a) : ℂ) *
        Complex.exp (-((s.im * a : ℝ) : ℂ) * I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im]

/-- The separated real-decay/Fourier integrand is absolutely integrable for
every positive real tilt and every real frequency. -/
theorem integrable_pairedEtaShiftedLogTailFourierMoment_integrand
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (gamma : ℝ) (N : ℕ) :
    Integrable (fun u : ℝ ↦
      (u : ℂ) ^ k * (Real.exp (-sigma * u) : ℂ) *
        Complex.exp (-((gamma * u : ℝ) : ℂ) * I))
      (pairedEtaShiftedLogTailMeasure N) := by
  let s : ℂ := (sigma : ℂ) + (gamma : ℂ) * I
  have hs : 0 < s.re := by simpa [s] using hsigma
  have hint :=
    integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand k hs N
  apply hint.congr
  filter_upwards with u
  rw [complex_exp_neg_mul_real_eq_decay_mul_oscillation]
  simp only [s, add_re, ofReal_re, mul_re, mul_im, I_re, I_im,
    ofReal_im, mul_zero, mul_one, sub_self, add_zero, zero_add, add_im]
  ring

/-- Separating real and imaginary coordinates identifies the shifted complex
Laplace moment with the shifted Fourier--Laplace moment. -/
theorem pairedEtaShiftedLogTailLaplaceMoment_eq_fourierMoment
    (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaShiftedLogTailLaplaceMoment k s N =
      pairedEtaShiftedLogTailFourierMoment k s.re s.im N := by
  unfold pairedEtaShiftedLogTailLaplaceMoment
    pairedEtaShiftedLogTailFourierMoment
  apply integral_congr_ae
  filter_upwards with u
  rw [complex_exp_neg_mul_real_eq_decay_mul_oscillation]
  ring

/-- The literal centered eta tail is exactly cutoff decay times cutoff phase
times a Fourier--Laplace moment of the shifted positive measure. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted
    (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail k s N =
      (Real.exp (-s.re * pairedEtaLogTailCutoff N) : ℂ) *
        pairedEtaLogTailCutoffOscillation s.im N *
          pairedEtaShiftedLogTailFourierMoment k s.re s.im N := by
  rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted,
    complex_exp_neg_mul_real_eq_decay_mul_oscillation,
    pairedEtaShiftedLogTailLaplaceMoment_eq_fourierMoment]
  rfl

/-- The cutoff oscillation has unit norm. -/
theorem norm_pairedEtaLogTailCutoffOscillation
    (gamma : ℝ) (N : ℕ) :
    ‖pairedEtaLogTailCutoffOscillation gamma N‖ = 1 := by
  unfold pairedEtaLogTailCutoffOscillation
  rw [show -((gamma * pairedEtaLogTailCutoff N : ℝ) : ℂ) * I =
      ((-gamma * pairedEtaLogTailCutoff N : ℝ) : ℂ) * I by
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The relative cutoff oscillation also has unit norm. -/
theorem norm_pairedEtaLogTailCutoffRelativeOscillation
    (gamma : ℝ) (N : ℕ) :
    ‖pairedEtaLogTailCutoffRelativeOscillation gamma N‖ = 1 := by
  unfold pairedEtaLogTailCutoffRelativeOscillation
  exact Complex.norm_exp_ofReal_mul_I _

/-- Conjugating the cutoff phase produces the original phase times the
explicit doubled relative phase. -/
theorem star_pairedEtaLogTailCutoffOscillation
    (gamma : ℝ) (N : ℕ) :
    starRingEnd ℂ (pairedEtaLogTailCutoffOscillation gamma N) =
      pairedEtaLogTailCutoffOscillation gamma N *
        pairedEtaLogTailCutoffRelativeOscillation gamma N := by
  unfold pairedEtaLogTailCutoffOscillation
    pairedEtaLogTailCutoffRelativeOscillation
  rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, conj_ofReal, conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Conjugating a shifted Fourier--Laplace moment reverses its frequency and
leaves its positive real tilt unchanged. -/
theorem star_pairedEtaShiftedLogTailFourierMoment
    (k : ℕ) (sigma gamma : ℝ) (N : ℕ) :
    starRingEnd ℂ
        (pairedEtaShiftedLogTailFourierMoment k sigma gamma N) =
      pairedEtaShiftedLogTailFourierMoment k sigma (-gamma) N := by
  unfold pairedEtaShiftedLogTailFourierMoment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  rw [map_mul, map_mul, map_pow, ← Complex.exp_conj]
  simp only [map_neg, map_mul, conj_ofReal, conj_I]
  congr 1
  push_cast
  ring_nf

/-- At a nontrivial zero, its centered leading tail is the shifted-measure
moment at real tilt `rho.re` and frequency `rho.im`. -/
theorem pairedEtaLeadingLogCutoffCenteredTail_eq_shifted
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail
        (analyticZetaZeroMultiplicity rho) rho.1 N =
      (Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) : ℂ) *
        pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaShiftedLogTailFourierMoment
            (analyticZetaZeroMultiplicity rho)
            rho.1.re rho.1.im N := by
  exact
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted
      (analyticZetaZeroMultiplicity rho) rho.1 N

/-- At the same-ordinate reflected zero, the centered leading tail uses the
complementary real tilt `1-rho.re` on exactly the same shifted measure and at
exactly the same Fourier frequency. -/
theorem pairedEtaLeadingLogCutoffCenteredPartnerTail_eq_shifted
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N =
      (Real.exp
          (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) : ℂ) *
        pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaShiftedLogTailFourierMoment
            (analyticZetaZeroMultiplicity rho)
            (1 - rho.1.re) rho.1.im N := by
  simpa only [NontrivialZetaZero.conjugatePartner_coe,
    Complex.sub_re, Complex.one_re, Complex.conj_re,
    Complex.sub_im, Complex.one_im, Complex.conj_im,
    zero_sub, neg_neg] using
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.conjugatePartner rho).1 N

/-- The symmetry-aware shifted core of the completed centered finite
residual.  Its two Fourier--Laplace moments use complementary real tilts on
the same positive shifted eta measure; its only relative cutoff phase is the
doubled oscillation displayed in the second term. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  -(pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (Real.exp
        (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) : ℂ) *
      pairedEtaShiftedLogTailFourierMoment
        (analyticZetaZeroMultiplicity rho)
        (1 - rho.1.re) rho.1.im N) +
    (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
      starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1 * rho.1) *
      (Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) : ℂ) *
      pairedEtaLogTailCutoffRelativeOscillation rho.1.im N *
      pairedEtaShiftedLogTailFourierMoment
        (analyticZetaZeroMultiplicity rho)
        rho.1.re (-rho.1.im) N

/-- The completed centered finite residual is exactly a unit common phase
times its symmetry-aware shifted coupled core. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_oscillation_mul_shiftedCoupledCore
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_tails,
    pairedEtaLeadingLogCutoffCenteredPartnerTail_eq_shifted,
    pairedEtaLeadingLogCutoffCenteredTail_eq_shifted]
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore
  simp only [map_mul, conj_ofReal]
  rw [star_pairedEtaLogTailCutoffOscillation,
    star_pairedEtaShiftedLogTailFourierMoment]
  ring

/-- Removing the common unit phase preserves the exact norm of the completed
centered finite residual. -/
theorem norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_shiftedCoupledCore
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ =
      ‖pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N‖ := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_oscillation_mul_shiftedCoupledCore,
    norm_mul, norm_pairedEtaLogTailCutoffOscillation, one_mul]

end

end RiemannGaussian
