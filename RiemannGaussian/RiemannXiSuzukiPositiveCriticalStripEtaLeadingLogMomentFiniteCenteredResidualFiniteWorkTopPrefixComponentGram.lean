import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixGram

/-!
# Complementary-component decomposition of the top-prefix Gram frontier

The critical-half interference feature is the sum of two explicit pieces:
the completed reflected-partner tilt and the parity-adjusted conjugate
original tilt.  This module separates those pieces before integration.

For their two complex integrals `P_N` and `Q_N`, Lean proves the exact
nonnegative decomposition

`|C_(m-1,N+1)|^2 = (|P_N|-|Q_N|)^2 + A_N`,

where

`A_N = 2 * (|P_N||Q_N| + Re(P_N conj(Q_N))) >= 0`

is the anti-alignment defect.  Thus small top-prefix Gram mass requires two
independent phenomena: complementary amplitude balance and almost maximally
opposite cross phase.  Endpoint-scaled Gram boundedness is proved equivalent
to endpoint-scaled boundedness of both nonnegative terms.

No amplitude-balance or anti-alignment estimate is assumed here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The reflected-partner component of the top-prefix coupled integrand. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
      rho (N + 1) *
    ((u : ℂ) ^ (analyticZetaZeroMultiplicity rho - 1) *
      (Real.exp (-(1 - rho.1.re) * u) : ℂ) *
      Complex.exp (-((rho.1.im * u : ℝ) : ℂ) * I))

/-- The parity-adjusted conjugate-original component of the top-prefix
coupled integrand. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
      rho (N + 1) *
    ((u : ℂ) ^ (analyticZetaZeroMultiplicity rho - 1) *
      (Real.exp (-rho.1.re * u) : ℂ) *
      Complex.exp (-((-rho.1.im * u : ℝ) : ℂ) * I))

/-- The reflected-partner component is integrable. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
        rho N)
      (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  exact
    (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho - 1)
      (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
      rho.1.im (N + 1)).const_mul
        (-pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
          rho (N + 1))

/-- The conjugate-original component is integrable. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
        rho N)
      (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  exact
    (integrable_pairedEtaShiftedLogTailFourierMoment_integrand
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho)
      (-rho.1.im) (N + 1)).const_mul
        (pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
          rho (N + 1))

/-- Pointwise, the critical-half interference feature is the sum of its two
complementary tilted components. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand_eq_components
    (rho : NontrivialZetaZero) (N : ℕ) (u : ℝ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N u =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
          rho N u +
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
          rho N u := by
  rw [←
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCoupledIntegrand_eq_halfIntegrand]
  rfl

/-- The integrated reflected-partner contribution. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ∫ u : ℝ,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
      rho N u
    ∂pairedEtaShiftedLogTailMeasure (N + 1)

/-- The integrated parity-adjusted conjugate-original contribution. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ∫ u : ℝ,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
      rho N u
    ∂pairedEtaShiftedLogTailMeasure (N + 1)

/-- The reflected-partner component integral is its coefficient times the
corresponding shifted Fourier--Laplace moment. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent_eq_coefficient_mul_moment
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N =
      -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
          rho (N + 1) *
        pairedEtaShiftedLogTailFourierMoment
          (analyticZetaZeroMultiplicity rho - 1)
          (1 - rho.1.re) rho.1.im (N + 1) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
    pairedEtaShiftedLogTailFourierMoment
  rw [integral_const_mul]

/-- The conjugate-original component integral is its coefficient times the
frequency-reversed shifted Fourier--Laplace moment. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent_eq_coefficient_mul_moment
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
          rho (N + 1) *
        pairedEtaShiftedLogTailFourierMoment
          (analyticZetaZeroMultiplicity rho - 1)
          rho.1.re (-rho.1.im) (N + 1) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
    pairedEtaShiftedLogTailFourierMoment
  rw [integral_const_mul]

/-- Restoring the common cutoff phase turns the partner component into the
literal completed centered partner tail of order `m-1`. -/
theorem
    oscillation_mul_topPrefixPartnerComponent_eq_neg_completed_partnerTail
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLogTailCutoffOscillation rho.1.im (N + 1) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
          rho N =
      -(pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho - 1)
          (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)) := by
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent_eq_coefficient_mul_moment,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
  simp only [NontrivialZetaZero.conjugatePartner_coe,
    Complex.sub_re, Complex.one_re, Complex.conj_re,
    Complex.sub_im, Complex.one_im, Complex.conj_im,
    zero_sub, neg_neg]
  ring

/-- Restoring the common cutoff phase turns the second component into the
parity-adjusted conjugate of the literal centered original tail. -/
theorem
    oscillation_mul_topPrefixConjugateComponent_eq_parity_mul_star_completed_rhoTail
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLogTailCutoffOscillation rho.1.im (N + 1) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLogLaplaceMomentCutoffCenteredTail
              (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)) := by
  rw [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent_eq_coefficient_mul_moment,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
  simp only [map_mul, conj_ofReal]
  rw [star_pairedEtaLogTailCutoffOscillation,
    star_pairedEtaShiftedLogTailFourierMoment]
  ring

/-- The partner-component norm is exactly the completion weight times the
literal order-`m-1` partner-tail norm. -/
theorem
    norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖ =
      pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho - 1)
          (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)‖ := by
  have h := congrArg norm
    (oscillation_mul_topPrefixPartnerComponent_eq_neg_completed_partnerTail
      rho N)
  unfold pairedEtaCompletionSpectralWeight
  simpa only [norm_mul, norm_neg,
    norm_pairedEtaLogTailCutoffOscillation, one_mul] using h

/-- The conjugate-component norm is exactly the original completion weight
times the literal order-`m-1` original-tail norm. -/
theorem
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N‖ =
      pairedEtaCompletionSpectralWeight rho *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)‖ := by
  have h := congrArg norm
    (oscillation_mul_topPrefixConjugateComponent_eq_parity_mul_star_completed_rhoTail
      rho N)
  unfold pairedEtaCompletionSpectralWeight
  simpa only [norm_mul, norm_pairedEtaLogTailCutoffOscillation,
    one_mul, norm_pow, norm_neg, norm_one, one_pow, norm_conj] using h

/-- The partner component obeys its full complementary-exponent centered-tail
envelope. -/
theorem
    norm_topPrefixPartnerComponent_le_completionWeight_mul_centeredTailUpper
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖ ≤
      pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho - 1)
          (NontrivialZetaZero.conjugatePartner rho).1.re (N + 1) := by
  rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail]
  exact mul_le_mul_of_nonneg_left
    (norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)) (N + 1))
    (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho)).le

/-- The conjugate-original component obeys its full original-exponent
centered-tail envelope. -/
theorem
    norm_topPrefixConjugateComponent_le_completionWeight_mul_centeredTailUpper
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N‖ ≤
      pairedEtaCompletionSpectralWeight rho *
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho - 1) rho.1.re (N + 1) := by
  rw [norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail]
  exact mul_le_mul_of_nonneg_left
    (norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho) (N + 1))
    (pairedEtaCompletionSpectralWeight_pos rho).le

/-- The one-variable interference integral splits exactly into the two
complementary component integrals. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand_eq_components
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ u : ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u
        ∂pairedEtaShiftedLogTailMeasure (N + 1)) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
          rho N +
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
  rw [← integral_add
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponentIntegrand
      rho N)
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponentIntegrand
      rho N)]
  apply integral_congr_ae
  exact Eventually.of_forall fun u =>
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand_eq_components
      rho N u

/-- The top-prefix squared norm is the norm square of the sum of the two
integrated complementary components. -/
theorem
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_normSq_components
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ ^ 2 =
      Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
            rho N +
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
            rho N) := by
  rw [
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_halfIntegrand,
    Complex.sq_norm,
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand_eq_components]

/-- The squared mismatch between the magnitudes of the two complementary
component integrals. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
      rho N‖ -
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
      rho N‖) ^ 2

/-- The residual failure of the two integrated components to be maximally
oppositely aligned. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 *
    (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N‖ +
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
          rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
            rho N)).re)

/-- The amplitude-imbalance term is nonnegative. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
  positivity

/-- The amplitude imbalance contains no hidden shifted-measure object: it is
literally the squared difference of the two completion-weighted centered-tail
magnitudes at the complementary zeros. -/
theorem
    topPrefixAmplitudeImbalance_eq_sq_completionWeighted_centeredTailNorm_sub
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N =
      (pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
            (analyticZetaZeroMultiplicity rho - 1)
            (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)‖ -
        pairedEtaCompletionSpectralWeight rho *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
            (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)‖) ^ 2 := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
  rw [
    norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail]

/-- The anti-alignment defect is nonnegative by the sharp elementary lower
bound on the real Hermitian cross term. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
        rho N := by
  let P : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
      rho N
  let Q : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
      rho N
  have hcross : |(P * starRingEnd ℂ Q).re| ≤ ‖P‖ * ‖Q‖ := by
    calc
      |(P * starRingEnd ℂ Q).re| ≤ ‖P * starRingEnd ℂ Q‖ :=
        Complex.abs_re_le_norm _
      _ = ‖P‖ * ‖Q‖ := by rw [norm_mul, norm_conj]
  have hlower : -(‖P‖ * ‖Q‖) ≤ (P * starRingEnd ℂ Q).re :=
    (abs_le.mp hcross).1
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
  change 0 ≤ 2 * (‖P‖ * ‖Q‖ + (P * starRingEnd ℂ Q).re)
  nlinarith

/-- The anti-alignment defect is at most four times the product of the two
component magnitudes. -/
theorem
    topPrefixAntiAlignmentDefect_le_four_mul_componentNorms
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
        rho N ≤
      4 *
        (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
            rho N‖ *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
            rho N‖) := by
  let P : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
      rho N
  let Q : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
      rho N
  have hcross : (P * starRingEnd ℂ Q).re ≤ ‖P‖ * ‖Q‖ := by
    calc
      (P * starRingEnd ℂ Q).re ≤ ‖P * starRingEnd ℂ Q‖ :=
        Complex.re_le_norm _
      _ = ‖P‖ * ‖Q‖ := by rw [norm_mul, norm_conj]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
  change 2 * (‖P‖ * ‖Q‖ + (P * starRingEnd ℂ Q).re) ≤
    4 * (‖P‖ * ‖Q‖)
  linarith

/-- The anti-alignment defect is controlled by the product of the two explicit
completion-weighted centered-tail envelopes. -/
theorem
    topPrefixAntiAlignmentDefect_le_four_mul_completionWeightedCenteredTailUppers
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
        rho N ≤
      4 *
        ((pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLogLaplaceMomentCenteredTailUpper
            (analyticZetaZeroMultiplicity rho - 1)
            (NontrivialZetaZero.conjugatePartner rho).1.re (N + 1)) *
        (pairedEtaCompletionSpectralWeight rho *
          pairedEtaLogLaplaceMomentCenteredTailUpper
            (analyticZetaZeroMultiplicity rho - 1) rho.1.re (N + 1))) := by
  apply (topPrefixAntiAlignmentDefect_le_four_mul_componentNorms rho N).trans
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul
      (norm_topPrefixPartnerComponent_le_completionWeight_mul_centeredTailUpper
        rho N)
      (norm_topPrefixConjugateComponent_le_completionWeight_mul_centeredTailUpper
        rho N)
      (norm_nonneg _)
      (mul_nonneg
        (pairedEtaCompletionSpectralWeight_pos
          (NontrivialZetaZero.conjugatePartner rho)).le
        (pairedEtaLogLaplaceMomentCenteredTailUpper_pos
          (analyticZetaZeroMultiplicity rho - 1)
          (NontrivialZetaZero.zero_lt_re
            (NontrivialZetaZero.conjugatePartner rho)) (N + 1)).le)
  · norm_num

/-- Complementary centered-tail envelopes have exactly one full endpoint
power in their product.  The frontier endpoint `2N+1` is smaller than the
tail endpoint `2N+3`, leaving a uniform fixed Gamma-moment bound. -/
theorem
    oddEndpoint_mul_centeredTailUpper_partner_mul_rho_le_fixedGammaProduct
    (rho : NontrivialZetaZero) (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho - 1)
          (NontrivialZetaZero.conjugatePartner rho).1.re (N + 1) *
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho - 1) rho.1.re (N + 1) ≤
      ((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
          (NontrivialZetaZero.conjugatePartner rho).1.re ^
            (analyticZetaZeroMultiplicity rho - 1 + 1)) *
        ((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
          rho.1.re ^ (analyticZetaZeroMultiplicity rho - 1 + 1)) := by
  let k := analyticZetaZeroMultiplicity rho - 1
  let partner := NontrivialZetaZero.conjugatePartner rho
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let y : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
  let A : ℝ := ((k.factorial : ℕ) : ℝ) / partner.1.re ^ (k + 1)
  let B : ℝ := ((k.factorial : ℕ) : ℝ) / rho.1.re ^ (k + 1)
  have hy : 0 < y := by
    dsimp only [y]
    positivity
  have hxy : x ≤ y := by
    dsimp only [x, y]
    norm_num
  have hsum : -partner.1.re + -rho.1.re = (-1 : ℝ) := by
    simp only [partner, NontrivialZetaZero.conjugatePartner_coe,
      Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  have hrpow : y ^ (-partner.1.re) * y ^ (-rho.1.re) = y⁻¹ := by
    rw [← Real.rpow_add hy, hsum, Real.rpow_neg_one]
  have hratio : x * y⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hy).2 hxy
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg (by positivity)
      (pow_nonneg (NontrivialZetaZero.zero_lt_re partner).le _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact div_nonneg (by positivity)
      (pow_nonneg (NontrivialZetaZero.zero_lt_re rho).le _)
  have hAB : 0 ≤ A * B := by
    exact mul_nonneg hA hB
  rw [pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow,
    pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow]
  change x * (y ^ (-partner.1.re) * A) * (y ^ (-rho.1.re) * B) ≤
    A * B
  calc
    x * (y ^ (-partner.1.re) * A) * (y ^ (-rho.1.re) * B) =
        (x * (y ^ (-partner.1.re) * y ^ (-rho.1.re))) * (A * B) := by
      ring
    _ = (x * y⁻¹) * (A * B) := by rw [hrpow]
    _ ≤ 1 * (A * B) := mul_le_mul_of_nonneg_right hratio hAB
    _ = A * B := one_mul _

/-- A fixed zero-dependent constant controlling the endpoint-scaled
anti-alignment defect for every cutoff. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleUpper
    (rho : NontrivialZetaZero) : ℝ :=
  4 *
    (pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaCompletionSpectralWeight rho) *
    (((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
        (NontrivialZetaZero.conjugatePartner rho).1.re ^
          (analyticZetaZeroMultiplicity rho - 1 + 1)) *
      ((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
        rho.1.re ^ (analyticZetaZeroMultiplicity rho - 1 + 1)))

/-- The anti-alignment defect is unconditionally bounded at the full endpoint
scale, uniformly over all cutoffs for each nontrivial zero. -/
theorem
    oddEndpoint_mul_topPrefixAntiAlignmentDefect_le_criticalScaleUpper
    (rho : NontrivialZetaZero) (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
          rho N ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleUpper
        rho := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let Wp : ℝ := pairedEtaCompletionSpectralWeight
    (NontrivialZetaZero.conjugatePartner rho)
  let Wr : ℝ := pairedEtaCompletionSpectralWeight rho
  let Up : ℝ := pairedEtaLogLaplaceMomentCenteredTailUpper
    (analyticZetaZeroMultiplicity rho - 1)
    (NontrivialZetaZero.conjugatePartner rho).1.re (N + 1)
  let Ur : ℝ := pairedEtaLogLaplaceMomentCenteredTailUpper
    (analyticZetaZeroMultiplicity rho - 1) rho.1.re (N + 1)
  let Gp : ℝ :=
    (((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
      (NontrivialZetaZero.conjugatePartner rho).1.re ^
        (analyticZetaZeroMultiplicity rho - 1 + 1)
  let Gr : ℝ :=
    (((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℝ) /
      rho.1.re ^ (analyticZetaZeroMultiplicity rho - 1 + 1)
  have hdefect :=
    topPrefixAntiAlignmentDefect_le_four_mul_completionWeightedCenteredTailUppers
      rho N
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hproduct : x * Up * Ur ≤ Gp * Gr := by
    simpa only [x, Up, Ur, Gp, Gr] using
      oddEndpoint_mul_centeredTailUpper_partner_mul_rho_le_fixedGammaProduct
        rho N
  have hweight : 0 ≤ 4 * (Wp * Wr) := by
    dsimp only [Wp, Wr]
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (pairedEtaCompletionSpectralWeight_pos
          (NontrivialZetaZero.conjugatePartner rho)).le
        (pairedEtaCompletionSpectralWeight_pos rho).le)
  calc
    x *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
          rho N ≤ x * (4 * ((Wp * Up) * (Wr * Ur))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [Wp, Wr, Up, Ur] using hdefect
      · exact hx
    _ = (4 * (Wp * Wr)) * (x * Up * Ur) := by ring
    _ ≤ (4 * (Wp * Wr)) * (Gp * Gr) :=
      mul_le_mul_of_nonneg_left hproduct hweight
    _ =
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleUpper
          rho := by
      unfold
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleUpper
      simp only [Wp, Wr, Gp, Gr]

/-- Exact nonnegative amplitude/phase decomposition of the top-prefix Gram. -/
theorem
    norm_sq_topPrefix_eq_amplitudeImbalance_add_antiAlignmentDefect
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ ^ 2 =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N +
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
          rho N := by
  let P : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
      rho N
  let Q : ℂ :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
      rho N
  rw [
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_normSq_components,
    Complex.normSq_add]
  have hP := Complex.sq_norm P
  have hQ := Complex.sq_norm Q
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
  change Complex.normSq P + Complex.normSq Q +
      2 * (P * starRingEnd ℂ Q).re =
    (‖P‖ - ‖Q‖) ^ 2 +
      2 * (‖P‖ * ‖Q‖ + (P * starRingEnd ℂ Q).re)
  rw [← hP, ← hQ]
  ring

/-- The endpoint-scaled Hermitian Gram mass is exactly the sum of the
endpoint-scaled amplitude imbalance and anti-alignment defect. -/
theorem
    oddEndpoint_mul_integral_topPrefixGramKernel_eq_amplitudeImbalance_add_antiAlignmentDefect
    (rho : NontrivialZetaZero) (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℝ) *
        (∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
            rho N p
          ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
            (pairedEtaShiftedLogTailMeasure (N + 1)))) =
      ((2 * N + 1 : ℕ) : ℝ) *
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
            rho N +
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
            rho N) := by
  rw [←
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_gramKernel,
    norm_sq_topPrefix_eq_amplitudeImbalance_add_antiAlignmentDefect]

/-- Eventual endpoint-scale amplitude balance for the two complementary
component integrals. -/
def PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded
    (rho : NontrivialZetaZero) : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ((2 * N + 1 : ℕ) : ℝ) *
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N ≤ C

/-- Eventual endpoint-scale control of the complementary anti-alignment
defect. -/
def PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleEventuallyBounded
    (rho : NontrivialZetaZero) : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ((2 * N + 1 : ℕ) : ℝ) *
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
        rho N ≤ C

/-- The local Hermitian Gram frontier is exactly the conjunction of endpoint
amplitude balance and endpoint anti-alignment control. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded_iff_amplitudeImbalance_and_antiAlignment
    (rho : NontrivialZetaZero) :
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded
        rho ↔
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded
          rho ∧
        PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleEventuallyBounded
          rho := by
  constructor
  · rintro ⟨C, hgram⟩
    constructor
    · refine ⟨C, ?_⟩
      filter_upwards [hgram] with N hN
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      let A : ℝ :=
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N
      let D : ℝ :=
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
          rho N
      have hD : 0 ≤ D := by
        simpa only [D] using
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect_nonneg
            rho N
      calc
        x * A ≤ x * (A + D) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · dsimp only [x]
            positivity
        _ = ((2 * N + 1 : ℕ) : ℝ) *
            (∫ p : ℝ × ℝ,
              pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
                rho N p
              ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
                (pairedEtaShiftedLogTailMeasure (N + 1)))) := by
              symm
              simpa only [x, A, D] using
                oddEndpoint_mul_integral_topPrefixGramKernel_eq_amplitudeImbalance_add_antiAlignmentDefect
                  rho N
        _ ≤ C := hN
    · refine ⟨C, ?_⟩
      filter_upwards [hgram] with N hN
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      let A : ℝ :=
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N
      let D : ℝ :=
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
          rho N
      have hA : 0 ≤ A := by
        simpa only [A] using
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance_nonneg
            rho N
      calc
        x * D ≤ x * (A + D) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · dsimp only [x]
            positivity
        _ = ((2 * N + 1 : ℕ) : ℝ) *
            (∫ p : ℝ × ℝ,
              pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
                rho N p
              ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
                (pairedEtaShiftedLogTailMeasure (N + 1)))) := by
              symm
              simpa only [x, A, D] using
                oddEndpoint_mul_integral_topPrefixGramKernel_eq_amplitudeImbalance_add_antiAlignmentDefect
                  rho N
        _ ≤ C := hN
  · rintro ⟨⟨C, hamp⟩, ⟨D, halign⟩⟩
    refine ⟨C + D, ?_⟩
    filter_upwards [hamp, halign] with N hampN halignN
    rw [
      oddEndpoint_mul_integral_topPrefixGramKernel_eq_amplitudeImbalance_add_antiAlignmentDefect]
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
              rho N +
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
              rho N) =
          ((2 * N + 1 : ℕ) : ℝ) *
              pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
                rho N +
            ((2 * N + 1 : ℕ) : ℝ) *
              pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentDefect
                rho N := by ring
      _ ≤ C + D := add_le_add hampN halignN

/-- The anti-alignment half of the component frontier is unconditional: the
complementary centered-tail exponents add to one, so their product already
has the full inverse-endpoint decay. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignment_criticalScale_eventuallyBounded
    (rho : NontrivialZetaZero) :
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleEventuallyBounded
      rho := by
  refine ⟨
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignmentCriticalScaleUpper
      rho, ?_⟩
  exact Eventually.of_forall fun N =>
    oddEndpoint_mul_topPrefixAntiAlignmentDefect_le_criticalScaleUpper rho N

/-- Consequently the entire Hermitian Gram frontier is equivalent to the
single complementary-amplitude imbalance bound; the cross-phase term needs no
additional conjectural estimate. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded_iff_amplitudeImbalance
    (rho : NontrivialZetaZero) :
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded
        rho ↔
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded
        rho := by
  constructor
  · intro hgram
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded_iff_amplitudeImbalance_and_antiAlignment
        rho).mp hgram |>.1
  · intro hamp
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded_iff_amplitudeImbalance_and_antiAlignment
        rho).mpr
        ⟨hamp,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAntiAlignment_criticalScale_eventuallyBounded
            rho⟩

/-- The original square-root top-prefix frontier is therefore exactly the
endpoint-scaled squared amplitude-balance frontier. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_amplitudeImbalance
    (rho : NontrivialZetaZero) :
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded
        rho ↔
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded
        rho := by
  exact
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram
      rho).trans
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded_iff_amplitudeImbalance
        rho)

/-- The global complementary-component amplitude-balance estimate. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded
      rho

/-- A universal endpoint-scaled bound for the squared difference of the two
component magnitudes proves the Riemann hypothesis. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance_criticalScale_eventuallyBounded
    (hamp :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceCriticalScaleEventuallyBounded) :
    RiemannHypothesis := by
  apply
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded
  intro rho
  exact
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_amplitudeImbalance
      rho).mpr (hamp rho)

end

end RiemannGaussian
