import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentGapBound

/-!
# Complementary comparison for the leading eta gap-moment defect

This module packages the first nonzero arithmetic gap-moment defect at a
nontrivial zeta zero and combines two previously independent facts:

* completed xi symmetry gives an exact relation between the defects at
  `rho` and `1 - conj rho`; and
* the first omitted eta interval gives an explicit strict saving over the
  full positive-half-line moment at each horizontal tilt.

The result is an exact completion-weighted norm ratio and unconditional
cross-tilt upper bounds.  These statements identify the quantitative scale
on which a future lower bound must operate.  They do not force the two tilts
to agree and therefore do not imply RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The first nonzero deviation of the explicit eta gap moment from its
full-half-line value at a nontrivial zeta zero. -/
def pairedEtaLeadingLogGapMomentDefect
    (rho : NontrivialZetaZero) : ℂ :=
  ((analyticZetaZeroMultiplicity rho).factorial : ℂ) *
      (rho.1 ^ (analyticZetaZeroMultiplicity rho + 1))⁻¹ -
    pairedEtaLogGapMoment (analyticZetaZeroMultiplicity rho) rho.1

/-- The canonical leading gap defect is exactly the first nonzero eta-support
Laplace moment. -/
theorem pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment
    (rho : NontrivialZetaZero) :
    pairedEtaLeadingLogGapMomentDefect rho =
      pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho) rho.1 := by
  unfold pairedEtaLeadingLogGapMomentDefect
  exact (pairedEtaLogLaplaceMoment_eq_factorial_sub_gap
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)).symm

/-- The leading gap defect at a nontrivial zeta zero is nonzero. -/
theorem pairedEtaLeadingLogGapMomentDefect_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaLeadingLogGapMomentDefect rho ≠ 0 := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  exact pairedEtaLogLaplaceMoment_multiplicity_ne_zero rho

/-- The positive completion and spectral-parameter weight attached to one
nontrivial zeta zero. -/
def pairedEtaCompletionSpectralWeight
    (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖

/-- The completion--spectral weight is strictly positive. -/
theorem pairedEtaCompletionSpectralWeight_pos
    (rho : NontrivialZetaZero) :
    0 < pairedEtaCompletionSpectralWeight rho := by
  unfold pairedEtaCompletionSpectralWeight
  exact mul_pos
    (norm_pos_iff.mpr (pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)))
    (norm_pos_iff.mpr (NontrivialZetaZero.coe_ne_zero rho))

/-- The completion-weighted magnitude of the first nonzero eta gap defect. -/
def pairedEtaCompletedLeadingLogGapMomentMagnitude
    (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletionSpectralWeight rho *
    ‖pairedEtaLeadingLogGapMomentDefect rho‖

/-- The completed leading-defect magnitude is strictly positive. -/
theorem pairedEtaCompletedLeadingLogGapMomentMagnitude_pos
    (rho : NontrivialZetaZero) :
    0 < pairedEtaCompletedLeadingLogGapMomentMagnitude rho := by
  unfold pairedEtaCompletedLeadingLogGapMomentMagnitude
  exact mul_pos (pairedEtaCompletionSpectralWeight_pos rho)
    (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))

/-- The explicit first-gap upper envelope at order `k` and positive real
tilt `sigma`. -/
def pairedEtaLeadingLogGapMomentDefectUpper
    (k : ℕ) (sigma : ℝ) : ℝ :=
  (k.factorial : ℝ) / sigma ^ (k + 1) -
    pairedEtaFirstGapRealMomentLower k sigma

/-- The canonical leading defect satisfies the explicit first-gap upper
envelope at its own horizontal tilt. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_le_upper
    (rho : NontrivialZetaZero) :
    ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
      pairedEtaLeadingLogGapMomentDefectUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re := by
  unfold pairedEtaLeadingLogGapMomentDefect
    pairedEtaLeadingLogGapMomentDefectUpper
  exact norm_pairedEtaLeadingLogGapMomentDefect_le_firstGap rho

/-- At a zeta zero the first-gap upper envelope is itself strictly positive,
because it bounds a nonzero defect norm. -/
theorem pairedEtaLeadingLogGapMomentDefectUpper_pos
    (rho : NontrivialZetaZero) :
    0 < pairedEtaLeadingLogGapMomentDefectUpper
      (analyticZetaZeroMultiplicity rho) rho.1.re := by
  exact lt_of_lt_of_le
    (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
    (norm_pairedEtaLeadingLogGapMomentDefect_le_upper rho)

/-- The exact completed partner identity, expressed using the canonical
leading gap defects. -/
theorem pairedEtaCompletedLeadingLogGapMomentDefect_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaLeadingLogGapMomentDefect
          (NontrivialZetaZero.conjugatePartner rho) =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 * rho.1 *
            pairedEtaLeadingLogGapMomentDefect rho) := by
  unfold pairedEtaLeadingLogGapMomentDefect
  simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
    pairedEtaLeadingLogGapMomentDefect_conjugatePartner rho

/-- Completed leading-defect magnitudes agree exactly at complementary
nontrivial zeros. -/
theorem pairedEtaCompletedLeadingLogGapMomentMagnitude_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingLogGapMomentMagnitude
        (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaCompletedLeadingLogGapMomentMagnitude rho := by
  have hnorm := congrArg norm
    (pairedEtaCompletedLeadingLogGapMomentDefect_conjugatePartner rho)
  simpa only [pairedEtaCompletedLeadingLogGapMomentMagnitude,
    pairedEtaCompletionSpectralWeight, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, norm_conj,
    analyticZetaZeroMultiplicity_conjugatePartner] using hnorm

/-- Equivalently, the raw defect norms at complementary zeros have the exact
ratio dictated by the reciprocal completion--spectral weights. -/
theorem norm_pairedEtaLeadingLogGapMomentDefect_conjugatePartner_ratio
    (rho : NontrivialZetaZero) :
    ‖pairedEtaLeadingLogGapMomentDefect
        (NontrivialZetaZero.conjugatePartner rho)‖ /
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ =
      pairedEtaCompletionSpectralWeight rho /
        pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) := by
  have h :=
    pairedEtaCompletedLeadingLogGapMomentMagnitude_conjugatePartner rho
  have hdefect : ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≠ 0 :=
    (norm_pos_iff.mpr
      (pairedEtaLeadingLogGapMomentDefect_ne_zero rho)).ne'
  have hweight : pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) ≠ 0 :=
    (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho)).ne'
  apply (div_eq_div_iff hdefect hweight).2
  simpa only [pairedEtaCompletedLeadingLogGapMomentMagnitude,
    mul_comm] using h

/-- The completed leading-defect magnitude is bounded by its locally tilted
first-gap envelope. -/
theorem pairedEtaCompletedLeadingLogGapMomentMagnitude_le_upper
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingLogGapMomentMagnitude rho ≤
      pairedEtaCompletionSpectralWeight rho *
        pairedEtaLeadingLogGapMomentDefectUpper
          (analyticZetaZeroMultiplicity rho) rho.1.re := by
  unfold pairedEtaCompletedLeadingLogGapMomentMagnitude
  exact mul_le_mul_of_nonneg_left
    (norm_pairedEtaLeadingLogGapMomentDefect_le_upper rho)
    (pairedEtaCompletionSpectralWeight_pos rho).le

/-- Symmetry transports each first-gap estimate to the opposite tilt.  Thus
the common completed defect is bounded by both explicit complementary
envelopes. -/
theorem pairedEtaCompletedLeadingLogGapMomentMagnitude_le_both_tilts
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingLogGapMomentMagnitude rho ≤
        pairedEtaCompletionSpectralWeight rho *
          pairedEtaLeadingLogGapMomentDefectUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re ∧
      pairedEtaCompletedLeadingLogGapMomentMagnitude rho ≤
        pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLeadingLogGapMomentDefectUpper
            (analyticZetaZeroMultiplicity rho) (1 - rho.1.re) := by
  constructor
  · exact pairedEtaCompletedLeadingLogGapMomentMagnitude_le_upper rho
  · rw [←
      pairedEtaCompletedLeadingLogGapMomentMagnitude_conjugatePartner rho]
    simpa [NontrivialZetaZero.conjugatePartner_coe] using
      pairedEtaCompletedLeadingLogGapMomentMagnitude_le_upper
        (NontrivialZetaZero.conjugatePartner rho)

end

end RiemannGaussian
