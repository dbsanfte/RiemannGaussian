import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixAmplitudeSummability

/-!
# Finite energy form of the top-prefix summability frontier

The summability criterion initially involves a nonlinear difference between
the norms of two infinite centered tails.  At the relevant order `m-1`, both
complete moments vanish.  This module uses that vanishing to replace each tail
exactly by a literal finite centered prefix.

The resulting magnitude difference is then factored through the signed
difference of the two finite prefix energies.  After division by their
nonnegative total amplitude, this normalized signed energy defect is exactly
the original magnitude difference, including at a zero denominator.  Thus the
open summability target becomes square-summability of one explicit normalized
finite arithmetic energy defect, a form suitable for a future Gram/Bessel or
orthogonality estimate.

No summability estimate is assumed or proved here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completion-weighted magnitude of the literal finite centered prefix
at the reflected partner. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)‖

/-- The completion-weighted magnitude of the literal finite centered prefix
at the original zero. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight rho *
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
      (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)‖

/-- The completed complex reflected-partner finite prefix whose norm is the
finite partner amplitude. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1 *
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho - 1)
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)

/-- The parity-adjusted conjugate-original completed finite prefix. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      (pairedEtaXiCompletionFactor rho.1 * rho.1 *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1))

/-- The literal top prefix is the difference of the two completed complex
finite terms. -/
theorem topPrefix_eq_finitePartnerTerm_sub_finiteConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho N := by
  rfl

/-- The completed complex partner term has exactly the named finite partner
amplitude as its norm. -/
theorem norm_topPrefixFinitePartnerTerm_eq_finitePartnerAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        rho N‖ =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
    pairedEtaCompletionSpectralWeight
  rw [norm_mul, norm_mul]

/-- The completed complex conjugate term has exactly the named finite
conjugate amplitude as its norm. -/
theorem norm_topPrefixFiniteConjugateTerm_eq_finiteConjugateAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
        rho N‖ =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
    pairedEtaCompletionSpectralWeight
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_conj]

/-- The finite reflected-partner amplitude is nonnegative. -/
theorem topPrefixFinitePartnerAmplitude_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
  exact mul_nonneg
    (pairedEtaCompletionSpectralWeight_pos
      (NontrivialZetaZero.conjugatePartner rho)).le
    (norm_nonneg _)

/-- The finite conjugate-original amplitude is nonnegative. -/
theorem topPrefixFiniteConjugateAmplitude_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
  exact mul_nonneg (pairedEtaCompletionSpectralWeight_pos rho).le
    (norm_nonneg _)

/-- Lower-moment vanishing rewrites the partner component magnitude exactly
as a completion-weighted literal finite centered prefix magnitude. -/
theorem
    norm_topPrefixPartnerComponent_eq_finitePartnerAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖ =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        rho N := by
  have hk : analyticZetaZeroMultiplicity rho - 1 <
      analyticZetaZeroMultiplicity rho := by
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hkpartner : analyticZetaZeroMultiplicity rho - 1 <
      analyticZetaZeroMultiplicity
        (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk
  rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      (NontrivialZetaZero.conjugatePartner rho) hkpartner (N + 1)]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
  rw [norm_neg]

/-- Lower-moment vanishing rewrites the conjugate-original component magnitude
exactly as a completion-weighted literal finite centered prefix magnitude. -/
theorem
    norm_topPrefixConjugateComponent_eq_finiteConjugateAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N‖ =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        rho N := by
  have hk : analyticZetaZeroMultiplicity rho - 1 <
      analyticZetaZeroMultiplicity rho := by
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  rw [norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      rho hk (N + 1)]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
  rw [norm_neg]

/-- The signed difference of the two literal finite prefix magnitudes. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
      rho N -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
      rho N

/-- The amplitude imbalance is already entirely finite arithmetic: it is the
square of the two completion-weighted finite centered-prefix magnitudes. -/
theorem topPrefixAmplitudeImbalance_eq_sq_finiteAmplitudeDifference
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
        rho N ^ 2 := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
  rw [norm_topPrefixPartnerComponent_eq_finitePartnerAmplitude,
    norm_topPrefixConjugateComponent_eq_finiteConjugateAmplitude]

/-- The signed difference between the two literal finite prefix energies. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
      rho N ^ 2 -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
      rho N ^ 2

/-- The total magnitude used to normalize the signed finite energy defect. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
      rho N +
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
      rho N

/-- The finite energy difference factors into the magnitude difference times
the total magnitude. -/
theorem topPrefixFiniteEnergyDifference_eq_amplitudeDifference_mul_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
          rho N *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
  ring

/-- The signed finite energy difference is exactly the difference between the
two integrated component norm squares, so it is a signed rank-one Gram-energy
defect rather than a tail abstraction. -/
theorem topPrefixFiniteEnergyDifference_eq_componentNormSq_sub
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N =
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
          rho N‖ ^ 2 -
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
          rho N‖ ^ 2 := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  rw [norm_topPrefixPartnerComponent_eq_finitePartnerAmplitude,
    norm_topPrefixConjugateComponent_eq_finiteConjugateAmplitude]

/-- The finite energy difference is the literal squared-norm difference of
the two completed complex finite terms. -/
theorem topPrefixFiniteEnergyDifference_eq_finiteTermNormSq_sub
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N =
      Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho N) -
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho N) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    norm_topPrefixFinitePartnerTerm_eq_finitePartnerAmplitude,
    norm_topPrefixFiniteConjugateTerm_eq_finiteConjugateAmplitude]

/-- Polarization of the signed finite energy: it is the nonnegative top-prefix
energy plus the signed cross phase against the conjugate finite term. -/
theorem topPrefixFiniteEnergyDifference_eq_topPrefixEnergy_add_phase
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N =
      Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
            rho N) +
        2 *
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
                rho N)).re := by
  rw [topPrefixFiniteEnergyDifference_eq_finiteTermNormSq_sub,
    topPrefix_eq_finitePartnerTerm_sub_finiteConjugateTerm]
  exact complex_normSq_sub_normSq_eq_residual_phase _ _

/-- Divide the signed finite energy difference by the total amplitude.  Lean's
totalized division is harmless: if the denominator vanishes, both nonnegative
amplitudes vanish. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
      rho N /
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
      rho N

private theorem sq_sub_sq_div_add_eq_sub_of_nonneg
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ 2 - b ^ 2) / (a + b) = a - b := by
  by_cases hzero : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · field_simp [hzero]
    ring

/-- The normalized signed finite energy defect is exactly the original signed
difference of finite component magnitudes, with no nonvanishing assumption. -/
theorem topPrefixNormalizedFiniteEnergyDefect_eq_finiteAmplitudeDifference
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteAmplitudeDifference
  exact sq_sub_sq_div_add_eq_sub_of_nonneg _ _
    (topPrefixFinitePartnerAmplitude_nonneg rho N)
    (topPrefixFiniteConjugateAmplitude_nonneg rho N)

/-- The normalized defect is the explicit polarized finite Gram-energy ledger
divided by the total finite amplitude. -/
theorem
    topPrefixNormalizedFiniteEnergyDefect_eq_topPrefixEnergy_add_phase_div_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N =
      (Complex.normSq
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
              rho N) +
          2 *
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                rho N *
              starRingEnd ℂ
                (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
                  rho N)).re) /
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
  rw [topPrefixFiniteEnergyDifference_eq_topPrefixEnergy_add_phase]

/-- Exact finite-energy form of the amplitude frontier. -/
theorem topPrefixAmplitudeImbalance_eq_sq_normalizedFiniteEnergyDefect
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N ^ 2 := by
  rw [topPrefixAmplitudeImbalance_eq_sq_finiteAmplitudeDifference,
    topPrefixNormalizedFiniteEnergyDefect_eq_finiteAmplitudeDifference]

/-- Local square-summability of the normalized signed finite energy defect is
exactly the critical-line equation. -/
theorem
    summable_sq_topPrefixNormalizedFiniteEnergyDefect_iff_re_eq_half
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N ^ 2) ↔
      rho.1.re = 1 / 2 := by
  rw [← summable_topPrefixAmplitudeImbalance_iff_re_eq_half rho]
  apply summable_congr
  intro N
  exact
    (topPrefixAmplitudeImbalance_eq_sq_normalizedFiniteEnergyDefect rho N).symm

/-- The universal finite-energy square-summability target. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefectSqSummable :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
        rho N ^ 2)

/-- Universal square-summability of the explicit normalized signed finite
energy defect is exactly RH.  Its arithmetic direction remains open. -/
theorem
    riemannHypothesis_iff_all_topPrefixNormalizedFiniteEnergyDefect_sq_summable :
    RiemannHypothesis ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefectSqSummable := by
  constructor
  · intro hRH rho
    exact
      (summable_sq_topPrefixNormalizedFiniteEnergyDefect_iff_re_eq_half rho).2
        ((summable_topPrefixAmplitudeImbalance_iff_re_eq_half rho).1
          ((riemannHypothesis_iff_all_topPrefixAmplitudeImbalance_summable.mp hRH)
            rho))
  · intro hsummable
    apply riemannHypothesis_iff_all_topPrefixAmplitudeImbalance_summable.mpr
    intro rho
    have hrho :=
      (summable_sq_topPrefixNormalizedFiniteEnergyDefect_iff_re_eq_half rho).1
        (hsummable rho)
    exact (summable_topPrefixAmplitudeImbalance_iff_re_eq_half rho).2 hrho

end

end RiemannGaussian
