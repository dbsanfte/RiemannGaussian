import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTail

/-!
# Centered finite completed residual for the leading eta moment

The cutoff-centered finite prefixes remove the logarithmic-power loss from
the individual leading-moment tails.  This module inserts those prefixes into
the exact completed functional-equation coupling at a nontrivial zero and its
same-ordinate reflected partner.

The resulting complex residual retains the complete phase, parity, Gamma,
dyadic, and spectral factors.  Exact cancellation of the two infinite leading
moments rewrites it as the difference of the two centered tail errors.  Lean
therefore bounds it unconditionally by

`W(rho#) T_N(rho#) + W(rho) T_N(rho)`,

where each `T_N` has full horizontal exponent and no logarithmic loss.  The
bound tends to zero and is strictly smaller than the former balanced
near-sharp completed residual bound whenever both older cutoff conditions
hold.  This is a sharper finite coupling, not a zero-location theorem: the
remaining frontier is a sign or phase constraint on the explicit residual.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The completed cutoff-centered prefix at the same-ordinate reflected
partner of a nontrivial zero. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1 *
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1 N

/-- The parity-adjusted conjugate of the completed cutoff-centered prefix at
the original nontrivial zero. -/
def pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
    starRingEnd ℂ
      (pairedEtaXiCompletionFactor rho.1 * rho.1 *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N)

/-- The completed functional-equation residual formed from the two
cutoff-centered finite leading-moment prefixes. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm rho N -
    pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N

/-- The cutoff-centered partner residual is literally the difference of its
two completed finite terms. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_sub
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N := rfl

/-- Polarization expresses a difference of two complex squared norms through
their residual and its phase against the second term. -/
theorem complex_normSq_sub_normSq_eq_residual_phase (z w : ℂ) :
    Complex.normSq z - Complex.normSq w =
      Complex.normSq (z - w) +
        2 * (w * starRingEnd ℂ (z - w)).re := by
  conv_lhs =>
    lhs
    rw [show z = w + (z - w) by ring]
  rw [Complex.normSq_add]
  ring

/-- The completed squared-norm defect between the two cutoff-centered finite
partner terms. -/
def pairedEtaCompletedLeadingLogCutoffCenteredNormDefect
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  Complex.normSq
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm rho N) -
    Complex.normSq
      (pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N)

/-- The completed centered-prefix norm defect is the explicit difference of
the two completion-weighted finite prefix norm squares. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredNormDefect_eq_weighted_sq_sub
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredNormDefect rho N =
      (pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho)
          (NontrivialZetaZero.conjugatePartner rho).1 N‖) ^ 2 -
      (pairedEtaCompletionSpectralWeight rho *
        ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N‖) ^ 2 := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredNormDefect
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm
    pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm
    pairedEtaCompletionSpectralWeight
  simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, norm_conj]

/-- The completed centered-prefix norm defect is exactly residual energy plus
the residual's signed phase against the original conjugate term. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredNormDefect_eq_residual_phase
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredNormDefect rho N =
      Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N) +
      2 *
        (pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)).re := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredNormDefect
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
  exact complex_normSq_sub_normSq_eq_residual_phase _ _

/-- A nonnegative residual phase forces the completed centered-prefix norm
defect to be nonnegative. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredNormDefect_nonneg_of_phase
    (rho : NontrivialZetaZero) (N : ℕ)
    (hphase : 0 ≤
      (pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)).re) :
    0 ≤ pairedEtaCompletedLeadingLogCutoffCenteredNormDefect rho N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredNormDefect_eq_residual_phase]
  nlinarith [Complex.normSq_nonneg
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)]

/-- Conversely, a negative completed centered-prefix norm defect certifies a
strictly negative residual phase. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredResidualPhase_neg_of_normDefect_neg
    (rho : NontrivialZetaZero) (N : ℕ)
    (hdefect : pairedEtaCompletedLeadingLogCutoffCenteredNormDefect rho N < 0) :
    (pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)).re < 0 := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredNormDefect_eq_residual_phase]
    at hdefect
  nlinarith [Complex.normSq_nonneg
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)]

/-- The sum of the two completion-weighted centered tail envelopes controlling
the cutoff-centered partner residual. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.conjugatePartner rho).1.re N +
    pairedEtaCompletionSpectralWeight rho *
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N

/-- Exact completed cancellation rewrites the centered finite residual as the
two centered-prefix approximation errors. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_errors
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1) -
        (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
                  (analyticZetaZeroMultiplicity rho) rho.1 N -
                pairedEtaLogLaplaceMoment
                  (analyticZetaZeroMultiplicity rho) rho.1)) := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerTerm
    pairedEtaCompletedLeadingLogCutoffCenteredConjugateTerm
  simp only [mul_sub, map_sub]
  rw [pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho]
  ring

/-- The centered finite residual is exactly a signed combination of the two
literal centered support tails.  This is the phase-bearing finite identity
behind the norm envelope below. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_tails
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      -(pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1 *
          pairedEtaLogLaplaceMomentCutoffCenteredTail
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1 N) +
        (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              pairedEtaLogLaplaceMomentCutoffCenteredTail
                (analyticZetaZeroMultiplicity rho) rho.1 N) := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_errors]
  have hpartner :=
    pairedEtaLeadingLogLaplaceMoment_eq_cutoffCenteredPartial_add_tail
      (NontrivialZetaZero.conjugatePartner rho) N
  simp only [analyticZetaZeroMultiplicity_conjugatePartner] at hpartner
  have hrho :=
    pairedEtaLeadingLogLaplaceMoment_eq_cutoffCenteredPartial_add_tail rho N
  rw [hpartner, hrho]
  simp only [sub_add_cancel_left]
  simp only [mul_neg, map_neg]
  ring

/-- The full complex cutoff-centered partner residual is bounded by the two
completion-weighted centered Gamma tails, with no cutoff hypothesis. -/
theorem norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper rho N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_errors]
  calc
    ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1) -
          (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ ≤
        ‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1 N -
              pairedEtaLogLaplaceMoment
                (analyticZetaZeroMultiplicity rho)
                (NontrivialZetaZero.conjugatePartner rho).1)‖ +
          ‖(-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
            starRingEnd ℂ
              (pairedEtaXiCompletionFactor rho.1 * rho.1 *
                (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
                    (analyticZetaZeroMultiplicity rho) rho.1 N -
                  pairedEtaLogLaplaceMoment
                    (analyticZetaZeroMultiplicity rho) rho.1))‖ :=
      norm_sub_le _ _
    _ = pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1‖ +
        pairedEtaCompletionSpectralWeight rho *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
              (analyticZetaZeroMultiplicity rho) rho.1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1‖ := by
      simp only [pairedEtaCompletionSpectralWeight, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, one_mul, norm_conj]
    _ ≤ pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          pairedEtaLogLaplaceMomentCenteredTailUpper
            (analyticZetaZeroMultiplicity rho)
            (NontrivialZetaZero.conjugatePartner rho).1.re N +
        pairedEtaCompletionSpectralWeight rho *
          pairedEtaLogLaplaceMomentCenteredTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re N := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left
        · simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using
            (norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le
              (NontrivialZetaZero.conjugatePartner rho) N)
        · exact (pairedEtaCompletionSpectralWeight_pos
            (NontrivialZetaZero.conjugatePartner rho)).le
      · apply mul_le_mul_of_nonneg_left
        · exact
            norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le rho N
        · exact (pairedEtaCompletionSpectralWeight_pos rho).le
    _ = pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
        rho N := rfl

/-- The centered completed residual envelope is strictly positive at every
finite cutoff. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_pos
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 < pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
      rho N := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
  exact add_pos
    (mul_pos
      (pairedEtaCompletionSpectralWeight_pos
        (NontrivialZetaZero.conjugatePartner rho))
      (pairedEtaLogLaplaceMomentCenteredTailUpper_pos
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho)) N))
    (mul_pos (pairedEtaCompletionSpectralWeight_pos rho)
      (pairedEtaLogLaplaceMomentCenteredTailUpper_pos
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re rho) N))

/-- The completion-weighted centered two-tail envelope tends to zero. -/
theorem
    tendsto_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper rho N)
      atTop (nhds 0) := by
  have hpartnerTail :=
    tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
  have hrhoTail :=
    tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)
  have hpartnerWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho)) atTop
      (nhds (pairedEtaCompletionSpectralWeight
        (NontrivialZetaZero.conjugatePartner rho))) :=
    tendsto_const_nhds
  have hrhoWeight : Tendsto
      (fun _ : ℕ ↦ pairedEtaCompletionSpectralWeight rho) atTop
      (nhds (pairedEtaCompletionSpectralWeight rho)) :=
    tendsto_const_nhds
  simpa only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper,
    mul_zero, add_zero] using
    (hpartnerWeight.mul hpartnerTail).add (hrhoWeight.mul hrhoTail)

/-- The full complex cutoff-centered completed partner residual tends to zero
under the no-log-loss envelope. -/
theorem
    tendsto_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)
      atTop (nhds 0) := by
  exact squeeze_zero_norm
    (fun N ↦
      norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le rho N)
    (tendsto_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_zero
      rho)

/-- Once both former balanced-split cutoffs hold, the new centered completed
residual envelope is strictly smaller than the previous near-sharp one. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_lt_nearSharp
    (rho : NontrivialZetaZero) (N : ℕ)
    (hpartnerCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        (NontrivialZetaZero.conjugatePartner rho).1.re *
          Real.log (((2 * N + 1 : ℕ) : ℝ)))
    (hrhoCutoff :
      (((analyticZetaZeroMultiplicity rho + 1 : ℕ) : ℝ)) <
        rho.1.re * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper rho N <
      pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
        rho N := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
    pairedEtaCompletedLeadingLogFinitePartnerResidualNearSharpUpper
  exact add_lt_add
    (mul_lt_mul_of_pos_left
      (pairedEtaLogLaplaceMomentCenteredTailUpper_lt_nearSharp
        (analyticZetaZeroMultiplicity rho) N
        (NontrivialZetaZero.zero_lt_re
          (NontrivialZetaZero.conjugatePartner rho)) hpartnerCutoff)
      (pairedEtaCompletionSpectralWeight_pos
        (NontrivialZetaZero.conjugatePartner rho)))
    (mul_lt_mul_of_pos_left
      (pairedEtaLogLaplaceMomentCenteredTailUpper_lt_nearSharp
        (analyticZetaZeroMultiplicity rho) N
        (NontrivialZetaZero.zero_lt_re rho) hrhoCutoff)
      (pairedEtaCompletionSpectralWeight_pos rho))

end
end RiemannGaussian
