import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualSharpAsymptotic

/-!
# Complex off-line asymptotic of the completed centered eta residual

The previous residual theorem retained only the norm after normalization by
the slower complementary horizontal rate.  Signed finite-work analysis also
needs the complex phase.  Here the residual is normalized by the full complex
odd-endpoint power at the reflected partner.

For `Re rho > 1/2`, the completed original tail vanishes under this
normalization, while the reflected-partner tail converges to its explicit
Gamma-moment constant.  The full normalized residual therefore has an exact
nonzero complex limit.  No phase or completion factor is discarded.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complex leading constant of the right-half off-line completed
centered residual after normalization at the reflected-partner exponent. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
    (rho : NontrivialZetaZero) : ℂ :=
  -(pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1) *
    ((((analyticZetaZeroMultiplicity rho).factorial : ℕ) : ℂ) *
      ((NontrivialZetaZero.conjugatePartner rho).1 ^
        (analyticZetaZeroMultiplicity rho + 1))⁻¹ / 2)

/-- The norm of the complex leading constant is exactly the positive sharp
limit previously obtained from rate separation. -/
theorem
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit_eq
    (rho : NontrivialZetaZero) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
        rho‖ =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
        rho := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit
    pairedEtaCompletionSpectralWeight
  simp only [norm_neg, norm_mul]

/-- The complex residual leading constant is nonzero. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
      rho ≠ 0 := by
  apply norm_pos_iff.mp
  rw [
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit_eq]
  exact
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit_pos rho

/-- At a right-half zero, the faster completed original tail tends to zero
after normalization by the full complex partner endpoint power. -/
theorem
    tendsto_oddEndpoint_partner_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredOriginalTail_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          (NontrivialZetaZero.conjugatePartner rho).1 *
        ((-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              pairedEtaLogLaplaceMomentCutoffCenteredTail
                (analyticZetaZeroMultiplicity rho) rho.1 N)))
      atTop (nhds 0) := by
  have hpartnerLt :
      (NontrivialZetaZero.conjugatePartner rho).1.re < rho.1.re := by
    have h : 1 - rho.1.re < rho.1.re := by linarith
    simpa [NontrivialZetaZero.conjugatePartner_coe] using h
  have htail :=
    tendsto_oddEndpoint_smaller_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) hpartnerLt
  have hweighted := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight rho) htail
  apply squeeze_zero_norm (a := fun N : ℕ =>
      pairedEtaCompletionSpectralWeight rho *
        ((((2 * N + 1 : ℕ) : ℝ) ^
            (NontrivialZetaZero.conjugatePartner rho).1.re) *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
            (analyticZetaZeroMultiplicity rho) rho.1 N‖))
  · intro N
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    unfold pairedEtaCompletionSpectralWeight
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_conj]
    ring_nf
    exact le_rfl
  · simpa only [mul_zero] using hweighted

/-- The slower completed reflected-partner tail retains its full complex
leading constant under partner endpoint normalization. -/
theorem
    tendsto_oddEndpoint_partner_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerTail
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          (NontrivialZetaZero.conjugatePartner rho).1 *
        (-(pairedEtaXiCompletionFactor
              (NontrivialZetaZero.conjugatePartner rho).1 *
            (NontrivialZetaZero.conjugatePartner rho).1 *
            pairedEtaLogLaplaceMomentCutoffCenteredTail
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1 N)))
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
          rho)) := by
  have htail :=
    tendsto_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
  have hscaled := Filter.Tendsto.const_mul
    (-(pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1)) htail
  simpa only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit]
    using hscaled.congr' (Eventually.of_forall fun N => by ring)

/-- Full complex sharp asymptotic of the actual completed centered residual
at every hypothetical right-half off-line zero. -/
theorem
    tendsto_oddEndpoint_partner_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
          rho)) := by
  have hpartner :=
    tendsto_oddEndpoint_partner_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerTail
      rho
  have horiginal :=
    tendsto_oddEndpoint_partner_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredOriginalTail_zero
      rho hrho
  have hsum := hpartner.add horiginal
  simpa only [add_zero] using hsum.congr' (Eventually.of_forall fun N => by
    rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_tails]
    ring)

end

end RiemannGaussian
