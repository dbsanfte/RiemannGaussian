import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualSharpAsymptotic

/-!
# Critical-scale rigidity for the completed centered eta residual

The sharp residual asymptotic separates off-line zeros at the critical
square-root scale.  If `Re rho > 1/2`, the residual decays with the slower
partner exponent `1 - Re rho < 1/2`; hence multiplication by
`(2N+1)^(1/2)` makes its norm diverge to infinity.  Reflection gives the same
obstruction in one orientation of every off-critical complementary pair.

This module packages the resulting exact arithmetic target: eventual boundedness
of the critical-scale residual at every nontrivial zero.  Lean proves that
this statement implies RH.  Conversely, RH makes both centered-tail envelopes
have exponent `1/2`, which proves the boundedness statement.  Thus the new
criterion is an RH-equivalent residual-rate reformulation.  Its arithmetic
direction remains open; the equivalence itself is not a proof of RH.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- At a hypothetical right-half zero, the completed centered residual is too
large for the critical square-root normalization: that normalized norm tends
to positive infinity. -/
theorem
    tendsto_oddEndpoint_half_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_atTop_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖)
      atTop atTop := by
  let partner : NontrivialZetaZero :=
    NontrivialZetaZero.conjugatePartner rho
  have hpartnerRate :=
    tendsto_oddEndpoint_partner_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual
      rho hrho
  have hgap : 0 < (1 / 2 : ℝ) - partner.1.re := by
    have hpartnerRe : partner.1.re = 1 - rho.1.re := by
      simp [partner, NontrivialZetaZero.conjugatePartner_coe]
    rw [hpartnerRe]
    linarith
  have hbase : Tendsto (fun N : ℕ => (2 : ℝ) * N + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  have hfactor : Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - partner.1.re))
      atTop atTop := by
    convert (tendsto_rpow_atTop hgap).comp hbase using 1
    funext N
    norm_num
  have hproduct := hfactor.atTop_mul_pos
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualSharpLimit_pos
      rho)
    hpartnerRate
  convert hproduct using 1
  funext N
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  symm
  change x ^ ((1 / 2 : ℝ) - partner.1.re) *
      (x ^ partner.1.re *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖) =
    x ^ (1 / 2 : ℝ) *
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖
  rw [← mul_assoc, ← Real.rpow_add hx]
  congr 2
  ring

/-- Consequently no eventual finite upper bound can hold at the critical
scale for a right-half off-line zero. -/
theorem
    not_exists_eventually_oddEndpoint_half_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤ C := by
  rintro ⟨C, hupper⟩
  have hlower :=
    (tendsto_oddEndpoint_half_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_atTop_of_half_lt_re
      rho hrho).eventually_gt_atTop C
  obtain ⟨N, hle, hlt⟩ := (hupper.and hlower).exists
  exact (not_lt_of_ge hle hlt)

/-- The global arithmetic residual-rate statement: at every nontrivial zero,
the actual completed centered residual is eventually bounded after the
critical square-root normalization. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded :
    Prop :=
  ∀ rho : NontrivialZetaZero, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤ C

/-- Global critical-scale boundedness forces every nontrivial zero onto the
critical line. -/
theorem
    nontrivialZetaZero_re_eq_half_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded
    (hbounded :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded)
    (rho : NontrivialZetaZero) :
    rho.1.re = 1 / 2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleft | hright
  · have hpartnerRight :
        1 / 2 < (NontrivialZetaZero.conjugatePartner rho).1.re := by
      have h : 1 / 2 < 1 - rho.1.re := by linarith
      simpa [NontrivialZetaZero.conjugatePartner_coe] using h
    exact
      (not_exists_eventually_oddEndpoint_half_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le_of_half_lt_re
        (NontrivialZetaZero.conjugatePartner rho) hpartnerRight)
        (hbounded (NontrivialZetaZero.conjugatePartner rho))
  · exact
      (not_exists_eventually_oddEndpoint_half_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le_of_half_lt_re
        rho hright) (hbounded rho)

/-- The global critical-scale residual bound implies Mathlib's Riemann
hypothesis. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded
    (hbounded :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_spectralCoordinate_real]
  intro s hs hnontrivial hone
  let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
  exact (zetaSpectralCoordinate_im_eq_zero_iff s).2
    (nontrivialZetaZero_re_eq_half_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded
      hbounded rho)

/-- On the critical line, the existing two-tail envelope becomes a constant
after square-root normalization. -/
theorem
    oddEndpoint_half_rpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_eq_of_re_eq_half
    (rho : NontrivialZetaZero) (hre : rho.1.re = 1 / 2) (N : ℕ) :
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper rho N =
      pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
          (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
            (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)) +
        pairedEtaCompletionSpectralWeight rho *
          (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
            (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)) := by
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hpartnerRe :
      (NontrivialZetaZero.conjugatePartner rho).1.re = 1 / 2 := by
    simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
      Complex.one_re, Complex.conj_re, hre]
    ring
  have hcancel : x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hx]
    norm_num
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper
  rw [pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow,
    pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow,
    hpartnerRe, hre]
  change x ^ (1 / 2 : ℝ) *
      (pairedEtaCompletionSpectralWeight
            (NontrivialZetaZero.conjugatePartner rho) *
          (x ^ (-(1 / 2 : ℝ)) *
            (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
              (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1))) +
        pairedEtaCompletionSpectralWeight rho *
          (x ^ (-(1 / 2 : ℝ)) *
            (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
              (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)))) = _
  calc
    _ = (x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ))) *
        (pairedEtaCompletionSpectralWeight
              (NontrivialZetaZero.conjugatePartner rho) *
            (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
              (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)) +
          pairedEtaCompletionSpectralWeight rho *
            (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
              (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1))) := by
      ring
    _ = _ := by rw [hcancel, one_mul]

/-- RH supplies the global critical-scale residual bound via the explicit
centered-tail envelope. -/
theorem
    all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded := by
  intro rho
  have him : (zetaSpectralCoordinate rho.1).im = 0 :=
    (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  have hre : rho.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
  refine ⟨
    pairedEtaCompletionSpectralWeight
          (NontrivialZetaZero.conjugatePartner rho) *
          (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
            (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)) +
      pairedEtaCompletionSpectralWeight rho *
          (((analyticZetaZeroMultiplicity rho).factorial : ℝ) /
            (1 / 2 : ℝ) ^ (analyticZetaZeroMultiplicity rho + 1)),
    Eventually.of_forall fun N => ?_⟩
  calc
    (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N‖ ≤
        (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper rho N :=
      mul_le_mul_of_nonneg_left
        (norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_le
          rho N)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ :=
      oddEndpoint_half_rpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualUpper_eq_of_re_eq_half
        rho hre N

/-- Critical-scale eventual boundedness of every completed centered residual
is exactly equivalent to RH.  The forward arithmetic bound is still open. -/
theorem
    riemannHypothesis_iff_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded :
    RiemannHypothesis ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualCriticalScaleEventuallyBounded := by
  constructor
  · exact
      all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded_of_riemannHypothesis
  · exact
      riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_criticalScale_eventuallyBounded

end

end RiemannGaussian
