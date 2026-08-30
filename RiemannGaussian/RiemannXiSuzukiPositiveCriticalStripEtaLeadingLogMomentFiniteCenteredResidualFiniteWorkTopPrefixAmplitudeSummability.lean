import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixAmplitudeAsymptotic

/-!
# Summability frontier for complementary top-prefix amplitudes

The sharp amplitude asymptotic is converted here into a Hilbert-space-shaped
criterion.  The amplitude imbalance is already the square of the difference
between two positive component magnitudes.  Lean proves that its series over
all cutoffs is summable exactly when the zero lies on the critical line.

Consequently, a genuine arithmetic Bessel or orthogonality theorem proving
this summability at every zero would prove RH.  No such theorem is assumed or
proved here: the global equivalence is a closure interface for that proposed
attack.
-/

open Asymptotics Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real `p`-series on the positive odd endpoints has the usual strict
summability threshold. -/
theorem summable_oddEndpoint_rpow_neg_iff (p : ℝ) :
    Summable (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ) ^ (-p)) ↔ 1 < p := by
  have hfun :
      (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ) ^ (-p)) =
        (fun N : ℕ =>
          (2 : ℝ) ^ (-p) *
            (1 / |(N : ℝ) + 1 / 2| ^ p)) := by
    funext N
    have hz : 0 < (N : ℝ) + 1 / 2 := by positivity
    have hx : ((2 * N + 1 : ℕ) : ℝ) =
        2 * ((N : ℝ) + 1 / 2) := by
      push_cast
      ring
    rw [hx, abs_of_pos hz, Real.mul_rpow (by norm_num) hz.le,
      Real.rpow_neg hz.le]
    simp only [one_div]
  rw [hfun,
    summable_mul_left_iff
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-p)).ne',
    Real.summable_one_div_nat_add_rpow]

/-- The squared complementary-amplitude mismatch is unchanged by reflection
across the critical line. -/
theorem
    topPrefixAmplitudeImbalance_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        (NontrivialZetaZero.conjugatePartner rho) N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
  rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail,
    norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail]
  simp only [NontrivialZetaZero.conjugatePartner_conjugatePartner,
    analyticZetaZeroMultiplicity_conjugatePartner]
  ring

/-- On the critical line the two component magnitudes agree at every cutoff,
so the amplitude imbalance vanishes identically. -/
theorem
    topPrefixAmplitudeImbalance_eq_zero_of_re_eq_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re = 1 / 2) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N = 0 := by
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho := by
    apply Subtype.ext
    apply Complex.ext
    · simp [NontrivialZetaZero.conjugatePartner_coe, hrho]
      norm_num
    · simp [NontrivialZetaZero.conjugatePartner_coe]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
  rw [norm_topPrefixPartnerComponent_eq_completionWeight_mul_norm_partnerTail,
    norm_topPrefixConjugateComponent_eq_completionWeight_mul_norm_rhoTail,
    hpartner]
  ring

/-- At a right-half zero, the squared complementary-amplitude mismatch is not
summable over the cutoff.  Its sharp decay exponent is strictly below the
harmonic threshold. -/
theorem
    not_summable_topPrefixAmplitudeImbalance_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ¬Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let p : ℝ := 2 * partner.1.re
  let L : ℝ :=
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
      rho) ^ 2
  have hpartnerRe : partner.1.re = 1 - rho.1.re := by
    simp [partner, NontrivialZetaZero.conjugatePartner_coe]
  have hp_lt : p < 1 := by
    dsimp only [p]
    rw [hpartnerRe]
    linarith
  have hLpos : 0 < L := by
    dsimp only [L]
    exact pow_pos (topPrefixPartnerAmplitudeSharpLimit_pos rho) 2
  have hnormalized :=
    tendsto_oddEndpoint_two_mul_partner_rpow_mul_topPrefixAmplitudeImbalance_of_half_lt_re
      rho hrho
  have hratio : Tendsto (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N /
        (L * ((2 * N + 1 : ℕ) : ℝ) ^ (-p)))
      atTop (nhds 1) := by
    have hscaled := hnormalized.div_const L
    have hconverted := hscaled.congr' (Eventually.of_forall fun N => by
        let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
        let A : ℝ :=
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
            rho N
        have hx : 0 < x := by
          dsimp only [x]
          positivity
        change (x ^ (2 * partner.1.re) * A) / L =
          A / (L * x ^ (-p))
        dsimp only [p]
        rw [Real.rpow_neg hx.le]
        field_simp [hLpos.ne',
          (Real.rpow_pos_of_pos hx (2 * partner.1.re)).ne'])
    convert hconverted using 1
    rw [show
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerAmplitudeSharpLimit
        rho) ^ 2 = L by rfl, div_self hLpos.ne']
  have hequivalent :
      (fun N : ℕ =>
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N) ~[atTop]
        (fun N : ℕ => L * ((2 * N + 1 : ℕ) : ℝ) ^ (-p)) :=
    Asymptotics.isEquivalent_of_tendsto_one hratio
  have hbaseNot :
      ¬Summable (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ) ^ (-p)) := by
    intro hsum
    have hp := (summable_oddEndpoint_rpow_neg_iff p).mp hsum
    linarith
  have hmodelNot :
      ¬Summable (fun N : ℕ =>
        L * ((2 * N + 1 : ℕ) : ℝ) ^ (-p)) := by
    intro hsum
    exact hbaseNot ((summable_mul_left_iff hLpos.ne').mp hsum)
  intro hsum
  exact hmodelNot (hequivalent.summable_iff_nat.mp hsum)

/-- Reflection transfers the nonsummability obstruction to a left-half zero. -/
theorem
    not_summable_topPrefixAmplitudeImbalance_of_re_lt_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re < 1 / 2) :
    ¬Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  have hpartner : 1 / 2 < partner.1.re := by
    have hpartnerRe : partner.1.re = 1 - rho.1.re := by
      simp [partner, NontrivialZetaZero.conjugatePartner_coe]
    rw [hpartnerRe]
    linarith
  have hnot :=
    not_summable_topPrefixAmplitudeImbalance_of_half_lt_re partner hpartner
  intro hsum
  apply hnot
  exact hsum.congr fun N =>
    (topPrefixAmplitudeImbalance_conjugatePartner rho N).symm

/-- Local `ell^2` classification: the complementary component-magnitude
difference is square-summable over cutoffs exactly on the critical line. -/
theorem
    summable_topPrefixAmplitudeImbalance_iff_re_eq_half
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N) ↔
      rho.1.re = 1 / 2 := by
  constructor
  · intro hsum
    rcases lt_trichotomy rho.1.re (1 / 2 : ℝ) with hleft | hline | hright
    · exact False.elim
        (not_summable_topPrefixAmplitudeImbalance_of_re_lt_half rho hleft hsum)
    · exact hline
    · exact False.elim
        (not_summable_topPrefixAmplitudeImbalance_of_half_lt_re rho hright hsum)
  · intro hrho
    have hzero :
        (fun N : ℕ =>
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
            rho N) = fun _ => 0 := by
      funext N
      exact topPrefixAmplitudeImbalance_eq_zero_of_re_eq_half rho hrho N
    rw [hzero]
    exact summable_zero

/-- The global arithmetic `ell^2` target for the complementary top-prefix
amplitude mismatch. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceSummable :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    Summable (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
        rho N)

/-- Global square-summability of the finite complementary-amplitude mismatch
is exactly RH.  This is a reduction, not a proof of the open arithmetic
direction. -/
theorem
    riemannHypothesis_iff_all_topPrefixAmplitudeImbalance_summable :
    RiemannHypothesis ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalanceSummable := by
  constructor
  · intro hRH rho
    apply (summable_topPrefixAmplitudeImbalance_iff_re_eq_half rho).2
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    exact (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1 him
  · intro hsummable
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnontrivial hone
    let rho : NontrivialZetaZero := ⟨s, hs, hnontrivial, hone⟩
    apply (zetaSpectralCoordinate_im_eq_zero_iff s).2
    exact (summable_topPrefixAmplitudeImbalance_iff_re_eq_half rho).1
      (hsummable rho)

end

end RiemannGaussian
