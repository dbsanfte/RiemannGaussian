import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyTransport

/-!
# Arithmetic expansion of the finite eta energy increments

The one-step energy law is useful only if its two component increments expose
the eta cutoff geometry.  This module proves the required individual
centered-prefix recurrence.

For every centered tail, the cutoff-`N` value is the newly exposed eta support
interval plus a triangular binomial combination of successor tails.  Below a
zeta zero's analytic multiplicity, complete-moment vanishing replaces every
tail in that recurrence by the negative literal finite prefix.  Thus a
consecutive finite-prefix difference is exactly one negative head interval
plus finitely many lower-order successor prefixes.

The partner and conjugate increments in the signed energy law are identified
with these explicit arithmetic works.  Substitution removes abstract
consecutive differences from the absolute energy-work estimate.  No estimate
for the resulting head-plus-hierarchy expressions is assumed here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The newly exposed eta interval contribution in absolute cutoff-centered
coordinates. -/
def pairedEtaLogLaplaceMomentCutoffCenteredHead
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
    pairedEtaShiftedLogHeadLaplaceMoment k s N

/-- Cutoff decay composes exactly with the one-step logarithmic translation. -/
theorem cexp_neg_mul_cutoff_mul_cexp_neg_mul_shiftIncrement
    (s : ℂ) (N : ℕ) :
    Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
        Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) =
      Complex.exp (-s * (pairedEtaLogTailCutoff (N + 1) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  unfold pairedEtaLogTailShiftIncrement
  push_cast
  ring

/-- Absolute-coordinate centered tails obey the exact triangular cutoff law:
one new eta interval plus every successor centered order through `k`. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredTail_transport
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail k s N =
      pairedEtaLogLaplaceMomentCutoffCenteredHead k s N +
        ∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaLogLaplaceMomentCutoffCenteredTail j s (N + 1) := by
  rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted,
    pairedEtaShiftedLogTailLaplaceMoment_transport k hs N]
  unfold pairedEtaLogLaplaceMomentCutoffCenteredHead
  rw [mul_add]
  congr 1
  calc
    Complex.exp (-s * (pairedEtaLogTailCutoff N : ℂ)) *
          (Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
            ∑ j ∈ Finset.range (k + 1),
              ((k.choose j : ℕ) : ℂ) *
                (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
                pairedEtaShiftedLogTailLaplaceMoment j s (N + 1)) =
        Complex.exp (-s * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              pairedEtaShiftedLogTailLaplaceMoment j s (N + 1) := by
      rw [← mul_assoc,
        cexp_neg_mul_cutoff_mul_cexp_neg_mul_shiftIncrement]
    _ = ∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            (Complex.exp
                (-s * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
              pairedEtaShiftedLogTailLaplaceMoment j s (N + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted]

/-- The completely finite individual centered-prefix work: one negative head
interval plus the strict lower-order successor hierarchy. -/
def pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  -pairedEtaLogLaplaceMomentCutoffCenteredHead k s N +
    ∑ j ∈ Finset.range k,
      ((k.choose j : ℕ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j s (N + 1)

/-- Below the exact zero multiplicity, the consecutive centered finite-prefix
difference is precisely its finite head-plus-lower-order work. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_succ_eq_finiteWork_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N -
        pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1) =
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k rho.1 N := by
  have htailN :=
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      rho hk N
  have htailSucc :=
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      rho hk (N + 1)
  have htransport :=
    pairedEtaLogLaplaceMomentCutoffCenteredTail_transport k
      (NontrivialZetaZero.zero_lt_re rho) N
  have hlower :
      (∑ j ∈ Finset.range k,
        ((k.choose j : ℕ) : ℂ) *
          (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
          pairedEtaLogLaplaceMomentCutoffCenteredTail j rho.1 (N + 1)) =
        -(∑ j ∈ Finset.range k,
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
              (N + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjm : j < analyticZetaZeroMultiplicity rho := hjk.trans hk
    rw [
      pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
        rho hjm (N + 1)]
    ring
  calc
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N -
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1) =
        -pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N +
          pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 (N + 1) := by
      rw [htailN, htailSucc]
      ring
    _ = -(pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 N +
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              pairedEtaLogLaplaceMomentCutoffCenteredTail j rho.1 (N + 1)) +
          pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 (N + 1) := by
      rw [htransport]
    _ = -pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 N +
        ∑ j ∈ Finset.range k,
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum j rho.1
              (N + 1) := by
      rw [Finset.sum_range_succ, hlower]
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        pow_zero]
      ring
    _ = pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k rho.1 N := rfl

/-- Explicit arithmetic realization of the partner finite-term increment. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
    (NontrivialZetaZero.conjugatePartner rho).1) *
      pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork
        (analyticZetaZeroMultiplicity rho - 1)
        (NontrivialZetaZero.conjugatePartner rho).1 (N + 1)

/-- Explicit arithmetic realization of the conjugate-original finite-term
increment. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
    starRingEnd ℂ
      ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork
          (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1))

/-- The named partner consecutive difference is exactly its new-interval and
lower-prefix arithmetic expansion. -/
theorem topPrefixFinitePartnerIncrement_eq_arithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  let k := analyticZetaZeroMultiplicity rho - 1
  have hk : k < analyticZetaZeroMultiplicity rho := by
    dsimp only [k]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hkpartner : k < analyticZetaZeroMultiplicity partner := by
    simpa only [partner, analyticZetaZeroMultiplicity_conjugatePartner] using hk
  have hwork :=
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_succ_eq_finiteWork_of_lt_multiplicity
      partner hkpartner (N + 1)
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
  change
    (pairedEtaXiCompletionFactor partner.1 * partner.1) *
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k partner.1 (N + 1) -
        (pairedEtaXiCompletionFactor partner.1 * partner.1) *
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k partner.1 (N + 2) =
      (pairedEtaXiCompletionFactor partner.1 * partner.1) *
        pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k partner.1 (N + 1)
  rw [← mul_sub]
  exact congrArg
    (fun z : ℂ =>
      (pairedEtaXiCompletionFactor partner.1 * partner.1) * z) hwork

/-- The named conjugate consecutive difference is exactly its new-interval
and lower-prefix arithmetic expansion. -/
theorem topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N := by
  let k := analyticZetaZeroMultiplicity rho - 1
  have hk : k < analyticZetaZeroMultiplicity rho := by
    dsimp only [k]
    have hm := analyticZetaZeroMultiplicity_positive rho
    omega
  have hwork :=
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_succ_eq_finiteWork_of_lt_multiplicity
      rho hk (N + 1)
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
  change
    (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ
            ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
              pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 1)) -
        (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ
            ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
              pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 2)) =
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
        starRingEnd ℂ
          ((pairedEtaXiCompletionFactor rho.1 * rho.1) *
            pairedEtaLogLaplaceMomentCutoffCenteredFiniteWork k rho.1 (N + 1))
  rw [← mul_sub, ← map_sub, ← mul_sub]
  exact congrArg
    (fun z : ℂ =>
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
        starRingEnd ℂ ((pairedEtaXiCompletionFactor rho.1 * rho.1) * z))
      hwork

/-- The absolute one-step energy estimate with both abstract differences
replaced by their literal head-plus-lower-prefix arithmetic works. -/
theorem abs_topPrefixFiniteEnergyWork_le_arithmetic_increment_energy_add_flux
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N| ≤
      Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
            rho N) +
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
            rho N) +
        2 *
          (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
                rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
                rho (N + 1)‖ +
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
                rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                rho (N + 1)‖) := by
  simpa only [topPrefixFinitePartnerIncrement_eq_arithmeticIncrement,
    topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement] using
      abs_topPrefixFiniteEnergyWork_le_increment_energy_add_flux rho N

end

end RiemannGaussian
