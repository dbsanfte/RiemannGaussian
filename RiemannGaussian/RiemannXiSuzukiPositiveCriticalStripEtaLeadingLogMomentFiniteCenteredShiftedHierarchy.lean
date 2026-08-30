import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredShiftedTransport

/-!
# Finite closure of the centered eta transport hierarchy

The cutoff transport law for the completed centered eta residual contains
shifted coupled moments of every order below the analytic zero multiplicity.
Those successor tails are not independent infinite data.  At an order
`k < m`, every uncentered eta moment through order `k` vanishes at the zero,
so the complete centered order-`k` moment vanishes as well.  Its literal tail
is therefore exactly the negative of its finite centered prefix.

This module proves that statement for arbitrary multiplicity and both members
of the functional-equation pair.  It then restores all completion factors,
conjugation, parity, and cutoff phases to identify every lower shifted coupled
moment with one explicit finite-prefix coupling.  Substitution closes the
residual work law into a finite arithmetic identity: its only new local term
is the first translated support interval, and its remaining hierarchy is a
finite sum of literal eta prefixes.  Obtaining a coercive sign or cancellation
estimate for this finite identity remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complete centered order-`k` eta moment, written as the binomial
combination of the ordinary complete logarithmic moments. -/
def pairedEtaLogLaplaceMomentCenteredFullSum
    (k : ℕ) (s : ℂ) (a : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1),
    ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
      pairedEtaLogLaplaceMoment j s

/-- Every complete centered moment splits exactly into its finite centered
prefix and its literal centered support tail. -/
theorem pairedEtaLogLaplaceMomentCenteredFullSum_eq_partial_add_tail
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (a : ℝ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCenteredFullSum k s a =
      pairedEtaLogLaplaceMomentCenteredPartialSum k s a N +
        ∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N := by
  unfold pairedEtaLogLaplaceMomentCenteredFullSum
    pairedEtaLogLaplaceMomentCenteredPartialSum
  calc
    (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          pairedEtaLogLaplaceMoment j s) =
      ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          (pairedEtaLogLaplaceMomentPartialSum j s N +
            ∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-s * t)
              ∂pairedEtaLogTailMeasure N) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [pairedEtaLogLaplaceMoment_eq_partialSum_add_tail j hs N]
    _ = (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          pairedEtaLogLaplaceMomentPartialSum j s N) +
      ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          (∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-s * t)
            ∂pairedEtaLogTailMeasure N) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          pairedEtaLogLaplaceMomentPartialSum j s N) +
        ∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N := by
      rw [sum_pairedEtaLogLaplaceMoment_centeredTail_eq_integral k hs a N]

/-- At a zero of multiplicity `m`, every complete centered moment of order
strictly below `m` vanishes, for every real center. -/
theorem pairedEtaLogLaplaceMomentCenteredFullSum_eq_zero_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (a : ℝ) :
    pairedEtaLogLaplaceMomentCenteredFullSum k rho.1 a = 0 := by
  unfold pairedEtaLogLaplaceMomentCenteredFullSum
  apply Finset.sum_eq_zero
  intro j hj
  have hjm : j < analyticZetaZeroMultiplicity rho := by
    have hjlt : j < k + 1 := Finset.mem_range.mp hj
    have hjk : j ≤ k := by omega
    exact hjk.trans_lt hk
  rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hjm,
    mul_zero]

/-- Below the zero multiplicity, a cutoff-centered finite prefix plus its
literal centered tail is exactly zero. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredPartial_add_tail_eq_zero_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N +
        pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N = 0 := by
  let a := pairedEtaLogTailCutoff N
  have hsplit :=
    pairedEtaLogLaplaceMomentCenteredFullSum_eq_partial_add_tail k
      (NontrivialZetaZero.zero_lt_re rho) a N
  have hzero :=
    pairedEtaLogLaplaceMomentCenteredFullSum_eq_zero_of_lt_multiplicity
      rho hk a
  rw [hzero] at hsplit
  simpa only [pairedEtaLogLaplaceMomentCutoffCenteredPartialSum,
    pairedEtaLogLaplaceMomentCutoffCenteredTail, pairedEtaLogTailCutoff,
    a] using hsplit.symm

/-- Equivalently, every lower cutoff-centered tail is the negative of the
literal finite centered prefix. -/
theorem pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N =
      -pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N := by
  have h :=
    pairedEtaLogLaplaceMomentCutoffCenteredPartial_add_tail_eq_zero_of_lt_multiplicity
      rho hk N
  linear_combination h

/-- Restoring the cutoff phase identifies an arbitrary shifted coupled order
with the same completion-weighted combination of the two literal centered
tails.  This identity does not use lower-order vanishing. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_tails
    (rho : NontrivialZetaZero) (k N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
        rho k N =
      -(pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1 *
          pairedEtaLogLaplaceMomentCutoffCenteredTail k
            (NontrivialZetaZero.conjugatePartner rho).1 N) +
        (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N) := by
  rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted
      k (NontrivialZetaZero.conjugatePartner rho).1 N,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_decay_mul_oscillation_mul_shifted
      k rho.1 N]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
  simp only [NontrivialZetaZero.conjugatePartner_coe,
    Complex.sub_re, Complex.one_re, Complex.conj_re,
    Complex.sub_im, Complex.one_im, Complex.conj_im,
    zero_sub, neg_neg, map_mul, conj_ofReal]
  rw [star_pairedEtaLogTailCutoffOscillation,
    star_pairedEtaShiftedLogTailFourierMoment]
  ring

/-- The completely finite arithmetic coupling that replaces a shifted tail
order below the analytic zero multiplicity.  Its parity remains the parity of
the leading order because it arises inside the leading residual transport. -/
def pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
    (rho : NontrivialZetaZero) (k N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1 *
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k
        (NontrivialZetaZero.conjugatePartner rho).1 N -
    (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
      starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 * rho.1 *
          pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N)

/-- Every shifted coupled order below the zero multiplicity is exactly its
literal finite-prefix coupling; no infinite tail remains on the right. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_finitePrefix_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
        rho k N =
      pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
        rho k N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_tails]
  have hpartner :
      k < analyticZetaZeroMultiplicity
        (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk
  rw [pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      (NontrivialZetaZero.conjugatePartner rho) hpartner N,
    pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity
      rho hk N]
  unfold pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
  simp only [mul_neg, map_neg]
  ring

/-- The actual leading residual work law has a completely finite lower-order
hierarchy: every successor term below multiplicity is a literal finite eta
prefix coupling. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ_eq_finitePrefixHierarchy
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho (N + 1) =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
            rho (analyticZetaZeroMultiplicity rho) N +
        ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho),
          ((((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^
              (analyticZetaZeroMultiplicity rho - j)) *
            pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
              rho j (N + 1) := by
  calc
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N -
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho (N + 1) =
        pairedEtaLogTailCutoffOscillation rho.1.im N *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
              rho (analyticZetaZeroMultiplicity rho) N +
          ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho),
            ((((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^
                (analyticZetaZeroMultiplicity rho - j)) *
              pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
                rho j (N + 1) :=
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ rho N
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_finitePrefix_of_lt_multiplicity
        rho (Finset.mem_range.mp hj) (N + 1)]

end

end RiemannGaussian
