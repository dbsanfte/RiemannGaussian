import RiemannGaussian.EtaMoebiusInverseWeights

/-!
# Exact odd-aggregate reconstruction of the original simple-zero current

The head/prefix current is reconstructed with the actual inverse divisor
weights, both completion channels, and each divided cutoff intact. The
identity is proved before taking the real part. A uniform bound on the
unweighted parity aggregates alone does not estimate this weighted sum.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual complex head/prefix pair is the sum of inverse-weighted
odd aggregates at their divided physical cutoffs. Both completed channels
and the original conjugation orientation survive the finite inversion. -/
theorem pairedEtaHeadCompletedMomentPair_zero_eq_oddInverse (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMomentPair rho N 0 0 =
      ∑ d ∈ (Finset.Icc 1 (2 * (N + 2))).filter Odd,
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
          (pairedEtaCompletedOddInverseTerm (NontrivialZetaZero.conjugatePartner rho) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment rho N 0)
          (pairedEtaCompletedOddInverseTerm rho (2 * (N + 2)) d) := by
  unfold pairedEtaHeadCompletedMomentPair
  rw [pairedEtaFiniteCompletedMoment_zero_eq_oddInverse,
    pairedEtaFiniteCompletedMoment_zero_eq_oddInverse]
  simp only [etaSignedCompletedPair, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum]

/-- At a simple actual zero, the unchanged leading current is exactly
the real part of the reconstructed weighted odd-aggregate sum. This is
the transfer identity; estimating the signed weighted sum remains open. -/
theorem pairedEtaLeadingCurrent_eq_oddInverse_head (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (∑ d ∈ (Finset.Icc 1 (2 * (N + 2))).filter Odd,
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
          (pairedEtaCompletedOddInverseTerm (NontrivialZetaZero.conjugatePartner rho) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment rho N 0)
          (pairedEtaCompletedOddInverseTerm rho (2 * (N + 2)) d)).re := by
  rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm,
    pairedEtaHeadCompletedMomentPair_zero_eq_oddInverse]

end

end RiemannGaussian
