import RiemannGaussian.EtaMomentMoebiusInverse

/-!
# Möbius reconstruction of both original signed-current branches

The full moment inversion is inserted into the unchanged completed
arithmetic current. Repeated zeros use a double divisor sum of adjacent
orders; simple zeros use the original head paired with an order-zero
inverse sum. Both completion channels, conjugation orientations, shifted
centers, and physical cutoffs remain present before taking real parts.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact complex signed finite moment pair is a double sum of
inverse features, preserving both independent divisor cutoffs and centers. -/
theorem pairedEtaFiniteCompletedMomentPair_eq_momentInverse
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    pairedEtaFiniteCompletedMomentPair rho N k l =
      ∑ d ∈ Finset.Icc 1 (2 * N), ∑ e ∈ Finset.Icc 1 (2 * N),
        etaSignedCompletedPair
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho) k
            (pairedEtaLogTailCutoff N) (2 * N) d)
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho) l
            (pairedEtaLogTailCutoff N) (2 * N) e)
          (pairedEtaCompletedMomentInverseTerm rho k (pairedEtaLogTailCutoff N) (2 * N) d)
          (pairedEtaCompletedMomentInverseTerm rho l (pairedEtaLogTailCutoff N) (2 * N) e) := by
  unfold pairedEtaFiniteCompletedMomentPair
  simp_rw [pairedEtaFiniteCompletedMoment_eq_momentInverse]
  simp only [etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]
  congr 1 <;> exact Finset.sum_comm

/-- The unchanged repeated-zero current has an exact inverse formula
at the two adjacent moment orders forced by its analytic multiplicity. -/
theorem pairedEtaLeadingCurrent_eq_momentInverse_adjacent
    (rho : NontrivialZetaZero) (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (∑ d ∈ Finset.Icc 1 (2 * (N + 2)), ∑ e ∈ Finset.Icc 1 (2 * (N + 2)),
          etaSignedCompletedPair
            (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho)
              (analyticZetaZeroMultiplicity rho - 2) (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
            (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho)
              (analyticZetaZeroMultiplicity rho - 1) (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) e)
            (pairedEtaCompletedMomentInverseTerm rho (analyticZetaZeroMultiplicity rho - 2)
              (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
            (pairedEtaCompletedMomentInverseTerm rho (analyticZetaZeroMultiplicity rho - 1)
              (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) e)).re := by
  rw [pairedEtaLeadingCurrent_eq_completedMomentPair rho hm,
    pairedEtaFiniteCompletedMomentPair_eq_momentInverse]

/-- The complex head pair uses the same complete inverse transform
without replacing the head's coordinate or its completion phase. -/
theorem pairedEtaHeadCompletedMomentPair_zero_eq_momentInverse
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMomentPair rho N 0 0 =
      ∑ d ∈ Finset.Icc 1 (2 * (N + 2)),
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho) 0
            (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment rho N 0)
          (pairedEtaCompletedMomentInverseTerm rho 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d) := by
  unfold pairedEtaHeadCompletedMomentPair
  rw [pairedEtaFiniteCompletedMoment_eq_momentInverse,
    pairedEtaFiniteCompletedMoment_eq_momentInverse]
  simp only [etaSignedCompletedPair, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum]

/-- The unchanged simple-zero current retains its exact head and full
inverse-weighted moment sum, with every center translation explicit. -/
theorem pairedEtaLeadingCurrent_eq_momentInverse_head
    (rho : NontrivialZetaZero) (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (∑ d ∈ Finset.Icc 1 (2 * (N + 2)),
        etaSignedCompletedPair
          (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
          (pairedEtaCompletedMomentInverseTerm (NontrivialZetaZero.conjugatePartner rho) 0
            (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)
          (pairedEtaHeadCompletedMoment rho N 0)
          (pairedEtaCompletedMomentInverseTerm rho 0 (pairedEtaLogTailCutoff (N + 2)) (2 * (N + 2)) d)).re := by
  rw [pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm,
    pairedEtaHeadCompletedMomentPair_zero_eq_momentInverse]

end

end RiemannGaussian
