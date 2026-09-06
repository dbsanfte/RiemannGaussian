import RiemannGaussian.EtaCurrentFiniteMomentPair

/-!
# Finite arithmetic evaluation of the repeated-zero midpoint coefficient

The original adjacent current is paired with its physical midpoint. Its
exact finite arithmetic expression contains a diagonal order `m-1` pair
and an order `m-2,m` pair. No vanishing of the order-`m` moment is assumed.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual factored adjacent kernel is the real part of the completed
complex pair, with its original shift and multiplicity factor. -/
theorem pairedEtaAdjacentKernel_eq_completedMomentPair (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) :
    pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p =
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (pairedEtaFiniteCompletedMomentPairKernel rho (N + 2)
          (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) p).re := by
  rw [← topPrefixFiniteEnergyAdjacentMomentKernel_eq_factored]
  unfold pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel pairedEtaFiniteCompletedMomentPairKernel
  rw [etaSignedCompletedPair_eq_parity_pair (analyticZetaZeroMultiplicity rho)]
  rfl

/-- The unchanged leading current is the actual signed finite moment pair
in the repeated-zero branch. -/
theorem pairedEtaLeadingCurrent_eq_completedMomentPair (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (pairedEtaFiniteCompletedMomentPair rho (N + 2)
          (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)).re := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity rho hm N]
  simp_rw [pairedEtaAdjacentKernel_eq_completedMomentPair]
  rw [integral_const_mul, integral_etaMomentPair_re (integrable_pairedEtaFiniteCompletedMomentPairKernel rho (N + 2)
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)),
    integral_pairedEtaFiniteCompletedMomentPairKernel]

/-- The actual midpoint moment is evaluated in the existing finite eta
arithmetic, retaining the order-`m` cross term and both completed channels. -/
theorem pairedEtaLeadingCurrentMidpointMoment_eq_adjacent_arithmetic (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaLeadingCurrentMidpointMoment rho N =
      pairedEtaLogTailCutoff (N + 2) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N +
        (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          ((pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 1) (analyticZetaZeroMultiplicity rho - 1)).re +
            (pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho)).re) := by
  rw [pairedEtaLeadingCurrentMidpointMoment, if_neg (show analyticZetaZeroMultiplicity rho ≠ 1 by omega)]
  simp_rw [pairedEtaAdjacentKernel_eq_completedMomentPair]
  have he (p : ℝ × ℝ) :
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          (pairedEtaFiniteCompletedMomentPairKernel rho (N + 2)
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) p).re *
            ((p.1 + p.2) / 2) =
        2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          (pairedEtaFiniteCompletedMomentPairKernel rho (N + 2)
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) p *
              ((p.1 + p.2) / 2 : ℝ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_etaMomentPair_re (integrable_pairedEtaFiniteCompletedMomentPairKernel_midpoint rho (N + 2)
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1)),
    integral_pairedEtaFiniteCompletedMomentPairKernel_midpoint, pairedEtaLeadingCurrent_eq_completedMomentPair rho hm,
    show analyticZetaZeroMultiplicity rho - 2 + 1 = analyticZetaZeroMultiplicity rho - 1 by omega,
    show analyticZetaZeroMultiplicity rho - 1 + 1 = analyticZetaZeroMultiplicity rho by omega]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.div_ofNat_re]
  ring

end

end RiemannGaussian
