import RiemannGaussian.EtaEnergyFiniteWindowMomentCorrelation

/-!
# Literal interval expansion of finite eta moment correlations

This module expands every cutoff-centered eta moment in the finite-window
energy ledger into the literal logarithmic intervals retained by the paired
eta measure.  The uncompleted Gram kernel is consequently an exact finite
triple sum over cutoff coordinates and pairs of arithmetic intervals.

The expansion is propagated through the fixed completion weights, the
diagonal and distinct-zero masses, and the terminal multiplicity-aware
rank--trace ledger.  No sign or cancellation estimate for the resulting
interval correlation is assumed or proved here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder ENNReal Interval Matrix
  Topology

namespace RiemannGaussian

noncomputable section

/-- The order-`k` centered Laplace contribution from the `n`th retained
logarithmic eta interval. -/
def pairedEtaLogLaplaceCenteredMomentIntervalAtom
    (k : ℕ) (s : ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
    (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)

/-- A finite centered eta moment is exactly the sum of its retained interval
atoms. -/
theorem pairedEtaLogLaplaceMomentCenteredPartialSum_eq_sum_intervalAtoms
    (k N : ℕ) (s : ℂ) (a : ℝ) :
    pairedEtaLogLaplaceMomentCenteredPartialSum k s a N =
      ∑ n ∈ Finset.range N,
        pairedEtaLogLaplaceCenteredMomentIntervalAtom k s a n := by
  rw [pairedEtaLogLaplaceMomentCenteredPartialSum_eq_integral_finiteLogMeasure]
  unfold pairedEtaFiniteLogMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro n _hn
    unfold pairedEtaLogLaplaceCenteredMomentIntervalAtom
    rw [← intervalIntegral.integral_of_le
      (pairedEtaFiniteLogInterval_pos n).le]
  · intro n _hn
    change IntegrableOn (fun t : ℝ ↦
      (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t))
      (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))
    apply IntegrableOn.mono_set
      ((show Continuous (fun t : ℝ ↦
        (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)) by
          fun_prop).continuousOn.integrableOn_Icc)
    exact Ioc_subset_Icc_self

/-- The literal retained-interval atom in the top-prefix centered moment at a
nontrivial zero. -/
def pairedEtaTopPrefixFiniteCenteredIntervalAtom
    (rho : NontrivialZetaZero) (N n : ℕ) : ℂ :=
  pairedEtaLogLaplaceCenteredMomentIntervalAtom
    (analyticZetaZeroMultiplicity rho - 1) rho.1
      (pairedEtaLogTailCutoff (N + 1)) n

/-- The top-prefix centered moment is exactly its finite sum of literal eta
interval atoms. -/
theorem pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteCenteredMoment rho N =
      ∑ n ∈ Finset.range (N + 1),
        pairedEtaTopPrefixFiniteCenteredIntervalAtom rho N n := by
  simpa only [pairedEtaTopPrefixFiniteCenteredMoment,
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum,
    pairedEtaTopPrefixFiniteCenteredIntervalAtom, pairedEtaLogTailCutoff] using
      (pairedEtaLogLaplaceMomentCenteredPartialSum_eq_sum_intervalAtoms
        (analyticZetaZeroMultiplicity rho - 1) (N + 1) rho.1
          (Real.log (((2 * (N + 1) + 1 : ℕ) : ℝ))))

/-- The literal cutoff/interval expansion of the uncompleted finite eta
moment correlation. -/
def pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  ∑ j,
    ∑ n ∈ Finset.range (cutoff j + 1),
      ∑ m ∈ Finset.range (cutoff j + 1),
        starRingEnd ℂ
            (pairedEtaTopPrefixFiniteCenteredIntervalAtom
              sigma (cutoff j) n) *
          pairedEtaTopPrefixFiniteCenteredIntervalAtom rho (cutoff j) m

/-- The finite moment Gram kernel is exactly the finite cutoff/interval
triple correlation. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation_eq_intervalCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation
        cutoff sigma rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation
  apply Finset.sum_congr rfl
  intro j _hj
  rw [pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms,
    pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms, map_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.mul_sum]

/-- The reflection coupling after expanding its arithmetic moment kernels
into literal retained eta intervals. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCompletionWeight
          (NontrivialZetaZero.conjugatePartner sigma)) *
      pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation cutoff
        (NontrivialZetaZero.conjugatePartner sigma)
        (NontrivialZetaZero.conjugatePartner rho) +
    pairedEtaTopPrefixFiniteCompletionWeight sigma *
      starRingEnd ℂ (pairedEtaTopPrefixFiniteCompletionWeight rho) *
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation
          cutoff sigma rho)

/-- The completion-weighted reflection correlation is exactly its literal
retained-interval expansion. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation_eq_intervalCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
        cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
        cutoff sigma rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
  rw [pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation_eq_intervalCorrelation,
    pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation_eq_intervalCorrelation]

/-- The completion-weighted self-mass with each centered moment displayed as
its finite sum of retained eta interval atoms. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) : ℝ :=
  ∑ j,
    (‖pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho)‖ ^ 2 *
      ‖∑ n ∈ Finset.range (cutoff j + 1),
        pairedEtaTopPrefixFiniteCenteredIntervalAtom
          (NontrivialZetaZero.conjugatePartner rho) (cutoff j) n‖ ^ 2 +
    ‖pairedEtaTopPrefixFiniteCompletionWeight rho‖ ^ 2 *
      ‖∑ n ∈ Finset.range (cutoff j + 1),
        pairedEtaTopPrefixFiniteCenteredIntervalAtom
          rho (cutoff j) n‖ ^ 2)

/-- The weighted centered-moment self-mass equals its literal finite interval
form. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass_eq_intervalSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass
        cutoff rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass
  apply Finset.sum_congr rfl
  intro j _hj
  rw [pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms,
    pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms]

/-- The diagonal finite-window mass in literal retained-interval form. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  4 * ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass
        cutoff rho ^ 2

/-- The signed distinct-zero finite-window mass in literal retained-interval
correlation form. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (2 *
          pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
            cutoff sigma rho) ^ 2).re

/-- The weighted-moment diagonal mass equals its literal retained-interval
form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass_eq_intervalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass
  apply congrArg (4 * ·)
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass_eq_intervalSelfMass]

/-- The weighted-moment distinct-zero mass equals its literal retained-
interval correlation form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass_eq_intervalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation_eq_intervalCorrelation]

/-- The coherent finite eta Frobenius mass is exactly the sum of its literal
interval-expanded diagonal and distinct-zero terms. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_intervalDiagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_weightedMomentDiagonal_add_offDiagonal,
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass_eq_intervalMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass_eq_intervalMass]

/-- The multiplicity-aware eta rank--trace ledger with every finite arithmetic
moment expanded into its literal retained logarithmic interval atoms. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_intervalCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
        cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h :=
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_weightedMoment_ledger
      cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass_eq_intervalMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass_eq_intervalMass]
    at h
  exact h

end

end RiemannGaussian
