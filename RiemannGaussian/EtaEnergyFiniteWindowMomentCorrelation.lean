import RiemannGaussian.EtaEnergyFiniteWindowReflectionCorrelation

/-!
# Spectral-weight factorization of finite eta moment correlations

This module factors the fixed completed spectral weight
`pairedEtaXiCompletionFactor rho * rho` out of the single original eta
channel.  The remaining Gram kernel is a finite correlation of literal
cutoff-centered eta moment prefixes.  Thus the reflection-coupled
distinct-zero term is separated exactly into fixed spectral weights and
finite arithmetic moment correlations.

No estimate for that finite correlation is assumed or proved here.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The fixed complex completion weight multiplying every finite eta prefix
at a nontrivial zero. -/
def pairedEtaTopPrefixFiniteCompletionWeight
    (rho : NontrivialZetaZero) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 * rho.1

/-- The literal order-`m-1` cutoff-centered finite eta moment used by the
top-prefix channel. -/
def pairedEtaTopPrefixFiniteCenteredMoment
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
    (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)

/-- The original completed channel is its fixed spectral weight times its
finite centered eta moment. -/
theorem originalChannelTerm_eq_completionWeight_mul_centeredMoment
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteOriginalChannelTerm rho N =
      pairedEtaTopPrefixFiniteCompletionWeight rho *
        pairedEtaTopPrefixFiniteCenteredMoment rho N := by
  rfl

/-- The finite Gram correlation of the uncompleted cutoff-centered eta
moments. -/
def pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  ∑ j,
    starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCenteredMoment sigma (cutoff j)) *
      pairedEtaTopPrefixFiniteCenteredMoment rho (cutoff j)

/-- The uncompleted finite-moment correlation has Hermitian conjugate
symmetry. -/
theorem momentCorrelation_swap
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation cutoff rho sigma =
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
          cutoff sigma rho) := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

/-- The original completed-channel correlation factors into two fixed
spectral weights and the finite eta-moment correlation. -/
theorem originalChannelCorrelation_eq_completionWeights_mul_momentCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
        cutoff sigma rho =
      starRingEnd ℂ (pairedEtaTopPrefixFiniteCompletionWeight sigma) *
        pairedEtaTopPrefixFiniteCompletionWeight rho *
          pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
            cutoff sigma rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [originalChannelTerm_eq_completionWeight_mul_centeredMoment,
    originalChannelTerm_eq_completionWeight_mul_centeredMoment, map_mul]
  ring

/-- The single finite eta-moment correlation coupled to its reflected copy,
including only the explicit fixed spectral weights outside the arithmetic
kernel. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCompletionWeight
          (NontrivialZetaZero.conjugatePartner sigma)) *
      pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation cutoff
        (NontrivialZetaZero.conjugatePartner sigma)
        (NontrivialZetaZero.conjugatePartner rho) +
    pairedEtaTopPrefixFiniteCompletionWeight sigma *
      starRingEnd ℂ (pairedEtaTopPrefixFiniteCompletionWeight rho) *
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCutoffFamilyMomentCorrelation
          cutoff sigma rho)

/-- The same-channel feature correlation is the weighted reflection coupling
of the finite eta-moment Gram kernel. -/
theorem sameChannelCorrelation_eq_weightedReflectionCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
        cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
        cutoff sigma rho := by
  rw [sameChannelCorrelation_eq_reflectedOriginal_add_star_original,
    originalChannelCorrelation_eq_completionWeights_mul_momentCorrelation,
    originalChannelCorrelation_eq_completionWeights_mul_momentCorrelation]
  unfold pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
  simp only [map_mul, starRingEnd_apply, star_star]

/-- The completion-weighted finite-moment self-mass at a zero and its
reflected partner. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) : ℝ :=
  ∑ j,
    (‖pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho)‖ ^ 2 *
      ‖pairedEtaTopPrefixFiniteCenteredMoment
        (NontrivialZetaZero.conjugatePartner rho) (cutoff j)‖ ^ 2 +
    ‖pairedEtaTopPrefixFiniteCompletionWeight rho‖ ^ 2 *
      ‖pairedEtaTopPrefixFiniteCenteredMoment rho (cutoff j)‖ ^ 2)

/-- The one-channel reflected self-mass factors into completion weights and
finite centered-moment norms. -/
theorem reflectedOriginalSelfMass_eq_weightedMomentSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
        cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass
        cutoff rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass
  apply Finset.sum_congr rfl
  intro j _hj
  rw [originalChannelTerm_eq_completionWeight_mul_centeredMoment,
    originalChannelTerm_eq_completionWeight_mul_centeredMoment,
    norm_mul, norm_mul]
  ring

/-- The diagonal finite-window mass after separating fixed completion
weights from finite eta moments. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  4 * ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedMomentSelfMass
        cutoff rho ^ 2

/-- The signed distinct-zero finite-window mass after separating fixed
completion weights from finite eta-moment correlations. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (2 *
          pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionCorrelation
            cutoff sigma rho) ^ 2).re

/-- The reflected-original diagonal mass equals its completion-weighted
finite-moment form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass_eq_weightedMomentMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass
  apply congrArg (4 * ·)
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [reflectedOriginalSelfMass_eq_weightedMomentSelfMass]

/-- The reflection-coupled signed distinct-zero mass equals its
completion-weighted finite-moment form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass_eq_weightedMomentMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
        cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass
        cutoff T := by
  unfold
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [← sameChannelCorrelation_eq_reflectedOriginal_add_star_original,
    sameChannelCorrelation_eq_weightedReflectionCorrelation]

/-- The coherent finite eta Frobenius mass with fixed spectral weights
separated from the finite arithmetic moment correlations. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_weightedMomentDiagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_reflectedOriginalDiagonal_add_offDiagonal,
    pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass_eq_weightedMomentMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass_eq_weightedMomentMass]

/-- The multiplicity-aware eta ledger with fixed spectral completion weights
separated from the finite cutoff-centered arithmetic moment correlations. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_weightedMoment_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedMomentMass cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedMomentMass cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h :=
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_reflectionCorrelation_ledger
      cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass_eq_weightedMomentMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass_eq_weightedMomentMass]
    at h
  exact h

end

end RiemannGaussian
