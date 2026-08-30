import RiemannGaussian.EtaEnergyFiniteWindowComponentCorrelation

/-!
# Reflection compression of finite eta component correlations

The two same-channel terms from the component expansion are themselves
reflection copies of one completed finite eta-prefix channel.  This module
names that original channel and proves that the live feature correlation is

`H(sigma#, rho#) + star (H(sigma, rho))`,

where `H` is one ordinary finite Hermitian Gram correlation and `#` is the
critical-line reflection of a genuine zeta zero.  The formula is propagated
through the finite masses and multiplicity-aware ledger without estimating
the remaining reflection-coupled sum.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The original completed finite eta-prefix channel at one zero and one
cutoff. -/
def pairedEtaTopPrefixFiniteOriginalChannelTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaXiCompletionFactor rho.1 * rho.1 *
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
      (analyticZetaZeroMultiplicity rho - 1) rho.1 (N + 1)

/-- The completed partner term is the original channel evaluated at the
reflected zero. -/
theorem topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        rho N =
      pairedEtaTopPrefixFiniteOriginalChannelTerm
        (NontrivialZetaZero.conjugatePartner rho) N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
    pairedEtaTopPrefixFiniteOriginalChannelTerm
  rw [analyticZetaZeroMultiplicity_conjugatePartner]

/-- The aligned conjugate term is exactly the conjugate of the original
channel at the same zero. -/
theorem topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N =
      starRingEnd ℂ (pairedEtaTopPrefixFiniteOriginalChannelTerm rho N) := by
  unfold pairedEtaTopPrefixFiniteAlignedConjugateTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    pairedEtaTopPrefixFiniteOriginalChannelTerm
  rw [show (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho =
      pairedEtaTopPrefixFiniteParity rho by rfl,
    ← mul_assoc, pairedEtaTopPrefixFiniteParity_mul_self, one_mul]

/-- The ordinary Hermitian Gram correlation of the original completed
finite-prefix channel over the selected cutoff family. -/
def pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  ∑ j,
    starRingEnd ℂ
        (pairedEtaTopPrefixFiniteOriginalChannelTerm sigma (cutoff j)) *
      pairedEtaTopPrefixFiniteOriginalChannelTerm rho (cutoff j)

/-- The original-channel Gram correlation obeys Hermitian conjugate
symmetry. -/
theorem originalChannelCorrelation_swap
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
        cutoff rho sigma =
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
          cutoff sigma rho) := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

/-- The two surviving component channels compress to one original-channel
Gram correlation at the reflected pair plus the conjugate correlation at the
original pair. -/
theorem sameChannelCorrelation_eq_reflectedOriginal_add_star_original
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
        cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation cutoff
          (NontrivialZetaZero.conjugatePartner sigma)
          (NontrivialZetaZero.conjugatePartner rho) +
        starRingEnd ℂ
          (pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
            cutoff sigma rho) := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
    topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
    topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm,
    topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm]
  simp only [map_mul, starRingEnd_apply, star_star, mul_comm]

/-- The original channel's combined self-mass at a zero and its reflected
partner. -/
def pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) : ℝ :=
  ∑ j,
    (‖pairedEtaTopPrefixFiniteOriginalChannelTerm
        (NontrivialZetaZero.conjugatePartner rho) (cutoff j)‖ ^ 2 +
      ‖pairedEtaTopPrefixFiniteOriginalChannelTerm rho (cutoff j)‖ ^ 2)

/-- The two-component same-channel self-mass is the original channel's mass
at the zero and its reflected partner. -/
theorem sameChannelSelfMass_eq_reflectedOriginalSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
        cutoff rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
    pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
  apply Finset.sum_congr rfl
  intro j _hj
  rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
    topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm,
    starRingEnd_apply, norm_star]

/-- The finite diagonal mass expressed through the single original channel
at each zero and its reflected partner. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  4 * ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      pairedEtaTopPrefixFiniteCutoffFamilyReflectedOriginalSelfMass
        cutoff rho ^ 2

/-- The signed distinct-zero mass expressed through one original-channel
Gram kernel coupled to its reflected copy. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (2 *
          (pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
              cutoff (NontrivialZetaZero.conjugatePartner sigma)
                (NontrivialZetaZero.conjugatePartner rho) +
            starRingEnd ℂ
              (pairedEtaTopPrefixFiniteCutoffFamilyOriginalChannelCorrelation
                cutoff sigma rho))) ^ 2).re

/-- The same-channel diagonal mass equals its one-channel reflection
compression. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass_eq_reflectedOriginalMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass
  apply congrArg (4 * ·)
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [sameChannelSelfMass_eq_reflectedOriginalSelfMass]

/-- The same-channel signed distinct-zero mass equals its one-channel
reflection-coupled compression. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass_eq_reflectionCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [sameChannelCorrelation_eq_reflectedOriginal_add_star_original]

/-- The coherent finite eta Frobenius mass in one original completed-prefix
channel and its critical-line reflection. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_reflectedOriginalDiagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_sameChannelDiagonal_add_offDiagonal,
    pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass_eq_reflectedOriginalMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass_eq_reflectionCorrelationMass]

/-- The multiplicity-aware eta ledger compressed to one original completed
finite-prefix Gram channel and its reflected copy. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_reflectionCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalReflectedOriginalMass cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalReflectionCorrelationMass
        cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h :=
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_sameChannel_ledger
      cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass_eq_reflectedOriginalMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass_eq_reflectionCorrelationMass]
    at h
  exact h

end

end RiemannGaussian
