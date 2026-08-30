import RiemannGaussian.EtaEnergyFiniteWindowPairCorrelation

/-!
# Diagonal and off-diagonal eta zero-pair masses

This module separates the exact finite eta pair correlation into its positive
diagonal self-mass and its signed off-diagonal interference mass.  The latter
retains the real part of the square of each complex Hermitian correlation;
no triangle inequality or absolute-square replacement is used.

The resulting rank--trace ledger names the off-diagonal cancellation term
directly.  Its required arithmetic estimate remains open.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

private def realWeightedSymmetricPairTerm
    {n α : Type*} [Fintype n] (w : α → ℝ) (v : α → n → ℂ)
    (a b : α) : ℝ :=
  (((w a * w b : ℝ) : ℂ) * (star (v b) ⬝ᵥ v a) ^ 2).re

private theorem realWeightedSymmetricPairTerm_self
    {n α : Type*} [Fintype n] (w : α → ℝ) (v : α → n → ℂ)
    (a : α) :
    realWeightedSymmetricPairTerm w v a a =
      w a ^ 2 * (∑ j, ‖v a j‖ ^ 2) ^ 2 := by
  have hdot :
      star (v a) ⬝ᵥ v a = ((∑ j, ‖v a j‖ ^ 2 : ℝ) : ℂ) := by
    unfold dotProduct
    push_cast
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Pi.star_apply, RCLike.star_def]
    rw [RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal]
  unfold realWeightedSymmetricPairTerm
  rw [hdot]
  norm_cast
  ring

private theorem sum_realWeightedSymmetricPairTerm_eq_diagonal_add_offDiagonal
    {n α : Type*} [Fintype n] [DecidableEq α] (s : Finset α)
    (w : α → ℝ) (v : α → n → ℂ) :
    (∑ a ∈ s, ∑ b ∈ s, realWeightedSymmetricPairTerm w v a b) =
      (∑ a ∈ s, w a ^ 2 * (∑ j, ‖v a j‖ ^ 2) ^ 2) +
        ∑ a ∈ s, ∑ b ∈ s.erase a,
          realWeightedSymmetricPairTerm w v a b := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← realWeightedSymmetricPairTerm_self w v a]
  exact (Finset.add_sum_erase s (realWeightedSymmetricPairTerm w v a) ha).symm

/-- The positive diagonal self-correlation mass in a finite eta zero
window. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      (∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j‖ ^ 2) ^ 2

/-- The signed off-diagonal interference mass over distinct ordered pairs in
a finite eta zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff sigma) ⬝ᵥ
          pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) ^ 2).re

/-- The exact eta zero-pair mass is its positive diagonal mass plus its
phase-preserving signed off-diagonal mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass_eq_diagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
          cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
  simpa only [realWeightedSymmetricPairTerm] using
    sum_realWeightedSymmetricPairTerm_eq_diagonal_add_offDiagonal
      (spectralZetaZeroWindow T)
      (fun rho ↦ (analyticZetaZeroMultiplicity rho : ℝ))
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff)

/-- The diagonal eta zero-pair mass is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass
      cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass
  positivity

/-- Frobenius positivity gives the unconditional lower floor on the signed
off-diagonal interference mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass_lowerBound
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    -pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff T ≤
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
        cutoff T := by
  have hmass :
      0 ≤ pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass cutoff T := by
    rw [← pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_pairCorrelationMass]
    exact HermitianInertia.frobSq_nonneg _
  rw [
    pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass_eq_diagonal_add_offDiagonal]
    at hmass
  linarith

/-- The named coherent Frobenius mass is exactly the diagonal self-mass plus
the signed off-diagonal interference mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_diagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_pairCorrelationMass,
    pairedEtaTopPrefixFiniteZeroWindowPairCorrelationMass_eq_diagonal_add_offDiagonal]

/-- The multiplicity-aware `c = 2` eta ledger with its coherent mass split
into the explicit diagonal and signed off-diagonal zero-pair terms. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_pairCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h := pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_ledger
    cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_diagonal_add_offDiagonal]
    at h
  linarith

end

end RiemannGaussian
