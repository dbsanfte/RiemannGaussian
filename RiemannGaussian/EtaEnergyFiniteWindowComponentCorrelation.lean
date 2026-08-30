import RiemannGaussian.EtaEnergyFiniteWindowPairCorrelationSplit

/-!
# Component expansion of finite eta zero-pair correlations

The packed eta feature has an even coordinate `P + Q` and an `I`-twisted odd
coordinate `I * (P - Q)`.  This module proves that their Hermitian
correlation cancels every mixed `P`--`Q` term exactly.  What remains is twice
the cutoff-family sum of the two same-channel correlations.

The result is propagated through the diagonal mass, signed off-diagonal
mass, coherent Frobenius mass, and multiplicity-aware rank--trace ledger.  It
is an exact eta-arithmetic expansion, not an estimate.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The cutoff-family sum of the partner--partner and aligned
conjugate--conjugate completed eta-prefix correlations. -/
def pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  ∑ j, (starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          sigma (cutoff j)) *
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        rho (cutoff j) +
    starRingEnd ℂ
        (pairedEtaTopPrefixFiniteAlignedConjugateTerm sigma (cutoff j)) *
      pairedEtaTopPrefixFiniteAlignedConjugateTerm rho (cutoff j))

/-- The packed-feature correlation is twice its same-channel completed-prefix
correlation.  The two mixed channels cancel exactly. -/
theorem star_cutoffFamilyFeature_dot_cutoffFamilyFeature_eq_two_mul_sameChannelCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff sigma) ⬝ᵥ
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho =
      2 * pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
        cutoff sigma rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyFeature
    pairedEtaTopPrefixFiniteHyperbolicFeature
    pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
    pairedEtaTopPrefixFiniteEvenCoordinate
    pairedEtaTopPrefixFiniteOddCoordinate dotProduct
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Pi.star_apply, RCLike.star_def, Fin.sum_univ_two, cons_val_zero,
    cons_val_one, map_add, map_mul, map_sub, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The sum of the squared norms in the two completed eta-prefix channels
for one zero. -/
def pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) : ℝ :=
  ∑ j, (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho (cutoff j)‖ ^ 2 +
    ‖pairedEtaTopPrefixFiniteAlignedConjugateTerm rho (cutoff j)‖ ^ 2)

/-- The squared-norm sum of the packed hyperbolic feature is twice the
same-channel self-mass. -/
theorem sum_norm_sq_cutoffFamilyFeature_eq_two_mul_sameChannelSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) :
    (∑ x, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho x‖ ^ 2) =
      2 * pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
        cutoff rho := by
  have h :=
    star_cutoffFamilyFeature_dot_cutoffFamilyFeature_eq_two_mul_sameChannelCorrelation
      cutoff rho rho
  have hleft :
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) ⬝ᵥ
          pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho =
        (((∑ x,
          ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho x‖ ^ 2 : ℝ) : ℂ)) := by
    unfold dotProduct
    push_cast
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [Pi.star_apply, RCLike.star_def]
    rw [RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal]
  have hright :
      pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
          cutoff rho rho =
        ((pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
          cutoff rho : ℝ) : ℂ) := by
    unfold pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
      pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
    push_cast
    apply Finset.sum_congr rfl
    intro j _hj
    rw [RCLike.conj_mul, RCLike.conj_mul]
    norm_cast
  rw [hleft, hright] at h
  norm_cast at h

/-- The diagonal eta mass written entirely in terms of the two completed
same-channel prefix families. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  4 * ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      pairedEtaTopPrefixFiniteCutoffFamilySameChannelSelfMass
        cutoff rho ^ 2

/-- The signed distinct-zero eta mass written entirely in terms of the two
completed same-channel prefix families. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (2 * pairedEtaTopPrefixFiniteCutoffFamilySameChannelCorrelation
          cutoff sigma rho) ^ 2).re

/-- The abstract diagonal packed-feature mass equals the literal
same-channel completed-prefix mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass_eq_sameChannelMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [sum_norm_sq_cutoffFamilyFeature_eq_two_mul_sameChannelSelfMass]
  ring

/-- The abstract signed off-diagonal packed-feature mass equals the literal
same-channel completed-prefix correlation mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass_eq_sameChannelMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [
    star_cutoffFamilyFeature_dot_cutoffFamilyFeature_eq_two_mul_sameChannelCorrelation]

/-- The coherent finite-window Frobenius mass is the literal same-channel
diagonal mass plus the signed same-channel distinct-zero interference. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_sameChannelDiagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_diagonal_add_offDiagonal,
    pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass_eq_sameChannelMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass_eq_sameChannelMass]

/-- The multiplicity-aware eta ledger in literal same-channel completed eta
prefix variables. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_sameChannel_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalSameChannelMass cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalSameChannelMass cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h :=
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_pairCorrelation_ledger
      cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowDiagonalPairCorrelationMass_eq_sameChannelMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalPairCorrelationMass_eq_sameChannelMass]
    at h
  exact h

end

end RiemannGaussian
