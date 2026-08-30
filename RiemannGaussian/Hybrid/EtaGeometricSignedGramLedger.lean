import RiemannGaussian.Hybrid.EtaGeometricPackedFeatureGram
import RiemannGaussian.EtaEnergyFiniteWindowBlock

/-!
# Joint signed and positive Gram ledger for geometric eta features

The finite eta certificate uses a complex-symmetric, sign-bearing sum of
`v vᵀ` blocks.  The preceding module constructs instead the positive
Hermitian sum of `v v*` blocks and proves that its geometric specialization
has full represented rank.  This module relates those two matrices without
identifying them.

On a symmetric spectral zero window, critical-line features are real under
the checked reflection law.  Every off-line reflected pair contributes its
real coordinate block plus its imaginary coordinate block to the Hermitian
Gram, while it contributes the real block minus the imaginary block to the
complex-symmetric certificate matrix.  Lean therefore proves the exact joint
ledger

`Gram = onLine + offReal + offImag`,

`Signed = onLine + offReal - offImag`.

Consequently both `Gram - Signed` and `Gram + Signed` are positive
semidefinite, with their separate colour content still explicit.  At the
geometric cutoffs the Gram simultaneously has rank equal to the number of
represented distinct zeros.  This is a normalized-carrier interface; it does
not yet supply the arithmetic trace or spectral estimate needed for a zero
proportion.
-/

open Complex Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Multiplicity-weighted Hermitian Gram over the genuine symmetric spectral
zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowHermitianGram
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
        (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))

/-- A reflected eta pair contributes the sum, rather than the difference,
of its positive real and imaginary coordinate blocks to the Hermitian Gram. -/
theorem topPrefixFiniteCutoffFamilyFeature_weightedPairHermitianGram_eq_real_add_imag
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
            (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        (analyticZetaZeroMultiplicity
            (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
              (NontrivialZetaZero.conjugatePartner rho))
            (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
              (NontrivialZetaZero.conjugatePartner rho))) =
      (analyticZetaZeroMultiplicity rho : ℂ) •
          ((2 : ℂ) • Matrix.vecMulVec
            (complexVectorReal
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
            (complexVectorReal
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) +
        (analyticZetaZeroMultiplicity rho : ℂ) •
          ((2 : ℂ) • Matrix.vecMulVec
            (complexVectorImag
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
            (complexVectorImag
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) := by
  rw [analyticZetaZeroMultiplicity_conjugatePartner,
    topPrefixFiniteCutoffFamilyFeature_conjugatePartner,
    star_star, ← smul_add]
  change (analyticZetaZeroMultiplicity rho : ℂ) •
      complexHermitianConjugatePairGram
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) = _
  rw [complexHermitianConjugatePairGram_eq_real_add_imag, smul_add]

/-- On the critical line, the Hermitian rank-one eta block is exactly the
complex-symmetric rank-one block because reflection fixes the feature. -/
theorem topPrefixFiniteCutoffFamilyFeature_weightedHermitianBlock_eq_symmetric_of_mem_critical
    {d : Type*} (cutoff : d → ℕ) {T : ℝ}
    {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralCriticalZetaZeroWindow T) :
    (analyticZetaZeroMultiplicity rho : ℂ) •
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
          (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) =
      (analyticZetaZeroMultiplicity rho : ℂ) •
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) := by
  have hre : rho.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1
      (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho :=
    conjugatePartner_eq_self_of_re_eq_half rho hre
  have hstar :
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) =
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho := by
    rw [← topPrefixFiniteCutoffFamilyFeature_conjugatePartner, hpartner]
  rw [hstar]

/-- Exact positive-channel decomposition of the Hermitian eta Gram on a
symmetric nonnegative spectral window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianGram_eq_onLine_add_offLineReal_add_imag
    {d : Type*} (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T +
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T +
          pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowHermitianGram
  rw [sum_spectralZetaZeroWindow_eq_upper_add_critical_add_lower,
    sum_spectralLowerZetaZeroWindow_eq_upper_conjugatePartner hT]
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
  calc
    (∑ rho ∈ spectralUpperZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) +
          (∑ rho ∈ spectralCriticalZetaZeroWindow T,
            (analyticZetaZeroMultiplicity rho : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
                (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          (analyticZetaZeroMultiplicity
              (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho))
              (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho))) =
      (∑ rho ∈ spectralCriticalZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          ((analyticZetaZeroMultiplicity rho : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
                (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
            (analyticZetaZeroMultiplicity
                (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                  (NontrivialZetaZero.conjugatePartner rho))
                (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                  (NontrivialZetaZero.conjugatePartner rho)))) := by
      rw [Finset.sum_add_distrib]
      abel
    _ = (∑ rho ∈ spectralCriticalZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          ((analyticZetaZeroMultiplicity rho : ℂ) •
              ((2 : ℂ) • Matrix.vecMulVec
                (complexVectorReal
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
                (complexVectorReal
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) +
            (analyticZetaZeroMultiplicity rho : ℂ) •
              ((2 : ℂ) • Matrix.vecMulVec
                (complexVectorImag
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
                (complexVectorImag
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))) := by
      apply congrArg₂ (fun A B ↦ A + B)
      · apply Finset.sum_congr rfl
        intro rho hrho
        exact
          topPrefixFiniteCutoffFamilyFeature_weightedHermitianBlock_eq_symmetric_of_mem_critical
            cutoff hrho
      · apply Finset.sum_congr rfl
        intro rho _hrho
        exact
          topPrefixFiniteCutoffFamilyFeature_weightedPairHermitianGram_eq_real_add_imag
            cutoff rho
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Exact colour ledger: subtracting the signed eta block from the Hermitian
Gram leaves twice the positive imaginary off-line block. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_eq_two_imag
    {d : Type*} (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T -
        pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T =
      (2 : ℂ) •
        pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T := by
  rw [pairedEtaTopPrefixFiniteZeroWindowHermitianGram_eq_onLine_add_offLineReal_add_imag
      cutoff hT,
    pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT,
    two_smul ℂ]
  abel

/-- Exact colour ledger: adding the signed eta block to the Hermitian Gram
leaves twice the positive on-line-plus-real block. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_eq_two_onLine_add_real
    {d : Type*} (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T =
      (2 : ℂ) •
        (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T +
          pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T) := by
  rw [pairedEtaTopPrefixFiniteZeroWindowHermitianGram_eq_onLine_add_offLineReal_add_imag
      cutoff hT,
    pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT,
    two_smul ℂ]
  abel

/-- The signed eta block is dominated from above by its positive Hermitian
companion, expressed without collapsing either colour channel. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).PosSemidef := by
  rw [pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_eq_two_imag
    cutoff hT]
  exact (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef
    cutoff T).smul (Complex.zero_le_real.mpr (by norm_num))

/-- The negative signed eta block is likewise dominated by the same positive
Hermitian companion. -/
theorem pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T +
      pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).PosSemidef := by
  rw [pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_eq_two_onLine_add_real
    cutoff hT]
  exact ((pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T).add
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
      cutoff T)).smul (Complex.zero_le_real.mpr (by norm_num))

/-- For a genuine spectral window, the enumerated geometric coordinate Gram
is exactly the window's multiplicity-weighted Hermitian Gram. -/
theorem pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram
    (q : ℕ) (T : ℝ) (n : ℕ) :
    pairedEtaGeometricMultiplicityWeightedCoordinateGram q
        (spectralZetaZeroWindow T) n =
      pairedEtaTopPrefixFiniteZeroWindowHermitianGram
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  rw [pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_sum]
  unfold pairedEtaTopPrefixFiniteZeroWindowHermitianGram
  let s := spectralZetaZeroWindow T
  let f : NontrivialZetaZero →
      Matrix (Fin s.card × Fin 2) (Fin s.card × Fin 2) ℂ := fun rho ↦
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature
          (fun j : Fin s.card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) rho)
        (star (pairedEtaTopPrefixFiniteCutoffFamilyFeature
          (fun j : Fin s.card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) rho))
  change (∑ i : Fin s.card, f ((etaZeroWindowEquivFin s).symm i)) =
    ∑ rho ∈ s, f rho
  calc
    _ = ∑ rho : s, f rho :=
      Fintype.sum_equiv (etaZeroWindowEquivFin s).symm _ _ (fun _ ↦ rfl)
    _ = _ := (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm

/-- The geometric positive Gram is eventually full-rank when specialized to
the genuine symmetric spectral window. -/
theorem exists_prime_eventually_posSemidef_and_rank_zeroWindowHermitianGram_eq_card
    (T : ℝ) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (pairedEtaTopPrefixFiniteZeroWindowHermitianGram
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T).PosSemidef ∧
        (pairedEtaTopPrefixFiniteZeroWindowHermitianGram
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T).rank =
          (spectralZetaZeroWindow T).card := by
  obtain ⟨q, hqPrime, hqOdd, hq, hgram⟩ :=
    exists_prime_eventually_posSemidef_and_rank_pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_card
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hgram] with n hn
  rw [← pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_zeroWindowHermitianGram]
  exact hn

/-- Complete joint carrier theorem.  At one odd prime base and every
sufficiently late geometric block, the genuine zero-window Hermitian Gram is
positive with full represented rank, and both of its signed-block difference
channels are positive semidefinite. -/
theorem exists_prime_eventually_fullRank_zeroWindowHermitianGram_and_signed_dominance
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        let cutoff : Fin (spectralZetaZeroWindow T).card → ℕ :=
          fun j ↦ pairedEtaGeometricHyperbolicCutoff q n j
        (pairedEtaTopPrefixFiniteZeroWindowHermitianGram
            cutoff T).PosSemidef ∧
          (pairedEtaTopPrefixFiniteZeroWindowHermitianGram
            cutoff T).rank = (spectralZetaZeroWindow T).card ∧
          (pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T -
            pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).PosSemidef ∧
          (pairedEtaTopPrefixFiniteZeroWindowHermitianGram cutoff T +
            pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).PosSemidef := by
  obtain ⟨q, hqPrime, hqOdd, hq, hgram⟩ :=
    exists_prime_eventually_posSemidef_and_rank_zeroWindowHermitianGram_eq_card T
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hgram] with n hn
  dsimp only
  exact ⟨hn.1, hn.2,
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram_sub_signedBlock_posSemidef
      _ hT,
    pairedEtaTopPrefixFiniteZeroWindowHermitianGram_add_signedBlock_posSemidef
      _ hT⟩

end

end RiemannGaussian
