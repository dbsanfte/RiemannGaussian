import RiemannGaussian.Hybrid.EtaGeometricNormalizedSignedPullback
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Reflection content of the normalized geometric eta pullback

The two-sided normalization from the preceding module produces a Hermitian
contraction on the finite zero-index space.  This module determines that
matrix exactly.

Reflection across the critical line permutes every nonnegative symmetric
spectral window.  After transporting this involution through the fixed finite
enumeration, let `P` be its permutation matrix.  The actual
multiplicity-weighted synthesis matrix `C` satisfies

`P Cᴴ = Cᵀ`.

The complex-symmetric eta block is also exactly `C Cᵀ`.  Hence its zero-space
pullback is

`B = Cᴴ (C Cᵀ) C = K P K`, where `K = Cᴴ C`.

At every separated block, cancellation by the checked inverse of `K` proves

`K⁻¹ B K⁻¹ = P`.

Thus complete two-sided whitening retains the reflection labels but cancels
all eta amplitudes.  Its trace is the number of fixed points of the reflected
zero permutation.  This is a rigorous information-flow diagnostic: an
arithmetic improvement cannot come from the fully whitened matrix alone and
must retain its coupling to `K` or another uncollapsed eta observable.
-/

open Complex Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Critical-line reflection restricted to a nonnegative finite symmetric
spectral window. -/
def spectralZetaZeroWindowConjugatePartnerEquiv
    (T : ℝ) (hT : 0 ≤ T) :
    ↥(spectralZetaZeroWindow T) ≃ ↥(spectralZetaZeroWindow T) :=
  NontrivialZetaZero.conjugatePartnerEquiv.subtypeEquiv fun rho ↦
    (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).symm

@[simp]
theorem spectralZetaZeroWindowConjugatePartnerEquiv_apply
    (T : ℝ) (hT : 0 ≤ T) (rho : ↥(spectralZetaZeroWindow T)) :
    (spectralZetaZeroWindowConjugatePartnerEquiv T hT rho :
      NontrivialZetaZero) =
      NontrivialZetaZero.conjugatePartner rho :=
  rfl

/-- Reflection transported to the fixed `Fin` enumeration of one finite
spectral window. -/
def pairedEtaZeroWindowConjugatePartnerPerm
    (T : ℝ) (hT : 0 ≤ T) :
    Equiv.Perm (Fin (spectralZetaZeroWindow T).card) :=
  ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm.trans
      (spectralZetaZeroWindowConjugatePartnerEquiv T hT)).trans
    (etaZeroWindowEquivFin (spectralZetaZeroWindow T))

/-- Decoding the reflected finite index gives the reflected zeta zero. -/
@[simp]
theorem etaZeroWindowEquivFin_symm_pairedEtaZeroWindowConjugatePartnerPerm
    (T : ℝ) (hT : 0 ≤ T)
    (i : Fin (spectralZetaZeroWindow T).card) :
    ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm
      (pairedEtaZeroWindowConjugatePartnerPerm T hT i) :
        NontrivialZetaZero) =
      NontrivialZetaZero.conjugatePartner
        ((etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm i) := by
  simp [pairedEtaZeroWindowConjugatePartnerPerm]

/-- The transported reflection permutation is an involution. -/
@[simp]
theorem pairedEtaZeroWindowConjugatePartnerPerm_apply_apply
    (T : ℝ) (hT : 0 ≤ T)
    (i : Fin (spectralZetaZeroWindow T).card) :
    pairedEtaZeroWindowConjugatePartnerPerm T hT
        (pairedEtaZeroWindowConjugatePartnerPerm T hT i) = i := by
  apply (etaZeroWindowEquivFin (spectralZetaZeroWindow T)).symm.injective
  apply Subtype.ext
  simp only [etaZeroWindowEquivFin_symm_pairedEtaZeroWindowConjugatePartnerPerm,
    NontrivialZetaZero.conjugatePartner_conjugatePartner]

/-- The permutation matrix of critical-line reflection on the enumerated
finite zero window. -/
def pairedEtaZeroWindowConjugatePartnerMatrix
    (T : ℝ) (hT : 0 ≤ T) :
    Matrix (Fin (spectralZetaZeroWindow T).card)
      (Fin (spectralZetaZeroWindow T).card) ℂ :=
  (pairedEtaZeroWindowConjugatePartnerPerm T hT).permMatrix ℂ

/-- The reflection permutation matrix squares to the identity. -/
theorem pairedEtaZeroWindowConjugatePartnerMatrix_mul_self
    (T : ℝ) (hT : 0 ≤ T) :
    pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        pairedEtaZeroWindowConjugatePartnerMatrix T hT = 1 := by
  rw [pairedEtaZeroWindowConjugatePartnerMatrix,
    ← Matrix.permMatrix_mul]
  have hperm :
      pairedEtaZeroWindowConjugatePartnerPerm T hT *
          pairedEtaZeroWindowConjugatePartnerPerm T hT = 1 := by
    ext i
    simp [Equiv.Perm.mul_apply]
  rw [hperm, Matrix.permMatrix_one]

/-- The positive square-root multiplicity is invariant under critical-line
reflection. -/
theorem pairedEtaGeometricMultiplicitySqrtWeight_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaGeometricMultiplicitySqrtWeight
        (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaGeometricMultiplicitySqrtWeight rho := by
  unfold pairedEtaGeometricMultiplicitySqrtWeight
  rw [analyticZetaZeroMultiplicity_conjugatePartner]

/-- Reflection of the zero index conjugates every entry of the actual
multiplicity-weighted synthesis matrix. -/
theorem pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_partnerPerm
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (a : Fin (spectralZetaZeroWindow T).card × Fin 2)
    (i : Fin (spectralZetaZeroWindow T).card) :
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n a
        (pairedEtaZeroWindowConjugatePartnerPerm T hT i) =
      star (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n a i) := by
  simp only [pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix,
    Matrix.transpose_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix,
    pairedEtaGeometricPackedHyperbolicFeature]
  rw [etaZeroWindowEquivFin_symm_pairedEtaZeroWindowConjugatePartnerPerm,
    pairedEtaGeometricMultiplicitySqrtWeight_conjugatePartner,
    topPrefixFiniteCutoffFamilyFeature_conjugatePartner]
  simp [pairedEtaGeometricMultiplicitySqrtWeight]

/-- The reflection permutation converts the synthesis conjugate transpose
into its ordinary transpose. -/
theorem pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaZeroWindowConjugatePartnerMatrix T hT *
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᴴ =
      (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n)ᵀ := by
  ext i a
  change
    (((pairedEtaZeroWindowConjugatePartnerPerm T hT).permMatrix ℂ).mulVec
      (fun j ↦ star
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n a j))) i =
      pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
        (spectralZetaZeroWindow T) n a i
  rw [Matrix.permMatrix_mulVec]
  simp only [Function.comp_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_partnerPerm,
    star_star]

/-- Multiplying the synthesis matrix by its ordinary transpose is the sum of
the literal multiplicity-weighted complex-symmetric feature blocks. -/
theorem pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_sum
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q s n *
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
          q s n)ᵀ =
      ∑ i : Fin s.card,
        (analyticZetaZeroMultiplicity
            ((etaZeroWindowEquivFin s).symm i) : ℂ) •
          Matrix.vecMulVec
            (pairedEtaGeometricPackedHyperbolicFeature q s n i)
            (pairedEtaGeometricPackedHyperbolicFeature q s n i) := by
  classical
  ext a b
  simp only [Matrix.mul_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix,
    Matrix.transpose_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← pairedEtaGeometricMultiplicitySqrtWeight_sq]
  ring

/-- On a genuine finite spectral window, `C Cᵀ` is exactly the existing
complex-symmetric signed eta block. -/
theorem pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock
    (q : ℕ) (T : ℝ) (n : ℕ) :
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n *
        (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q
          (spectralZetaZeroWindow T) n)ᵀ =
      pairedEtaTopPrefixFiniteZeroWindowBlock
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  rw [pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_sum]
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
  let s := spectralZetaZeroWindow T
  let f : NontrivialZetaZero →
      Matrix (Fin s.card × Fin 2) (Fin s.card × Fin 2) ℂ := fun rho ↦
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature
          (fun j : Fin s.card ↦ pairedEtaGeometricHyperbolicCutoff q n j) rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature
          (fun j : Fin s.card ↦ pairedEtaGeometricHyperbolicCutoff q n j) rho)
  change (∑ i : Fin s.card, f ((etaZeroWindowEquivFin s).symm i)) =
    ∑ rho ∈ s, f rho
  calc
    _ = ∑ rho : s, f rho :=
      Fintype.sum_equiv (etaZeroWindowEquivFin s).symm _ _ (fun _ ↦ rfl)
    _ = _ := (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm

/-- Exact factorization of the signed zero-space pullback through the
reflection permutation: `B = K P K`. -/
theorem pairedEtaGeometricSignedZeroPullback_eq_zeroGram_mul_partnerMatrix_mul_zeroGram
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    pairedEtaGeometricSignedZeroPullback q T n =
      pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n *
        pairedEtaZeroWindowConjugatePartnerMatrix T hT *
      pairedEtaGeometricMultiplicityWeightedZeroGram q
          (spectralZetaZeroWindow T) n := by
  rw [pairedEtaGeometricSignedZeroPullback,
    ← pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mul_transpose_eq_zeroWindowBlock
      q T n,
    ← pairedEtaZeroWindowConjugatePartnerMatrix_mul_synthesis_conjTranspose_eq_transpose
      q hT n]
  simp only [pairedEtaGeometricMultiplicityWeightedZeroGram,
    Matrix.mul_assoc]

/-- Wherever the actual eta features are separated, complete two-sided
normalization is exactly the reflected-zero permutation matrix. -/
theorem pairedEtaGeometricNormalizedSignedZeroPullback_eq_partnerMatrix
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricNormalizedSignedZeroPullback q T n =
      pairedEtaZeroWindowConjugatePartnerMatrix T hT := by
  rw [pairedEtaGeometricNormalizedSignedZeroPullback,
    pairedEtaGeometricSignedZeroPullback_eq_zeroGram_mul_partnerMatrix_mul_zeroGram
      q hT n]
  let K := pairedEtaGeometricMultiplicityWeightedZeroGram q
    (spectralZetaZeroWindow T) n
  let P := pairedEtaZeroWindowConjugatePartnerMatrix T hT
  change K⁻¹ * (K * P * K) * K⁻¹ = P
  have hK' : K.PosDef := by simpa [K] using hK
  let _ := hK'.isUnit.invertible
  calc
    K⁻¹ * (K * P * K) * K⁻¹ =
        (K⁻¹ * K) * P * (K * K⁻¹) := by noncomm_ring
    _ = P := by
      rw [Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible]
      simp

/-- The fully normalized matrix is consequently an involution. -/
theorem pairedEtaGeometricNormalizedSignedZeroPullback_mul_self
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricNormalizedSignedZeroPullback q T n *
        pairedEtaGeometricNormalizedSignedZeroPullback q T n = 1 := by
  rw [pairedEtaGeometricNormalizedSignedZeroPullback_eq_partnerMatrix q hT n hK,
    pairedEtaZeroWindowConjugatePartnerMatrix_mul_self]

/-- The trace of the fully normalized eta matrix counts exactly the fixed
indices of critical-line reflection. -/
theorem trace_pairedEtaGeometricNormalizedSignedZeroPullback_eq_fixedPoints_ncard
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricNormalizedSignedZeroPullback q T n).trace =
      ((Function.fixedPoints
        (pairedEtaZeroWindowConjugatePartnerPerm T hT)).ncard : ℂ) := by
  rw [pairedEtaGeometricNormalizedSignedZeroPullback_eq_partnerMatrix q hT n hK,
    pairedEtaZeroWindowConjugatePartnerMatrix,
    Matrix.trace_permutation]

/-- For every nonnegative finite spectral window, one odd prime makes the
fully normalized eta matrix equal the reflection permutation, square to the
identity, and have the corresponding fixed-point trace at every sufficiently
late block. -/
theorem exists_prime_eventually_normalizedSignedZeroPullback_eq_reflection
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        pairedEtaGeometricNormalizedSignedZeroPullback q T n =
            pairedEtaZeroWindowConjugatePartnerMatrix T hT ∧
          pairedEtaGeometricNormalizedSignedZeroPullback q T n *
              pairedEtaGeometricNormalizedSignedZeroPullback q T n = 1 ∧
          (pairedEtaGeometricNormalizedSignedZeroPullback q T n).trace =
            ((Function.fixedPoints
              (pairedEtaZeroWindowConjugatePartnerPerm T hT)).ncard : ℂ) := by
  obtain ⟨q, hqPrime, hqOdd, hq, hK⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hK] with n hn
  exact
    ⟨pairedEtaGeometricNormalizedSignedZeroPullback_eq_partnerMatrix q hT n hn.1,
      pairedEtaGeometricNormalizedSignedZeroPullback_mul_self q hT n hn.1,
      trace_pairedEtaGeometricNormalizedSignedZeroPullback_eq_fixedPoints_ncard
        q hT n hn.1⟩

end

end RiemannGaussian
