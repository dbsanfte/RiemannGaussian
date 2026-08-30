import RiemannGaussian.Hybrid.EtaGeometricSignedGramLedger

/-!
# Positive-definite zero-index Gram for geometric eta features

The coordinate Hermitian Gram lives on the packed cutoff/colour space and has
rank equal to the number of represented zeros, but it is necessarily singular
when that coordinate space is larger.  For normalization we instead pull the
same multiplicity-weighted synthesis matrix back to the zero-index space.

The resulting square matrix is `K = Cᴴ C`.  Linear independence of the actual
packed eta features makes the synthesis map injective, so Mathlib's checked
Gram criterion proves `K` positive definite.  Its inverse is therefore also
positive definite.  For every finite zeta-zero window, one odd prime base
makes both facts hold at all sufficiently late geometric blocks.

This supplies a rigorous invertible metric for the next whitening step.  It
does not yet define the whitened signed operator or prove an arithmetic
certificate estimate.
-/

open Complex Filter
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- Square zero-index Gram of the multiplicity-weighted packed eta synthesis
matrix. -/
def pairedEtaGeometricMultiplicityWeightedZeroGram
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card) ℂ :=
  (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q s n)ᴴ *
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q s n

/-- The zero-index Gram is positive semidefinite before any separation
hypothesis. -/
theorem pairedEtaGeometricMultiplicityWeightedZeroGram_posSemidef
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    (pairedEtaGeometricMultiplicityWeightedZeroGram q s n).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- Linear independence of the actual packed eta features makes the
multiplicity-weighted synthesis map injective. -/
theorem pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mulVec_injective
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    Function.Injective
      (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
        q s n).mulVec := by
  rw [Matrix.mulVec_injective_iff]
  have hrows :=
    linearIndependent_rows_pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix
      hli
  simpa [pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix,
    Matrix.col] using hrows

/-- At every separated geometric block, the square zero-index Gram is
positive definite. -/
theorem pairedEtaGeometricMultiplicityWeightedZeroGram_posDef
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    (pairedEtaGeometricMultiplicityWeightedZeroGram q s n).PosDef := by
  exact Matrix.PosDef.conjTranspose_mul_self _
    (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_mulVec_injective
      hli)

/-- The inverse zero-index Gram is positive definite at every separated
geometric block. -/
theorem pairedEtaGeometricMultiplicityWeightedZeroGram_inv_posDef
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    (pairedEtaGeometricMultiplicityWeightedZeroGram q s n)⁻¹.PosDef :=
  (pairedEtaGeometricMultiplicityWeightedZeroGram_posDef hli).inv

/-- Every finite zeta-zero window has one odd prime base for which the
zero-index Gram and its inverse are both positive definite at all sufficiently
late geometric blocks. -/
theorem exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (pairedEtaGeometricMultiplicityWeightedZeroGram q s n).PosDef ∧
          (pairedEtaGeometricMultiplicityWeightedZeroGram q s n)⁻¹.PosDef := by
  obtain ⟨q, hqPrime, hqOdd, hq, hli⟩ :=
    exists_prime_eventually_linearIndependent_pairedEtaGeometricPackedHyperbolicFeature s
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hli] with n hlin
  have hlin' : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i) := by
    simpa only [pairedEtaGeometricPackedHyperbolicFeature] using hlin
  exact ⟨pairedEtaGeometricMultiplicityWeightedZeroGram_posDef hlin',
    pairedEtaGeometricMultiplicityWeightedZeroGram_inv_posDef hlin'⟩

end

end RiemannGaussian
