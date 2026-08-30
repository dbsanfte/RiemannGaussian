import RiemannGaussian.Hybrid.EtaGeometricPackedFeatureRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Multiplicity-weighted positive Gram companion for geometric eta features

The packed-feature separation theorem gives linearly independent vectors for
all distinct zeros in an arbitrary finite window.  This module retains their
analytic multiplicities and converts that information into a literal positive
Hermitian coordinate matrix.

Each feature column is scaled by the positive square root of its analytic
zero multiplicity.  The synthesis matrix times its conjugate transpose is
therefore exactly the sum of the multiplicity-weighted Hermitian rank-one
blocks `v v*`.  It is positive semidefinite, and its rank is exactly the
number of represented distinct zeros at all sufficiently late geometric
blocks.

This matrix is deliberately kept separate from the project's existing
complex-symmetric sum of `v vᵀ`, whose sign-bearing real-minus-imaginary
decomposition drives the inertia certificate.  The new Gram matrix proves
that the same literal eta carrier retains every represented zero in a
positive channel; it does not yet bound the signed certificate block or prove
a zero proportion.
-/

open Complex Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The actual packed geometric eta feature for one row of a finite zero
window. -/
def pairedEtaGeometricPackedHyperbolicFeature
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ)
    (i : Fin s.card) : Fin s.card × Fin 2 → ℂ :=
  pairedEtaTopPrefixFiniteCutoffFamilyFeature
    (fun j : Fin s.card ↦ pairedEtaGeometricHyperbolicCutoff q n j)
    ((etaZeroWindowEquivFin s).symm i)

/-- Row evaluation matrix of the actual packed geometric eta features. -/
def pairedEtaGeometricPackedHyperbolicFeatureRowMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card × Fin 2) ℂ := fun i ↦
  pairedEtaGeometricPackedHyperbolicFeature q s n i

/-- Positive square-root multiplicity used to retain the analytic divisor
weight in a Hermitian Gram factorization. -/
def pairedEtaGeometricMultiplicitySqrtWeight
    (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ)

/-- Every square-root analytic multiplicity is nonzero. -/
theorem pairedEtaGeometricMultiplicitySqrtWeight_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaGeometricMultiplicitySqrtWeight rho ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact Real.sqrt_ne_zero'.mpr
    (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)

/-- Squaring the real multiplicity weight recovers the analytic
multiplicity as a complex scalar. -/
theorem pairedEtaGeometricMultiplicitySqrtWeight_sq
    (rho : NontrivialZetaZero) :
    pairedEtaGeometricMultiplicitySqrtWeight rho *
        pairedEtaGeometricMultiplicitySqrtWeight rho =
      (analyticZetaZeroMultiplicity rho : ℂ) := by
  unfold pairedEtaGeometricMultiplicitySqrtWeight
  norm_cast
  exact Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- Row matrix after retaining analytic multiplicity through a nonzero
positive square-root scale on every genuine zero. -/
def pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card × Fin 2) ℂ := fun i j ↦
  pairedEtaGeometricMultiplicitySqrtWeight
      ((etaZeroWindowEquivFin s).symm i) *
    pairedEtaGeometricPackedHyperbolicFeature q s n i j

/-- Column synthesis matrix of the multiplicity-weighted packed eta
features. -/
def pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card × Fin 2) (Fin s.card) ℂ :=
  (pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix q s n)ᵀ

/-- Positive Hermitian coordinate companion formed from the same actual
packed eta features as the complex-symmetric certificate block. -/
def pairedEtaGeometricMultiplicityWeightedCoordinateGram
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card × Fin 2) (Fin s.card × Fin 2) ℂ :=
  pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q s n *
    (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix q s n)ᴴ

/-- The coordinate companion is exactly the sum of multiplicity-weighted
Hermitian outer products of the literal packed eta features. -/
theorem pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_sum
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    pairedEtaGeometricMultiplicityWeightedCoordinateGram q s n =
      ∑ i : Fin s.card,
        (analyticZetaZeroMultiplicity
            ((etaZeroWindowEquivFin s).symm i) : ℂ) •
          Matrix.vecMulVec
            (pairedEtaGeometricPackedHyperbolicFeature q s n i)
            (star (pairedEtaGeometricPackedHyperbolicFeature q s n i)) := by
  classical
  ext a b
  simp only [pairedEtaGeometricMultiplicityWeightedCoordinateGram,
    Matrix.mul_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix,
    Matrix.transpose_apply,
    pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix,
    Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [star_mul]
  have hstar :
      star (pairedEtaGeometricMultiplicitySqrtWeight
        ((etaZeroWindowEquivFin s).symm i)) =
        pairedEtaGeometricMultiplicitySqrtWeight
          ((etaZeroWindowEquivFin s).symm i) := by
    simp [pairedEtaGeometricMultiplicitySqrtWeight, RCLike.star_def,
      Complex.conj_ofReal]
  rw [hstar]
  calc
    _ = (pairedEtaGeometricMultiplicitySqrtWeight
            ((etaZeroWindowEquivFin s).symm i) *
          pairedEtaGeometricMultiplicitySqrtWeight
            ((etaZeroWindowEquivFin s).symm i)) *
        (pairedEtaGeometricPackedHyperbolicFeature q s n i a *
          star (pairedEtaGeometricPackedHyperbolicFeature q s n i b)) := by
            ring
    _ = _ := by
      rw [pairedEtaGeometricMultiplicitySqrtWeight_sq]

/-- The multiplicity-weighted coordinate companion is positive
semidefinite for every base and cutoff block. -/
theorem pairedEtaGeometricMultiplicityWeightedCoordinateGram_posSemidef
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    (pairedEtaGeometricMultiplicityWeightedCoordinateGram q s n).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- The positive coordinate companion is Hermitian. -/
theorem pairedEtaGeometricMultiplicityWeightedCoordinateGram_isHermitian
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    (pairedEtaGeometricMultiplicityWeightedCoordinateGram
      q s n).IsHermitian :=
  (pairedEtaGeometricMultiplicityWeightedCoordinateGram_posSemidef
    q s n).isHermitian

/-- Nonzero multiplicity scaling preserves linear independence of the actual
packed eta feature rows. -/
theorem linearIndependent_rows_pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    LinearIndependent ℂ
      (pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix q s n) := by
  change LinearIndependent ℂ (fun i ↦
    pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix q s n i)
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hunweighted :
      ∑ k,
          (c k * pairedEtaGeometricMultiplicitySqrtWeight
              ((etaZeroWindowEquivFin s).symm k)) •
            pairedEtaGeometricPackedHyperbolicFeature q s n k = 0 := by
    funext j
    have hj := congrFun hsum j
    simpa only [pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using hj
  have hscaled := Fintype.linearIndependent_iff.mp hli
    (fun k ↦ c k * pairedEtaGeometricMultiplicitySqrtWeight
      ((etaZeroWindowEquivFin s).symm k)) hunweighted i
  exact (mul_eq_zero.mp hscaled).resolve_right
    (pairedEtaGeometricMultiplicitySqrtWeight_ne_zero
      ((etaZeroWindowEquivFin s).symm i))

/-- Linear independence of the actual packed features gives full zero-column
rank to their multiplicity-weighted synthesis matrix. -/
theorem rank_pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_eq_card
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    (pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix
      q s n).rank = s.card := by
  rw [pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix,
    Matrix.rank_transpose]
  change Matrix.rank (fun i j ↦
    pairedEtaGeometricMultiplicitySqrtWeight
        ((etaZeroWindowEquivFin s).symm i) *
      pairedEtaGeometricPackedHyperbolicFeature q s n i j) = s.card
  simpa only [Fintype.card_fin] using
    (linearIndependent_rows_pairedEtaGeometricMultiplicityWeightedFeatureRowMatrix
      hli).rank_matrix

/-- The positive Hermitian companion has rank exactly equal to the number of
represented distinct zeta zeros whenever the packed features are independent. -/
theorem rank_pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_card
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hli : LinearIndependent ℂ
      (fun i : Fin s.card ↦
        pairedEtaGeometricPackedHyperbolicFeature q s n i)) :
    (pairedEtaGeometricMultiplicityWeightedCoordinateGram q s n).rank =
      s.card := by
  unfold pairedEtaGeometricMultiplicityWeightedCoordinateGram
  rw [Matrix.rank_self_mul_conjTranspose]
  exact
    rank_pairedEtaGeometricMultiplicityWeightedFeatureSynthesisMatrix_eq_card
      hli

/-- Every finite zeta-zero window has one odd prime base for which all
sufficiently late multiplicity-weighted coordinate companions are positive
semidefinite and have rank exactly the number of represented distinct zeros. -/
theorem exists_prime_eventually_posSemidef_and_rank_pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_card
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (pairedEtaGeometricMultiplicityWeightedCoordinateGram
            q s n).PosSemidef ∧
          (pairedEtaGeometricMultiplicityWeightedCoordinateGram
            q s n).rank = s.card := by
  obtain ⟨q, hqPrime, hqOdd, hq, hli⟩ :=
    exists_prime_eventually_linearIndependent_pairedEtaGeometricPackedHyperbolicFeature s
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hli] with n hlin
  exact ⟨pairedEtaGeometricMultiplicityWeightedCoordinateGram_posSemidef
      q s n,
    rank_pairedEtaGeometricMultiplicityWeightedCoordinateGram_eq_card
      (by simpa only [pairedEtaGeometricPackedHyperbolicFeature] using hlin)⟩

end

end RiemannGaussian
