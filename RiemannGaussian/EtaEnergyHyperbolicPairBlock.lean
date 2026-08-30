import RiemannGaussian.EtaEnergyLeadingFluxKernelFactorization
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Hyperbolic pair coordinates for the finite eta energy

This module compresses the two completed finite eta-prefix terms at the live
frontier into one two-dimensional feature.  After aligning the parity in the
conjugate-original term, critical-line reflection swaps the two terms through
complex conjugation.  Their even coordinate is therefore conjugation-even and
their odd coordinate conjugation-odd.  Multiplying the odd coordinate by `I`
produces a feature which reflection sends to its componentwise conjugate.

The existing signed finite eta energy is exactly the Hermitian quadratic form
of this feature against one fixed hyperbolic `2 x 2` signature matrix.  This is
the concrete interface needed for finite-window rank and inertia arguments.

We also record the sign convention behind conjugate-pair compression.  The
complex-symmetric pair `v vᵀ + conj(v) conj(v)ᵀ` is a difference of two
positive rank-one real blocks.  The Hermitian Gram pair
`v v* + conj(v) conj(v)*` is instead their sum.  These are distinct identities;
the indefinite sign belongs only to the transpose construction.
-/

open Complex
open scoped ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-! ## Generic conjugate-pair algebra -/

/-- The componentwise real part of a complex vector, regarded as a complex
vector with real entries. -/
def complexVectorReal {d : Type*} (v : d → ℂ) : d → ℂ :=
  fun j ↦ ((v j).re : ℂ)

/-- The componentwise imaginary part of a complex vector, regarded as a
complex vector with real entries. -/
def complexVectorImag {d : Type*} (v : d → ℂ) : d → ℂ :=
  fun j ↦ ((v j).im : ℂ)

@[simp] theorem star_complexVectorReal {d : Type*} (v : d → ℂ) :
    star (complexVectorReal v) = complexVectorReal v := by
  funext j
  simp [complexVectorReal]

@[simp] theorem star_complexVectorImag {d : Type*} (v : d → ℂ) :
    star (complexVectorImag v) = complexVectorImag v := by
  funext j
  simp [complexVectorImag]

/-- The complex-symmetric sum of a vector outer product and its conjugate
partner.  The second vector in each outer product is not conjugated. -/
def complexSymmetricConjugatePairBlock {d : Type*} (v : d → ℂ) :
    Matrix d d ℂ :=
  Matrix.vecMulVec v v + Matrix.vecMulVec (star v) (star v)

/-- The Hermitian Gram sum of a vector and its conjugate partner. -/
def complexHermitianConjugatePairGram {d : Type*} (v : d → ℂ) :
    Matrix d d ℂ :=
  Matrix.vecMulVec v (star v) + Matrix.vecMulVec (star v) v

/-- The transpose conjugate-pair block is indefinite in general: it is twice
the real rank-one block minus twice the imaginary rank-one block. -/
theorem complexSymmetricConjugatePairBlock_eq_real_sub_imag
    {d : Type*} (v : d → ℂ) :
    complexSymmetricConjugatePairBlock v =
      (2 : ℂ) • Matrix.vecMulVec (complexVectorReal v) (complexVectorReal v) -
        (2 : ℂ) • Matrix.vecMulVec (complexVectorImag v) (complexVectorImag v) := by
  ext i j
  simp only [complexSymmetricConjugatePairBlock, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, complexVectorReal, complexVectorImag,
    smul_eq_mul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

/-- In contrast, the conjugate-transpose pair is a positive sum: it is twice
the real rank-one block plus twice the imaginary rank-one block. -/
theorem complexHermitianConjugatePairGram_eq_real_add_imag
    {d : Type*} (v : d → ℂ) :
    complexHermitianConjugatePairGram v =
      (2 : ℂ) • Matrix.vecMulVec (complexVectorReal v) (complexVectorReal v) +
        (2 : ℂ) • Matrix.vecMulVec (complexVectorImag v) (complexVectorImag v) := by
  ext i j
  simp only [complexHermitianConjugatePairGram, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, complexVectorReal, complexVectorImag, smul_eq_mul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Twice the real rank-one block in the conjugate-pair decomposition is
positive semidefinite. -/
theorem complexVectorRealPairBlock_posSemidef
    {d : Type*} [Finite d] (v : d → ℂ) :
    ((2 : ℂ) •
      Matrix.vecMulVec (complexVectorReal v) (complexVectorReal v)).PosSemidef := by
  have hbase := Matrix.posSemidef_vecMulVec_self_star (complexVectorReal v)
  rw [star_complexVectorReal] at hbase
  exact hbase.smul (Complex.zero_le_real.mpr (by norm_num))

/-- Twice the imaginary rank-one block in the conjugate-pair decomposition
is positive semidefinite. -/
theorem complexVectorImagPairBlock_posSemidef
    {d : Type*} [Finite d] (v : d → ℂ) :
    ((2 : ℂ) •
      Matrix.vecMulVec (complexVectorImag v) (complexVectorImag v)).PosSemidef := by
  have hbase := Matrix.posSemidef_vecMulVec_self_star (complexVectorImag v)
  rw [star_complexVectorImag] at hbase
  exact hbase.smul (Complex.zero_le_real.mpr (by norm_num))

/-- Although it is generally indefinite, the complex-symmetric conjugate
pair block is Hermitian because it is the difference of two real positive
semidefinite blocks. -/
theorem complexSymmetricConjugatePairBlock_isHermitian
    {d : Type*} [Finite d] (v : d → ℂ) :
    (complexSymmetricConjugatePairBlock v).IsHermitian := by
  rw [complexSymmetricConjugatePairBlock_eq_real_sub_imag]
  exact (complexVectorRealPairBlock_posSemidef v).isHermitian.sub
    (complexVectorImagPairBlock_posSemidef v).isHermitian

/-- The ordinary Hermitian conjugate-pair Gram is positive semidefinite. -/
theorem complexHermitianConjugatePairGram_posSemidef
    {d : Type*} [Finite d] (v : d → ℂ) :
    (complexHermitianConjugatePairGram v).PosSemidef := by
  unfold complexHermitianConjugatePairGram
  exact (Matrix.posSemidef_vecMulVec_self_star v).add
    (by simpa using Matrix.posSemidef_vecMulVec_self_star (star v))

/-! ## Eta-specific hyperbolic coordinates -/

/-- The parity factor already present in the conjugate-original finite eta
term. -/
def pairedEtaTopPrefixFiniteParity (rho : NontrivialZetaZero) : ℂ :=
  (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho

@[simp] theorem pairedEtaTopPrefixFiniteParity_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteParity
        (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaTopPrefixFiniteParity rho := by
  simp [pairedEtaTopPrefixFiniteParity,
    analyticZetaZeroMultiplicity_conjugatePartner]

@[simp] theorem star_pairedEtaTopPrefixFiniteParity
    (rho : NontrivialZetaZero) :
    starRingEnd ℂ (pairedEtaTopPrefixFiniteParity rho) =
      pairedEtaTopPrefixFiniteParity rho := by
  simp [pairedEtaTopPrefixFiniteParity]

@[simp] theorem pairedEtaTopPrefixFiniteParity_mul_self
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteParity rho *
        pairedEtaTopPrefixFiniteParity rho = 1 := by
  unfold pairedEtaTopPrefixFiniteParity
  rw [← mul_pow]
  norm_num

/-- Remove the duplicate parity from the conjugate-original term.  The
result is the literal conjugate of the completed original finite prefix. -/
def pairedEtaTopPrefixFiniteAlignedConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaTopPrefixFiniteParity rho *
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
      rho N

/-- Reflection sends the partner term to the conjugate of the aligned
conjugate-original term. -/
theorem topPrefixFinitePartnerTerm_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
        (NontrivialZetaZero.conjugatePartner rho) N =
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N) := by
  unfold pairedEtaTopPrefixFiniteAlignedConjugateTerm
    pairedEtaTopPrefixFiniteParity
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
  simp only [NontrivialZetaZero.conjugatePartner_conjugatePartner,
    analyticZetaZeroMultiplicity_conjugatePartner, map_mul, map_pow,
    map_neg, map_one, starRingEnd_apply, star_star]
  have hparity :
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hparity, one_mul]

/-- Reflection sends the aligned conjugate-original term to the conjugate of
the partner term. -/
theorem topPrefixFiniteAlignedConjugateTerm_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteAlignedConjugateTerm
        (NontrivialZetaZero.conjugatePartner rho) N =
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho N) := by
  unfold pairedEtaTopPrefixFiniteAlignedConjugateTerm
    pairedEtaTopPrefixFiniteParity
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
  simp only [analyticZetaZeroMultiplicity_conjugatePartner]
  have hparity :
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hparity, one_mul]

/-- The reflection-even coordinate of the two completed finite eta-prefix
terms. -/
def pairedEtaTopPrefixFiniteEvenCoordinate
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho N +
    pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N

/-- The reflection-odd coordinate of the two completed finite eta-prefix
terms. -/
def pairedEtaTopPrefixFiniteOddCoordinate
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho N -
    pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N

/-- The even coordinate becomes its complex conjugate under critical-line
reflection. -/
theorem topPrefixFiniteEvenCoordinate_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteEvenCoordinate
        (NontrivialZetaZero.conjugatePartner rho) N =
      starRingEnd ℂ (pairedEtaTopPrefixFiniteEvenCoordinate rho N) := by
  unfold pairedEtaTopPrefixFiniteEvenCoordinate
  rw [topPrefixFinitePartnerTerm_conjugatePartner,
    topPrefixFiniteAlignedConjugateTerm_conjugatePartner, map_add]
  ring

/-- The odd coordinate becomes the negative of its complex conjugate under
critical-line reflection. -/
theorem topPrefixFiniteOddCoordinate_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteOddCoordinate
        (NontrivialZetaZero.conjugatePartner rho) N =
      -starRingEnd ℂ (pairedEtaTopPrefixFiniteOddCoordinate rho N) := by
  unfold pairedEtaTopPrefixFiniteOddCoordinate
  rw [topPrefixFinitePartnerTerm_conjugatePartner,
    topPrefixFiniteAlignedConjugateTerm_conjugatePartner, map_sub]
  ring

/-- Two-dimensional eta feature obtained by multiplying the odd coordinate
by `I`.  This twist converts reflection-odd conjugation into ordinary
componentwise conjugation. -/
def pairedEtaTopPrefixFiniteHyperbolicFeature
    (rho : NontrivialZetaZero) (N : ℕ) : Fin 2 → ℂ :=
  ![pairedEtaTopPrefixFiniteEvenCoordinate rho N,
    I * pairedEtaTopPrefixFiniteOddCoordinate rho N]

/-- Critical-line reflection sends the eta hyperbolic feature to its
componentwise complex conjugate. -/
theorem topPrefixFiniteHyperbolicFeature_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteHyperbolicFeature
        (NontrivialZetaZero.conjugatePartner rho) N =
      star (pairedEtaTopPrefixFiniteHyperbolicFeature rho N) := by
  funext j
  fin_cases j
  · simp [pairedEtaTopPrefixFiniteHyperbolicFeature,
      topPrefixFiniteEvenCoordinate_conjugatePartner]
  · simp [pairedEtaTopPrefixFiniteHyperbolicFeature,
      topPrefixFiniteOddCoordinate_conjugatePartner]

/-- The fixed `2 x 2` hyperbolic signature matrix used by the eta feature. -/
def pairedEtaTopPrefixFiniteHyperbolicSignature : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -I / 2;
     I / 2, 0]

/-- The eta signature matrix is Hermitian. -/
theorem pairedEtaTopPrefixFiniteHyperbolicSignature_isHermitian :
    pairedEtaTopPrefixFiniteHyperbolicSignature.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedEtaTopPrefixFiniteHyperbolicSignature,
      Matrix.conjTranspose_apply]

/-- Real Hermitian quadratic form of the fixed eta signature matrix. -/
def pairedEtaTopPrefixFiniteHyperbolicForm (v : Fin 2 → ℂ) : ℝ :=
  (star v ⬝ᵥ
    Matrix.mulVec pairedEtaTopPrefixFiniteHyperbolicSignature v).re

/-- In even/odd coordinates, the fixed signature form is the real mixed
pairing between those coordinates. -/
theorem pairedEtaTopPrefixFiniteHyperbolicForm_mk (u v : ℂ) :
    pairedEtaTopPrefixFiniteHyperbolicForm ![u, I * v] =
      (u * starRingEnd ℂ v).re := by
  unfold pairedEtaTopPrefixFiniteHyperbolicForm
    pairedEtaTopPrefixFiniteHyperbolicSignature
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Multiplying the conjugate-original term by its parity does not change
its squared norm. -/
theorem normSq_topPrefixFiniteAlignedConjugateTerm
    (rho : NontrivialZetaZero) (N : ℕ) :
    Complex.normSq (pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N) =
      Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho N) := by
  unfold pairedEtaTopPrefixFiniteAlignedConjugateTerm
  rw [Complex.normSq_mul]
  have hparity :
      Complex.normSq (pairedEtaTopPrefixFiniteParity rho) = 1 := by
    unfold pairedEtaTopPrefixFiniteParity
    rw [Complex.normSq_eq_norm_sq, norm_pow, norm_neg, norm_one, one_pow]
    norm_num
  rw [hparity, one_mul]

/-- The current signed finite eta energy is exactly the fixed hyperbolic
Hermitian form of the reflection-equivariant two-coordinate feature. -/
theorem topPrefixFiniteEnergyDifference_eq_hyperbolicForm
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N =
      pairedEtaTopPrefixFiniteHyperbolicForm
        (pairedEtaTopPrefixFiniteHyperbolicFeature rho N) := by
  let P :=
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho N
  let Q := pairedEtaTopPrefixFiniteAlignedConjugateTerm rho N
  have hform :
      pairedEtaTopPrefixFiniteHyperbolicForm
          (pairedEtaTopPrefixFiniteHyperbolicFeature rho N) =
        Complex.normSq P - Complex.normSq Q := by
    rw [show pairedEtaTopPrefixFiniteHyperbolicFeature rho N =
        ![P + Q, I * (P - Q)] by
      rfl, pairedEtaTopPrefixFiniteHyperbolicForm_mk]
    simp only [map_sub]
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  rw [hform]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  rw [← norm_topPrefixFinitePartnerTerm_eq_finitePartnerAmplitude,
    ← norm_topPrefixFiniteConjugateTerm_eq_finiteConjugateAmplitude,
    ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  change Complex.normSq P - _ = _
  rw [normSq_topPrefixFiniteAlignedConjugateTerm]

/-- The reflected eta feature therefore supplies the literal
complex-symmetric conjugate-pair block used in rank/inertia compression. -/
theorem topPrefixFiniteHyperbolicFeature_pairBlock_eq_real_sub_imag
    (rho : NontrivialZetaZero) (N : ℕ) :
    Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteHyperbolicFeature rho N)
          (pairedEtaTopPrefixFiniteHyperbolicFeature rho N) +
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteHyperbolicFeature
            (NontrivialZetaZero.conjugatePartner rho) N)
          (pairedEtaTopPrefixFiniteHyperbolicFeature
            (NontrivialZetaZero.conjugatePartner rho) N) =
      (2 : ℂ) • Matrix.vecMulVec
          (complexVectorReal
            (pairedEtaTopPrefixFiniteHyperbolicFeature rho N))
          (complexVectorReal
            (pairedEtaTopPrefixFiniteHyperbolicFeature rho N)) -
        (2 : ℂ) • Matrix.vecMulVec
          (complexVectorImag
            (pairedEtaTopPrefixFiniteHyperbolicFeature rho N))
          (complexVectorImag
            (pairedEtaTopPrefixFiniteHyperbolicFeature rho N)) := by
  rw [topPrefixFiniteHyperbolicFeature_conjugatePartner]
  exact complexSymmetricConjugatePairBlock_eq_real_sub_imag _

/-- Each reflected eta feature pair gives a genuine Hermitian block.  Its
indefiniteness is confined to the difference of the two explicit positive
rank-one real and imaginary parts above. -/
theorem topPrefixFiniteHyperbolicFeature_pairBlock_isHermitian
    (rho : NontrivialZetaZero) (N : ℕ) :
    (Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteHyperbolicFeature rho N)
          (pairedEtaTopPrefixFiniteHyperbolicFeature rho N) +
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteHyperbolicFeature
            (NontrivialZetaZero.conjugatePartner rho) N)
          (pairedEtaTopPrefixFiniteHyperbolicFeature
            (NontrivialZetaZero.conjugatePartner rho) N)).IsHermitian := by
  rw [topPrefixFiniteHyperbolicFeature_conjugatePartner]
  exact complexSymmetricConjugatePairBlock_isHermitian _

end

end RiemannGaussian
