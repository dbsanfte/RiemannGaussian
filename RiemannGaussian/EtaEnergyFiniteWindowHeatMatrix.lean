import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteGaussianGram
import RiemannGaussian.EtaEnergyFiniteWindowMatrixLeading
import Mathlib.Analysis.Matrix.Order

/-!
# Gaussian proper-time compression of finite eta zero-window matrices

This module joins the continuous Gaussian parameter to the finite eta matrix
frontier without first taking a trace or norm.  The already proved finite
Gaussian arithmetic quadratic is realized as the quadratic form of a literal
kernel matrix.  Its positivity proves that

`exp (-u * (lambda_i - lambda_j)^2)`

is positive semidefinite at every positive proper time `u`.  Schur
multiplication by this kernel therefore gives a positivity-preserving finite
heat compression.

For the eta zero-window matrices, the nodes are the exact centered cutoff
times `log (2N+1)`, repeated across the two hyperbolic channels.  Lean proves
that the compressed matrix remains the genuine multiplicity-weighted zero
sum, retains the exact `onLine + (offReal - offImag)` decomposition, and is
Hermitian.  Each matrix entry is differentiable in proper time with the
explicit squared-gap generator.  The previously proved leading/remainder
matrix-work decomposition also commutes exactly with this heat compression.

These are finite exact identities.  No limiting operator, arithmetic
cancellation estimate, or zero-location consequence is inferred here.
-/

open Complex
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-! ## The Gaussian quadratic as a positive kernel matrix -/

/-- Matrix whose quadratic form is the existing finite Gaussian Gram
quadratic on a complete finite index type. -/
def finiteGaussianGramKernelMatrix {d : Type*}
    (frequency : d → ℝ) (tau x : ℝ) : Matrix d d ℂ :=
  fun k j ↦
    (Real.sqrt (Real.pi / tau) : ℂ) *
      Complex.exp
        (((-(frequency k - frequency j) ^ 2 / (4 * tau) : ℝ) : ℂ) +
          Complex.I * (x * (frequency k - frequency j)))

/-- The quadratic form of the finite Gaussian kernel matrix is exactly the
previously proved arithmetic Gaussian Gram quadratic. -/
theorem finiteGaussianGramKernelMatrix_quadratic_eq
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (tau x : ℝ) (c : d → ℂ) :
    star c ⬝ᵥ Matrix.mulVec
        (finiteGaussianGramKernelMatrix frequency tau x) c =
      finiteGaussianGramQuadratic Finset.univ c frequency tau x := by
  unfold finiteGaussianGramKernelMatrix finiteGaussianGramQuadratic
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The finite Gaussian kernel matrix is Hermitian for all real parameters. -/
theorem finiteGaussianGramKernelMatrix_isHermitian
    {d : Type*} (frequency : d → ℝ) (tau x : ℝ) :
    (finiteGaussianGramKernelMatrix frequency tau x).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, finiteGaussianGramKernelMatrix,
    ← Complex.exp_conj]
  left
  congr 1
  simp only [starRingEnd_apply]
  norm_num
  ring

/-- At positive Gaussian precision, the complete finite Gaussian kernel
matrix is positive semidefinite. -/
theorem finiteGaussianGramKernelMatrix_posSemidef
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    {tau : ℝ} (htau : 0 < tau) (x : ℝ) :
    (finiteGaussianGramKernelMatrix frequency tau x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (finiteGaussianGramKernelMatrix_isHermitian frequency tau x)
  intro c
  rw [finiteGaussianGramKernelMatrix_quadratic_eq]
  rw [Complex.nonneg_iff]
  constructor
  · exact finiteGaussianGramQuadratic_re_nonneg
      Finset.univ c frequency htau x
  · exact (finiteGaussianGramQuadratic_im
      Finset.univ c frequency htau x).symm

/-! ## Proper-time kernel, generator, and Schur compression -/

/-- The unnormalized Gaussian proper-time kernel on a finite real node
family. -/
def finiteGaussianProperTimeKernelMatrix {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) : Matrix d d ℂ :=
  fun i j ↦
    (Real.exp (-heat * (frequency i - frequency j) ^ 2) : ℂ)

/-- The proper-time kernel is exactly a positive scalar rescaling of the
existing Gaussian Gram kernel at precision `(4 * heat)⁻¹`. -/
theorem finiteGaussianProperTimeKernelMatrix_eq_scaled_gram
    {d : Type*} (frequency : d → ℝ) {heat : ℝ} (hheat : 0 < heat) :
    finiteGaussianProperTimeKernelMatrix frequency heat =
      ((Real.sqrt (Real.pi / (4 * heat)⁻¹))⁻¹ : ℂ) •
        finiteGaussianGramKernelMatrix frequency (4 * heat)⁻¹ 0 := by
  have htau : 0 < (4 * heat)⁻¹ := by positivity
  have hsqrt : 0 < Real.sqrt (Real.pi / (4 * heat)⁻¹) := by positivity
  have hsqrtComplex :
      (Real.sqrt (Real.pi / (4 * heat)⁻¹) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt.ne'
  ext i j
  simp only [finiteGaussianProperTimeKernelMatrix,
    finiteGaussianGramKernelMatrix, Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hsqrtComplex, one_mul]
  push_cast
  field_simp [hheat.ne']
  ring_nf

/-- The Gaussian proper-time kernel is positive semidefinite at every
positive proper time. -/
theorem finiteGaussianProperTimeKernelMatrix_posSemidef
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    {heat : ℝ} (hheat : 0 < heat) :
    (finiteGaussianProperTimeKernelMatrix frequency heat).PosSemidef := by
  have htau : 0 < (4 * heat)⁻¹ := by positivity
  have hgram := finiteGaussianGramKernelMatrix_posSemidef
    frequency htau 0
  have hscale :
      (0 : ℂ) ≤ ((Real.sqrt (Real.pi / (4 * heat)⁻¹))⁻¹ : ℂ) := by
    positivity
  rw [finiteGaussianProperTimeKernelMatrix_eq_scaled_gram
    frequency hheat]
  exact hgram.smul hscale

/-- Entrywise infinitesimal generator of the Gaussian proper-time kernel. -/
def finiteGaussianProperTimeGeneratorMatrix {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) : Matrix d d ℂ :=
  fun i j ↦
    ((-(frequency i - frequency j) ^ 2 : ℝ) : ℂ) *
      finiteGaussianProperTimeKernelMatrix frequency heat i j

/-- Every entry of the proper-time kernel has the explicit squared-gap
derivative. -/
theorem hasDerivAt_finiteGaussianProperTimeKernelMatrix_apply
    {d : Type*} (frequency : d → ℝ) (heat : ℝ) (i j : d) :
    HasDerivAt
      (fun u : ℝ ↦
        finiteGaussianProperTimeKernelMatrix frequency u i j)
      (finiteGaussianProperTimeGeneratorMatrix frequency heat i j)
      heat := by
  let q : ℝ := (frequency i - frequency j) ^ 2
  have hinner : HasDerivAt (fun u : ℝ ↦ -u * q) (-q) heat := by
    simpa using (hasDerivAt_id heat).neg.mul_const q
  have hreal : HasDerivAt (fun u : ℝ ↦ Real.exp (-(u * q)))
      (-q * Real.exp (-(heat * q))) heat := by
    simpa only [Function.comp_def, mul_comm, neg_mul] using
      (Real.hasDerivAt_exp (-heat * q)).comp heat hinner
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp heat hreal.hasFDerivAt
  unfold finiteGaussianProperTimeGeneratorMatrix
    finiteGaussianProperTimeKernelMatrix
  dsimp only [q] at hcomplex
  simpa only [Function.comp_def, Complex.ofRealCLM_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul] using
      hcomplex.hasDerivAt

/-- Schur compression of a complex matrix by the Gaussian proper-time
kernel. -/
def finiteGaussianProperTimeCompression {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  finiteGaussianProperTimeKernelMatrix frequency heat ⊙ A

/-- Entrywise generator of the Gaussian proper-time compression. -/
def finiteGaussianProperTimeCompressionGenerator {d : Type*}
    (frequency : d → ℝ) (heat : ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ :=
  finiteGaussianProperTimeGeneratorMatrix frequency heat ⊙ A

/-- Differentiating a fixed matrix after Gaussian compression gives the
explicit compressed squared-gap generator, entry by entry. -/
theorem hasDerivAt_finiteGaussianProperTimeCompression_apply
    {d : Type*} (frequency : d → ℝ) (heat : ℝ)
    (A : Matrix d d ℂ) (i j : d) :
    HasDerivAt
      (fun u : ℝ ↦ finiteGaussianProperTimeCompression frequency u A i j)
      (finiteGaussianProperTimeCompressionGenerator frequency heat A i j)
      heat := by
  simpa only [finiteGaussianProperTimeCompression,
    finiteGaussianProperTimeCompressionGenerator, Matrix.hadamard_apply]
    using
      (hasDerivAt_finiteGaussianProperTimeKernelMatrix_apply
        frequency heat i j).mul_const (A i j)

/-- Gaussian proper-time compression commutes with every finite matrix sum. -/
theorem finiteGaussianProperTimeCompression_finsetSum
    {d alpha : Type*} (frequency : d → ℝ) (heat : ℝ)
    (S : Finset alpha) (A : alpha → Matrix d d ℂ) :
    finiteGaussianProperTimeCompression frequency heat (∑ a ∈ S, A a) =
      ∑ a ∈ S, finiteGaussianProperTimeCompression frequency heat (A a) := by
  ext i j
  simp only [finiteGaussianProperTimeCompression, Matrix.hadamard_apply,
    Matrix.sum_apply, Finset.mul_sum]

/-- Gaussian proper-time compression preserves positive semidefiniteness. -/
theorem finiteGaussianProperTimeCompression_posSemidef
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    {heat : ℝ} (hheat : 0 < heat)
    {A : Matrix d d ℂ} (hA : A.PosSemidef) :
    (finiteGaussianProperTimeCompression frequency heat A).PosSemidef := by
  unfold finiteGaussianProperTimeCompression
  exact (finiteGaussianProperTimeKernelMatrix_posSemidef
    frequency hheat).hadamard hA

/-! ## Eta cutoff heat nodes and compressed zero-window blocks -/

/-- Centered logarithmic cutoff time attached to each packed eta coordinate.
The two hyperbolic channels at the same cutoff share one node. -/
def pairedEtaTopPrefixFiniteCutoffFamilyHeatNode {d : Type*}
    (cutoff : d → ℕ) : d × Fin 2 → ℝ :=
  fun j ↦ Real.log (((2 * cutoff j.1 + 1 : ℕ) : ℝ))

/-- Proper-time Gaussian compression of the complete finite eta zero-window
block. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock {d : Type*}
    (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T)

/-- Explicit proper-time generator of the compressed eta zero-window block. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowGenerator {d : Type*}
    (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompressionGenerator
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T)

/-- Every entry of the actual compressed eta zero-window block has the
explicit proper-time derivative. -/
theorem hasDerivAt_pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock_apply
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ)
    (i j : d × Fin 2) :
    HasDerivAt
      (fun u : ℝ ↦
        pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock cutoff T u i j)
      (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowGenerator
        cutoff T heat i j)
      heat := by
  exact hasDerivAt_finiteGaussianProperTimeCompression_apply
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) i j

/-- Heat compression commutes with the genuine multiplicity-weighted finite
zero sum defining the eta window block. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock_eq_zeroSum
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock cutoff T heat =
      ∑ rho ∈ spectralZetaZeroWindow T,
        finiteGaussianProperTimeCompression
          (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
          ((analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) := by
  unfold pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock
    pairedEtaTopPrefixFiniteZeroWindowBlock
  exact finiteGaussianProperTimeCompression_finsetSum _ _ _ _

/-- Heat-compressed critical-line portion of the eta zero-window block. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOnLineBlock {d : Type*}
    (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T)

/-- Heat-compressed positive real portion of the off-line eta pairs. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineRealBlock
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T)

/-- Heat-compressed positive imaginary portion of the off-line eta pairs. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineImagBlock
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T)

/-- The heat-compressed critical-line eta block remains positive
semidefinite. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOnLineBlock_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    {heat : ℝ} (hheat : 0 < heat) :
    (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOnLineBlock
      cutoff T heat).PosSemidef := by
  exact finiteGaussianProperTimeCompression_posSemidef _ hheat
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T)

/-- The heat-compressed real off-line eta block remains positive
semidefinite. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineRealBlock_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    {heat : ℝ} (hheat : 0 < heat) :
    (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineRealBlock
      cutoff T heat).PosSemidef := by
  exact finiteGaussianProperTimeCompression_posSemidef _ hheat
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef cutoff T)

/-- The heat-compressed imaginary off-line eta block remains positive
semidefinite. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineImagBlock_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    {heat : ℝ} (hheat : 0 < heat) :
    (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineImagBlock
      cutoff T heat).PosSemidef := by
  exact finiteGaussianProperTimeCompression_posSemidef _ hheat
    (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef cutoff T)

/-- Exact heat-compressed zero-window structure: Gaussian compression retains
the on-line block plus the difference of the two off-line positive blocks. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
    {d : Type*} (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (heat : ℝ) :
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock cutoff T heat =
      pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOnLineBlock cutoff T heat +
        (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineRealBlock
            cutoff T heat -
          pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineImagBlock
            cutoff T heat) := by
  unfold pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOnLineBlock
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineRealBlock
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowOffLineImagBlock
    finiteGaussianProperTimeCompression
  rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
    cutoff hT]
  ext i j
  simp only [Matrix.hadamard_apply, Matrix.add_apply, Matrix.sub_apply]
  ring

/-- At positive proper time and on a nonnegative spectral window, the full
heat-compressed eta block is Hermitian. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock_isHermitian
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    {T heat : ℝ} (hT : 0 ≤ T) (hheat : 0 < heat) :
    (pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock
      cutoff T heat).IsHermitian := by
  unfold pairedEtaTopPrefixFiniteHeatCompressedZeroWindowBlock
    finiteGaussianProperTimeCompression
  exact
    (finiteGaussianProperTimeKernelMatrix_posSemidef
      (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) hheat).isHermitian.hadamard
        (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)

/-! ## Heat compression of the matrix-current transport law -/

/-- Heat compression of the leading eta zero-window matrix current. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowLeadingCurrent
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T)

/-- Heat compression of the remainder eta zero-window matrix current. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowRemainderCurrent
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent cutoff T)

/-- Heat compression of the exact eta zero-window matrix work. -/
def pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  finiteGaussianProperTimeCompression
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode cutoff) heat
    (pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T)

/-- The exact leading/remainder eta matrix-current law commutes with Gaussian
proper-time compression at every real heat parameter. -/
theorem pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork_eq_leading_add_remainder
    {d : Type*} (cutoff : d → ℕ) (T heat : ℝ) :
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork cutoff T heat =
      pairedEtaTopPrefixFiniteHeatCompressedZeroWindowLeadingCurrent
          cutoff T heat +
        pairedEtaTopPrefixFiniteHeatCompressedZeroWindowRemainderCurrent
          cutoff T heat := by
  unfold pairedEtaTopPrefixFiniteHeatCompressedZeroWindowMatrixWork
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowLeadingCurrent
    pairedEtaTopPrefixFiniteHeatCompressedZeroWindowRemainderCurrent
    finiteGaussianProperTimeCompression
  rw [topPrefixFiniteZeroWindowMatrixWork_eq_leading_add_remainder]
  ext i j
  simp only [Matrix.hadamard_apply, Matrix.add_apply]
  ring

end

end RiemannGaussian
