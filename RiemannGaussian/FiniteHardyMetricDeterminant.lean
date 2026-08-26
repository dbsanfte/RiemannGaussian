import RiemannGaussian.FiniteHardyResidualGram
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Basis-independent finite Hardy metric determinant

This file proves the operator identity proposed in the finite Hardy dispatch.
For the actual cross angle `C` and orthogonal residual map `R`, Lean proves

`R† R = I - C† C`.

It then proves a general change-of-basis theorem: in any basis of a
finite-dimensional Hilbert space, the determinant of `R† R` is the determinant
of the residual Gram matrix divided by that of the base Gram matrix.  This
removes any need to assume that the metric modes are distinct.
-/

open MeasureTheory
open scoped ComplexConjugate ENNReal InnerProduct

namespace RiemannGaussian

noncomputable section

/-- Polarized Pythagoras for two orthogonal-projection residuals. -/
theorem inner_sub_starProjection_sub_starProjection
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x y : E) :
    inner 𝕜 (x - K.starProjection x) (y - K.starProjection y) =
      inner 𝕜 x y -
        inner 𝕜 (K.starProjection x) (K.starProjection y) := by
  rw [inner_sub_right]
  rw [K.starProjection_inner_eq_zero x
    (K.starProjection y) (K.starProjection_apply_mem y), sub_zero]
  rw [inner_sub_left]
  congr 1
  rw [K.inner_starProjection_left_eq_right]
  rw [← sub_eq_zero]
  rw [← inner_sub_left]
  exact K.starProjection_inner_eq_zero x
    (K.starProjection y) (K.starProjection_apply_mem y)

/-- The orthogonal residual map on the actual finite negative Hardy model. -/
noncomputable def finiteHardyCrossAngleResidual
    (A : Polynomial ℝ) (tau : ℝ) :
    finiteNegativeBoundarySubspace A tau →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  ((1 : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
      Lp ℂ 2 (volume : Measure ℝ)) -
    (finitePositiveBoundarySubspace A tau).starProjection).comp
      (finiteNegativeBoundarySubspace A tau).subtypeL

@[simp] theorem finiteHardyCrossAngleResidual_apply
    (A : Polynomial ℝ) (tau : ℝ)
    (n : finiteNegativeBoundarySubspace A tau) :
    finiteHardyCrossAngleResidual A tau n =
      (n : Lp ℂ 2 (volume : Measure ℝ)) -
        (finiteHardyCrossAngle A tau n :
          Lp ℂ 2 (volume : Measure ℝ)) := by
  rfl

theorem finiteHardyCrossAngleResidual_inner
    (A : Polynomial ℝ) (tau : ℝ)
    (n m : finiteNegativeBoundarySubspace A tau) :
    inner ℂ (finiteHardyCrossAngleResidual A tau n)
        (finiteHardyCrossAngleResidual A tau m) =
      inner ℂ n m -
      inner ℂ (finiteHardyCrossAngle A tau n)
          (finiteHardyCrossAngle A tau m) := by
  change
    inner ℂ
        ((n : Lp ℂ 2 (volume : Measure ℝ)) -
          (finitePositiveBoundarySubspace A tau).starProjection n)
        ((m : Lp ℂ 2 (volume : Measure ℝ)) -
          (finitePositiveBoundarySubspace A tau).starProjection m) =
      inner ℂ (n : Lp ℂ 2 (volume : Measure ℝ)) m -
        inner ℂ ((finitePositiveBoundarySubspace A tau).starProjection n)
          ((finitePositiveBoundarySubspace A tau).starProjection m)
  exact inner_sub_starProjection_sub_starProjection
    (finitePositiveBoundarySubspace A tau)
    (n : Lp ℂ 2 (volume : Measure ℝ))
    (m : Lp ℂ 2 (volume : Measure ℝ))

/-- The residual Gram operator is exactly `I - C† C`. -/
theorem finiteHardyCrossAngleResidual_adjoint_comp_self
    (A : Polynomial ℝ) (tau : ℝ) :
    letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
      FiniteDimensional.complete ℂ _
    letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
      FiniteDimensional.complete ℂ _
    (finiteHardyCrossAngleResidual A tau).adjoint.comp
        (finiteHardyCrossAngleResidual A tau) =
      1 - (finiteHardyCrossAngle A tau).adjoint.comp
        (finiteHardyCrossAngle A tau) := by
  letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  apply ContinuousLinearMap.ext
  intro n
  apply ext_inner_right ℂ
  intro m
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  exact finiteHardyCrossAngleResidual_inner A tau n m

/-- The basis-independent cross-angle complement Gram operator. -/
noncomputable def finiteHardyCrossAngleComplementGramOperator
    (A : Polynomial ℝ) (tau : ℝ) :
    finiteNegativeBoundarySubspace A tau →L[ℂ]
      finiteNegativeBoundarySubspace A tau := by
  letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  exact 1 - (finiteHardyCrossAngle A tau).adjoint.comp
    (finiteHardyCrossAngle A tau)

theorem finiteHardyCrossAngleComplementGramOperator_eq_residual
    (A : Polynomial ℝ) (tau : ℝ) :
    letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
      FiniteDimensional.complete ℂ _
    letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
      FiniteDimensional.complete ℂ _
    finiteHardyCrossAngleComplementGramOperator A tau =
      (finiteHardyCrossAngleResidual A tau).adjoint.comp
        (finiteHardyCrossAngleResidual A tau) := by
  letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  rw [finiteHardyCrossAngleComplementGramOperator]
  exact (finiteHardyCrossAngleResidual_adjoint_comp_self A tau).symm

/-- Gram convention compatible with the project matrices: row `i`, column
`j` is `inner (b j) (b i)`. -/
def basisReverseGram
    {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : Module.Basis ι 𝕜 E) [Fintype ι] : Matrix ι ι 𝕜 :=
  fun i j ↦ inner 𝕜 (b j) (b i)

/-- Matrix of the sesquilinear form `inner x (T y)` in the project Gram
convention. -/
def basisOperatorReverseGram
    {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : Module.Basis ι 𝕜 E) [Fintype ι] (T : E →ₗ[𝕜] E) :
    Matrix ι ι 𝕜 :=
  fun i j ↦ inner 𝕜 (b j) (T (b i))

theorem basisOperatorReverseGram_eq_transpose_toMatrix_mul
    {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) (T : E →ₗ[𝕜] E) :
    basisOperatorReverseGram b T =
      Matrix.transpose (LinearMap.toMatrix b b T) * basisReverseGram b := by
  ext i j
  rw [basisOperatorReverseGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply,
    basisReverseGram]
  calc
    inner 𝕜 (b j) (T (b i)) =
        inner 𝕜 (b j)
          (∑ k, (b.repr (T (b i))) k • b k) := by
      rw [b.sum_repr]
    _ = ∑ k, (b.repr (T (b i))) k * inner 𝕜 (b j) (b k) := by
      rw [inner_sum]
      simp only [inner_smul_right]

theorem basisOperatorReverseGram_det
    {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) (T : E →ₗ[𝕜] E) :
    Matrix.det (basisOperatorReverseGram b T) =
      LinearMap.det T * Matrix.det (basisReverseGram b) := by
  rw [basisOperatorReverseGram_eq_transpose_toMatrix_mul,
    Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]

/-- Gram matrix of the images of a basis under a continuous linear map. -/
def basisMapReverseGram
    {𝕜 E F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (b : Module.Basis ι 𝕜 E) [Fintype ι] (R : E →L[𝕜] F) :
    Matrix ι ι 𝕜 :=
  fun i j ↦ inner 𝕜 (R (b j)) (R (b i))

theorem basisMapReverseGram_eq_adjointComp
    {𝕜 E F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [Fintype ι]
    (b : Module.Basis ι 𝕜 E) (R : E →L[𝕜] F) :
    basisMapReverseGram b R =
      basisOperatorReverseGram b (R.adjoint.comp R).toLinearMap := by
  ext i j
  change inner 𝕜 (R (b j)) (R (b i)) =
    inner 𝕜 (b j) (R.adjoint (R (b i)))
  exact (R.adjoint_inner_right (b j) (R (b i))).symm

theorem basisReverseGram_det_ne_zero
    {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) :
    Matrix.det (basisReverseGram b) ≠ 0 := by
  have htranspose : basisReverseGram b =
      Matrix.transpose (Matrix.gram 𝕜 b) := by
    ext i j
    rfl
  rw [htranspose, Matrix.det_transpose,
    Matrix.det_gram_ne_zero_iff_linearIndependent]
  exact b.linearIndependent

/-- Basis-independent determinant ratio for an arbitrary bounded map from a
finite-dimensional Hilbert space. -/
theorem basisMapReverseGram_det_ratio
    {𝕜 E F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝕜 E) (R : E →L[𝕜] F) :
    Matrix.det (basisMapReverseGram b R) /
        Matrix.det (basisReverseGram b) =
      LinearMap.det (R.adjoint.comp R).toLinearMap := by
  rw [basisMapReverseGram_eq_adjointComp,
    basisOperatorReverseGram_det]
  exact mul_div_cancel_right₀ _ (basisReverseGram_det_ne_zero b)

/-- Determinant of the actual cross-angle complement Gram operator as the
residual/base Gram ratio in an arbitrary basis of the negative model. -/
theorem finiteHardyCrossAngleComplementGramOperator_det_eq_basisResidual_ratio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Polynomial ℝ) (tau : ℝ)
    (b : Module.Basis ι ℂ (finiteNegativeBoundarySubspace A tau)) :
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
      Matrix.det
          (basisMapReverseGram b (finiteHardyCrossAngleResidual A tau)) /
        Matrix.det (basisReverseGram b) := by
  letI : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  letI : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  calc
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
        LinearMap.det
          ((finiteHardyCrossAngleResidual A tau).adjoint.comp
            (finiteHardyCrossAngleResidual A tau)).toLinearMap := by
      rw [finiteHardyCrossAngleComplementGramOperator_eq_residual]
    _ = Matrix.det
          (basisMapReverseGram b (finiteHardyCrossAngleResidual A tau)) /
        Matrix.det (basisReverseGram b) :=
      (basisMapReverseGram_det_ratio b
        (finiteHardyCrossAngleResidual A tau)).symm

end

end RiemannGaussian
