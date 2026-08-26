import RiemannGaussian.FiniteHardyMetricDeterminant

/-!
# Cauchy bases for the finite negative Hardy model

An upper-half-plane zero `w` of the finite Blaschke numerator gives a
boundary Cauchy vector `x ↦ (x - conj w)⁻¹`.  This file proves directly that
the vector belongs to the actual negative rational `L²` model.  For two
distinct such zeros and a degree-two Blaschke factor, the two vectors are
then promoted to a basis of that model.
-/

open MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal Matrix

namespace RiemannGaussian

noncomputable section

/-- The quotient coordinate which represents a Cauchy kernel at a root of
its denominator. -/
def finiteModelRootCauchyCoordinate
    (P : ℂ[X]) (gamma : ℂ) (hP : P ≠ 0) : finiteModelSpace P :=
  ⟨P / (X - C gamma), by
    change P / (X - C gamma) ∈ Polynomial.degreeLT ℂ P.natDegree
    rw [Polynomial.mem_degreeLT]
    calc
      degree (P / (X - C gamma)) < degree P :=
        degree_div_lt hP (by simp [degree_X_sub_C])
      _ = (P.natDegree : WithBot ℕ) := degree_eq_natDegree hP⟩

/-- Removing the root's linear factor and multiplying it back reconstructs
the denominator exactly. -/
theorem X_sub_C_mul_finiteModelRootCauchyCoordinate
    {P : ℂ[X]} {gamma : ℂ} (hP : P ≠ 0) (hgamma : P.eval gamma = 0) :
    (X - C gamma) *
        ((finiteModelRootCauchyCoordinate P gamma hP :
          finiteModelSpace P) : ℂ[X]) = P := by
  change (X - C gamma) * (P / (X - C gamma)) = P
  exact Polynomial.IsRoot.mul_div_eq hgamma

/-- On the real boundary, the root quotient is literally the unnormalized
Cauchy kernel. -/
theorem finiteModelBoundaryValue_rootCauchyCoordinate
    {P : ℂ[X]} (hP : P ≠ 0)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    {w : ℂ} (hw : 0 < w.im)
    (hroot : P.eval (starRingEnd ℂ w) = 0) (x : ℝ) :
    finiteModelBoundaryValue P
        (finiteModelRootCauchyCoordinate P (starRingEnd ℂ w) hP) x =
      upperCauchyBoundaryValue w x := by
  have hrec := congrArg (Polynomial.eval (x : ℂ))
    (X_sub_C_mul_finiteModelRootCauchyCoordinate hP hroot)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hrec
  have hden := upperCauchyDenominator_eval_real_ne_zero hw x
  unfold finiteModelBoundaryValue finiteModelValue upperCauchyBoundaryValue
  change
    (P / (X - C (starRingEnd ℂ w))).eval (x : ℂ) /
        P.eval (x : ℂ) =
      ((x : ℂ) - starRingEnd ℂ w)⁻¹
  field_simp [hreal x, hden]
  have hden' : (x : ℂ) - starRingEnd ℂ w ≠ 0 := by
    simpa using hden
  apply (eq_div_iff hden').2
  simpa [finiteModelRootCauchyCoordinate, mul_comm] using hrec

/-- `L²` equality between the denominator-quotient coordinate and its
Cauchy boundary vector. -/
theorem finiteModelBoundaryLp_rootCauchyCoordinate
    {P : ℂ[X]} (hP : P ≠ 0)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    {w : ℂ} (hw : 0 < w.im)
    (hroot : P.eval (starRingEnd ℂ w) = 0) :
    finiteModelBoundaryLpLinearMap P hreal
        (finiteModelRootCauchyCoordinate P (starRingEnd ℂ w) hP) =
      upperCauchyBoundaryLp w hw := by
  apply Lp.ext
  filter_upwards [
      finiteModelBoundaryLpLinearMap_ae P hreal
        (finiteModelRootCauchyCoordinate P (starRingEnd ℂ w) hP),
      upperCauchyBoundaryLp_ae w hw]
    with x hmodel hcauchy
  rw [hmodel, hcauchy]
  exact finiteModelBoundaryValue_rootCauchyCoordinate
    hP hreal hw hroot x

/-- A zero of the upper root factor becomes a conjugate zero of the negative
model denominator. -/
theorem conjugate_upperRootFactor_eval_conj_eq_zero
    (p : ℂ[X]) {w : ℂ} (hroot : (upperRootFactor p).eval w = 0) :
    (conjugatePolynomial (upperRootFactor p)).eval
        (starRingEnd ℂ w) = 0 := by
  simp [hroot]

/-- The actual negative-model Cauchy vector attached to an upper root. -/
def finiteNegativeCauchyVector
    (A : ℝ[X]) (tau : ℝ) (w : ℂ) (hw : 0 < w.im)
    (hroot : (upperRootFactor (finiteEPolynomial A tau)).eval w = 0) :
    finiteNegativeBoundarySubspace A tau :=
  ⟨upperCauchyBoundaryLp w hw, by
    refine ⟨finiteModelRootCauchyCoordinate
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))
      (starRingEnd ℂ w)
      (conjugatePolynomial_ne_zero
        (upperRootFactor_ne_zero (finiteEPolynomial A tau))), ?_⟩
    exact finiteModelBoundaryLp_rootCauchyCoordinate
      (conjugatePolynomial_ne_zero
        (upperRootFactor_ne_zero (finiteEPolynomial A tau)))
      (conjugate_upperRootFactor_eval_real_ne_zero
        (finiteEPolynomial A tau)) hw
      (conjugate_upperRootFactor_eval_conj_eq_zero
        (finiteEPolynomial A tau) hroot)⟩

@[simp] theorem finiteNegativeCauchyVector_coe
    (A : ℝ[X]) (tau : ℝ) (w : ℂ) (hw : 0 < w.im)
    (hroot : (upperRootFactor (finiteEPolynomial A tau)).eval w = 0) :
    (finiteNegativeCauchyVector A tau w hw hroot :
      Lp ℂ 2 (volume : Measure ℝ)) = upperCauchyBoundaryLp w hw :=
  rfl

/-- The boundary realization preserves the exact dimension of the negative
algebraic model. -/
@[simp] theorem finiteNegativeBoundarySubspace_finrank
    (A : ℝ[X]) (tau : ℝ) :
    Module.finrank ℂ (finiteNegativeBoundarySubspace A tau) =
      (upperRootFactor (finiteEPolynomial A tau)).natDegree := by
  change Module.finrank ℂ
      (LinearMap.range (finiteNegativeModelBoundaryLpLinearMap A tau)) = _
  rw [LinearMap.finrank_range_of_inj
      (finiteNegativeModelBoundaryLpLinearMap_injective A tau),
    finiteModelSpace_finrank, conjugatePolynomial_natDegree]

/-- The ordered pair of actual negative-model Cauchy vectors. -/
def twoFiniteNegativeCauchyVectors
    (A : ℝ[X]) (tau : ℝ) (w₀ w₁ : ℂ)
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0) :
    Fin 2 → finiteNegativeBoundarySubspace A tau :=
  ![finiteNegativeCauchyVector A tau w₀ hw₀ hroot₀,
    finiteNegativeCauchyVector A tau w₁ hw₁ hroot₁]

/-- Distinct upper nodes give a linearly independent pair inside the actual
negative boundary model. -/
theorem twoFiniteNegativeCauchyVectors_linearIndependent
    (A : ℝ[X]) (tau : ℝ) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁) :
    LinearIndependent ℂ
      (twoFiniteNegativeCauchyVectors A tau w₀ w₁ hw₀ hw₁
        hroot₀ hroot₁) := by
  change LinearIndependent ℂ
    ![finiteNegativeCauchyVector A tau w₀ hw₀ hroot₀,
      finiteNegativeCauchyVector A tau w₁ hw₁ hroot₁]
  have hfirst :
      finiteNegativeCauchyVector A tau w₀ hw₀ hroot₀ ≠ 0 := by
    intro hzero
    have hzeroAmbient := congrArg Subtype.val hzero
    exact upperCauchyBoundaryLp_ne_smul_of_ne hw₁ hw₀ hne.symm 0
      (by simpa using hzeroAmbient)
  rw [LinearIndependent.pair_iff' hfirst]
  intro c hsmul
  have hsmulAmbient := congrArg Subtype.val hsmul
  exact upperCauchyBoundaryLp_ne_smul_of_ne hw₀ hw₁ hne c
    (by simpa using hsmulAmbient.symm)

/-- In the degree-two case, the two distinct root Cauchy vectors form a
basis of the entire actual negative model. -/
noncomputable def finiteNegativeCauchyBasis
    (A : ℝ[X]) (tau : ℝ) (w₀ w₁ : ℂ)
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A tau)).natDegree = 2) :
    Module.Basis (Fin 2) ℂ (finiteNegativeBoundarySubspace A tau) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (twoFiniteNegativeCauchyVectors A tau w₀ w₁ hw₀ hw₁
      hroot₀ hroot₁)
    (twoFiniteNegativeCauchyVectors_linearIndependent A tau hw₀ hw₁
      hroot₀ hroot₁ hne)
    (by simpa using hdegree.symm)

@[simp] theorem finiteNegativeCauchyBasis_apply
    (A : ℝ[X]) (tau : ℝ) (w₀ w₁ : ℂ)
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A tau)).natDegree = 2) (i : Fin 2) :
    finiteNegativeCauchyBasis A tau w₀ w₁ hw₀ hw₁ hroot₀ hroot₁
        hne hdegree i =
      twoFiniteNegativeCauchyVectors A tau w₀ w₁ hw₀ hw₁
        hroot₀ hroot₁ i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank'
      (twoFiniteNegativeCauchyVectors A tau w₀ w₁ hw₀ hw₁
        hroot₀ hroot₁)
      (twoFiniteNegativeCauchyVectors_linearIndependent A tau hw₀ hw₁
        hroot₀ hroot₁ hne)
      (by simpa using hdegree.symm)) i

/-- On a root Cauchy basis vector, the abstract residual map is the concrete
Cauchy projection residual used in the two-node Gram calculation. -/
theorem finiteHardyCrossAngleResidual_finiteNegativeCauchyVector
    (A : ℝ[X]) (tau : ℝ) {w : ℂ} (hw : 0 < w.im)
    (hroot : (upperRootFactor (finiteEPolynomial A tau)).eval w = 0) :
    finiteHardyCrossAngleResidual A tau
        (finiteNegativeCauchyVector A tau w hw hroot) =
      finiteHardyCauchyProjectionResidual
        (finiteEPolynomial A tau) w hw := by
  rfl

/-- Coprimality of the two finite-model denominators discharges the
reflected-node nonvanishing hypothesis required by the projection formula. -/
theorem lowerRootFactor_eval_conj_ne_zero_of_upperRoot
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {w : ℂ}
    (hroot : (upperRootFactor (finiteEPolynomial A tau)).eval w = 0) :
    (lowerRootFactor (finiteEPolynomial A tau)).eval
        (starRingEnd ℂ w) ≠ 0 := by
  have hpoint :=
    (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))
      (lowerRootFactor (finiteEPolynomial A tau))).mp
      (finiteModelDenominators_isCoprime hA htau) (starRingEnd ℂ w)
  simp only [aeval_def] at hpoint
  rcases hpoint with hD | hL
  · exact False.elim (hD
      (conjugate_upperRootFactor_eval_conj_eq_zero
        (finiteEPolynomial A tau) hroot))
  · exact hL

/-- The reverse Gram matrix of the root Cauchy basis is the concrete
two-node Cauchy Gram matrix. -/
theorem basisReverseGram_finiteNegativeCauchyBasis
    (A : ℝ[X]) (tau : ℝ) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A tau)).natDegree = 2) :
    basisReverseGram
        (finiteNegativeCauchyBasis A tau w₀ w₁ hw₀ hw₁
          hroot₀ hroot₁ hne hdegree) =
      twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisReverseGram, twoUpperCauchyGramMatrix,
      twoFiniteNegativeCauchyVectors]

/-- The residual Gram matrix in the root Cauchy basis is the concrete
two-node projection-residual matrix. -/
theorem basisMapReverseGram_finiteNegativeCauchyBasis
    (A : ℝ[X]) (tau : ℝ) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A tau)).natDegree = 2) :
    basisMapReverseGram
        (finiteNegativeCauchyBasis A tau w₀ w₁ hw₀ hw₁
          hroot₀ hroot₁ hne hdegree)
        (finiteHardyCrossAngleResidual A tau) =
      twoFiniteHardyResidualGramMatrix
        (finiteEPolynomial A tau) w₀ w₁ hw₀ hw₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-finiteHardyCrossAngleResidual_apply, basisMapReverseGram,
      twoFiniteHardyResidualGramMatrix, twoFiniteNegativeCauchyVectors,
      finiteHardyCrossAngleResidual_finiteNegativeCauchyVector]

/-- Degree-two root specialization of the basis-independent metric
determinant.  This is the concrete finite Hardy identity

`det (I - C† C) = |S(w₀) S(w₁)|²`

for the actual cross angle and actual Blaschke-root Cauchy basis, with no
assumption about distinct singular values or generalized metric modes. -/
theorem finiteHardyCrossAngleComplementGramOperator_det_eq_rootValues
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {w₀ w₁ : ℂ} (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A tau)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A tau)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A tau)).natDegree = 2) :
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
      (Complex.normSq
        (lowerRootInnerValue (finiteEPolynomial A tau) w₀ *
          lowerRootInnerValue (finiteEPolynomial A tau) w₁) : ℂ) := by
  let b := finiteNegativeCauchyBasis A tau w₀ w₁ hw₀ hw₁
    hroot₀ hroot₁ hne hdegree
  have hconj₀ :
      (lowerRootFactor (finiteEPolynomial A tau)).eval
          (starRingEnd ℂ w₀) ≠ 0 :=
    lowerRootFactor_eval_conj_ne_zero_of_upperRoot hA htau hroot₀
  have hconj₁ :
      (lowerRootFactor (finiteEPolynomial A tau)).eval
          (starRingEnd ℂ w₁) ≠ 0 :=
    lowerRootFactor_eval_conj_ne_zero_of_upperRoot hA htau hroot₁
  calc
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
        Matrix.det
            (basisMapReverseGram b
              (finiteHardyCrossAngleResidual A tau)) /
          Matrix.det (basisReverseGram b) :=
      finiteHardyCrossAngleComplementGramOperator_det_eq_basisResidual_ratio
        A tau b
    _ = Matrix.det
          (twoFiniteHardyResidualGramMatrix
            (finiteEPolynomial A tau) w₀ w₁ hw₀ hw₁) /
        Matrix.det (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) := by
      rw [show b = finiteNegativeCauchyBasis A tau w₀ w₁ hw₀ hw₁
          hroot₀ hroot₁ hne hdegree from rfl,
        basisMapReverseGram_finiteNegativeCauchyBasis,
        basisReverseGram_finiteNegativeCauchyBasis]
    _ = (Complex.normSq
          (lowerRootInnerValue (finiteEPolynomial A tau) w₀ *
            lowerRootInnerValue (finiteEPolynomial A tau) w₁) : ℂ) :=
      twoFiniteHardyResidualGramMatrix_det_ratio_of_ne
        (finiteEPolynomial A tau) hw₀ hw₁ hne hconj₀ hconj₁

end

end RiemannGaussian
