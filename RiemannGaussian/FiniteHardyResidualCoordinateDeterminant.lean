import RiemannGaussian.FiniteHardySylvesterProjection
import RiemannGaussian.FiniteHardyConfluentBasis
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant of the finite Hardy residual coordinate

This file computes the determinant of the exact Sylvester residual-coordinate
endomorphism constructed in `FiniteHardySylvesterProjection`.  A comparison
between two Sylvester maps is lower triangular, so its determinant is the
residual-coordinate determinant.  The Sylvester determinant formula then
identifies that determinant with a quotient of resultants and, finally, with
a root product.

Polynomial roots are retained as multisets throughout.  Consequently the
final formula counts repeated roots with their full algebraic multiplicity and
does not assume separability.
-/

open MeasureTheory Polynomial

namespace RiemannGaussian

noncomputable section

/-- A block lower-triangular endomorphism with identity lower-right block has
the determinant of its upper-left endomorphism. -/
theorem det_prod_lowerTriangular
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (T : M →ₗ[R] M) (Q : M →ₗ[R] N) :
    LinearMap.det
        ((T.comp (LinearMap.fst R M N)).prod
          (Q.comp (LinearMap.fst R M N) + LinearMap.snd R M N)) =
      LinearMap.det T := by
  classical
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  let b := bM.prod bN
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bM]
  have hmatrix :
      LinearMap.toMatrix b b
          ((T.comp (LinearMap.fst R M N)).prod
            (Q.comp (LinearMap.fst R M N) + LinearMap.snd R M N)) =
        Matrix.fromBlocks
          (LinearMap.toMatrix bM bM T) 0
          (LinearMap.toMatrix bM bN Q) 1 := by
    ext (i | i) (j | j) <;>
      simp [b, bM, bN, LinearMap.toMatrix_apply,
        Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

/-- The second Sylvester coordinate in the exact projection decomposition. -/
noncomputable def finiteNegativeReflectedProjectionCoordinateLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      finiteModelSpace
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))) :=
  (LinearMap.snd ℂ _ _).comp
    (finiteNegativeSylvesterCoordinatePairLinearMap A tau)

/-- Comparison endomorphism obtained by following the Sylvester map for the
lower root factor by the inverse Sylvester map for its conjugate. -/
noncomputable def finiteNegativeSylvesterComparisonLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    (finiteNegativeModelSpace A tau ×
        finiteModelSpace
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)))) →ₗ[ℂ]
      (finiteNegativeModelSpace A tau ×
        finiteModelSpace
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)))) :=
  (finiteModelSylvesterLinearEquiv A tau).symm.toLinearMap.comp
    (Polynomial.sylvesterMap
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau)))
      (lowerRootFactor (finiteEPolynomial A tau))
      (m := (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree)
      (n := (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau))).natDegree)
      le_rfl (by simp))

/-- Evaluation formula for the reflected projection coordinate. -/
@[simp] theorem finiteNegativeReflectedProjectionCoordinateLinearMap_apply
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    finiteNegativeReflectedProjectionCoordinateLinearMap A tau q =
      ((finiteModelSylvesterLinearEquiv A tau).symm
        (finiteNegativeCommonNumeratorLinearMap A tau q)).2 := by
  rfl

/-- The Sylvester comparison map is lower triangular: its diagonal blocks are
the residual-coordinate endomorphism and the identity. -/
theorem finiteNegativeSylvesterComparisonLinearMap_apply
    (A : ℝ[X]) (tau : ℝ)
    (q : finiteNegativeModelSpace A tau)
    (r : finiteModelSpace
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau)))) :
    finiteNegativeSylvesterComparisonLinearMap A tau (q, r) =
      (finiteNegativeResidualCoordinateLinearMap A tau q,
        finiteNegativeReflectedProjectionCoordinateLinearMap A tau q + r) := by
  change (finiteModelSylvesterLinearEquiv A tau).symm
      ((Polynomial.sylvesterMap
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (lowerRootFactor (finiteEPolynomial A tau))
        (m := (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree)
        (n := (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))).natDegree)
        le_rfl (by simp)) (q, r)) = _
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [finiteModelSylvesterLinearEquiv_apply_coe]
  change
    conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)) * (r : ℂ[X]) +
        lowerRootFactor (finiteEPolynomial A tau) * (q : ℂ[X]) =
      conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)) *
          ((finiteNegativeReflectedProjectionCoordinateLinearMap
              A tau q : ℂ[X]) + (r : ℂ[X])) +
        conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau)) *
          (finiteNegativeResidualCoordinateLinearMap A tau q : ℂ[X])
  have hdecomp := finiteNegativeCommonNumerator_decomposition A tau q
  rw [finiteNegativeResidualCoordinateLinearMap_apply,
    finiteNegativeReflectedProjectionCoordinateLinearMap_apply]
  linear_combination -hdecomp

/-- Operator form of the lower-triangular Sylvester comparison law. -/
theorem finiteNegativeSylvesterComparisonLinearMap_eq_lowerTriangular
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeSylvesterComparisonLinearMap A tau =
      ((finiteNegativeResidualCoordinateLinearMap A tau).comp
          (LinearMap.fst ℂ _ _)).prod
        ((finiteNegativeReflectedProjectionCoordinateLinearMap A tau).comp
            (LinearMap.fst ℂ _ _) +
          LinearMap.snd ℂ _ _) := by
  apply LinearMap.ext
  rintro ⟨q, r⟩
  exact finiteNegativeSylvesterComparisonLinearMap_apply A tau q r

/-- The Sylvester comparison determinant is exactly the determinant of the
residual-coordinate endomorphism. -/
theorem finiteNegativeSylvesterComparisonLinearMap_det
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det (finiteNegativeSylvesterComparisonLinearMap A tau) =
      LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) := by
  rw [finiteNegativeSylvesterComparisonLinearMap_eq_lowerTriangular]
  exact det_prod_lowerTriangular _ _

/-- Cross-multiplication form of the residual-coordinate resultant formula. -/
theorem finiteNegative_resultant_mul_residualCoordinate_det
    (A : ℝ[X]) (tau : ℝ) :
    Polynomial.resultant
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau))) *
        LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) =
      Polynomial.resultant
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (lowerRootFactor (finiteEPolynomial A tau)) := by
  let D := conjugatePolynomial
    (upperRootFactor (finiteEPolynomial A tau))
  let V := conjugatePolynomial
    (lowerRootFactor (finiteEPolynomial A tau))
  let L := lowerRootFactor (finiteEPolynomial A tau)
  let bDom := ((Polynomial.degreeLT.basis ℂ D.natDegree).prod
    (Polynomial.degreeLT.basis ℂ V.natDegree)).reindex
      finSumFinEquiv
  let bCod := Polynomial.degreeLT.basis ℂ (D.natDegree + V.natDegree)
  let Sg := Polynomial.sylvesterMap D V
    (m := D.natDegree) (n := V.natDegree) le_rfl le_rfl
  let Sh := Polynomial.sylvesterMap D L
    (m := D.natDegree) (n := V.natDegree) le_rfl (by simp [L, V])
  let F :
      (Polynomial.degreeLT ℂ D.natDegree ×
          Polynomial.degreeLT ℂ V.natDegree) →ₗ[ℂ]
        (Polynomial.degreeLT ℂ D.natDegree ×
          Polynomial.degreeLT ℂ V.natDegree) :=
    finiteNegativeSylvesterComparisonLinearMap A tau
  have hcomp : Sg.comp F = Sh := by
    apply LinearMap.ext
    intro x
    change (finiteModelSylvesterLinearEquiv A tau)
        ((finiteModelSylvesterLinearEquiv A tau).symm (Sh x)) = Sh x
    exact (finiteModelSylvesterLinearEquiv A tau).apply_symm_apply (Sh x)
  have hmatrix :
      LinearMap.toMatrix bDom bCod Sg *
          LinearMap.toMatrix bDom bDom F =
        LinearMap.toMatrix bDom bCod Sh := by
    rw [← LinearMap.toMatrix_comp]
    exact congrArg (LinearMap.toMatrix bDom bCod) hcomp
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul] at hdet
  rw [show LinearMap.toMatrix bDom bCod Sg =
      Polynomial.sylvester D V D.natDegree V.natDegree by
        simpa [bDom, bCod, Sg] using
          Polynomial.toMatrix_sylvesterMap' D V le_rfl le_rfl,
    show LinearMap.toMatrix bDom bCod Sh =
      Polynomial.sylvester D L D.natDegree V.natDegree by
        simpa [bDom, bCod, Sh] using
          Polynomial.toMatrix_sylvesterMap' D L le_rfl
            (by simp [L, V]),
    LinearMap.det_toMatrix] at hdet
  have hFdet : LinearMap.det F =
      LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) := by
    change LinearMap.det
        (finiteNegativeSylvesterComparisonLinearMap A tau) = _
    exact finiteNegativeSylvesterComparisonLinearMap_det A tau
  rw [hFdet] at hdet
  have hVL : V.natDegree = L.natDegree := by simp [V, L]
  conv_rhs at hdet => rw [hVL]
  simpa [D, V, L, F, Polynomial.resultant] using hdet

/-- The residual-coordinate determinant is a quotient of two resultants. -/
theorem finiteNegativeResidualCoordinateLinearMap_det_eq_resultant_div
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) =
      Polynomial.resultant
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))
          (lowerRootFactor (finiteEPolynomial A tau)) /
        Polynomial.resultant
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau))) := by
  have hnonzero :
      Polynomial.resultant
          (conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)))
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau))) ≠ 0 :=
    Polynomial.resultant_ne_zero _ _
      (conjugate_rootFactors_isCoprime (finiteEPolynomial A tau))
  apply (eq_div_iff hnonzero).2
  simpa [mul_comm] using
    finiteNegative_resultant_mul_residualCoordinate_det A tau

/-- The residual-coordinate determinant is the quotient of lower-factor
values over all reflected upper roots, counted with multiplicity. -/
theorem finiteNegativeResidualCoordinateLinearMap_det_eq_rootProduct
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) =
      ((conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).roots.map
        fun a ↦
          (lowerRootFactor (finiteEPolynomial A tau)).eval a /
            (conjugatePolynomial
              (lowerRootFactor (finiteEPolynomial A tau))).eval a).prod := by
  let D := conjugatePolynomial
    (upperRootFactor (finiteEPolynomial A tau))
  let L := lowerRootFactor (finiteEPolynomial A tau)
  let V := conjugatePolynomial
    (lowerRootFactor (finiteEPolynomial A tau))
  have hDmonic : D.Monic :=
    conjugatePolynomial_monic_of_monic
      (upperRootFactor_monic (finiteEPolynomial A tau))
  have hDL : Polynomial.resultant D L =
      (D.roots.map L.eval).prod := by
    simpa [hDmonic.leadingCoeff] using
      Polynomial.resultant_eq_prod_eval D L L.natDegree le_rfl
        (IsAlgClosed.splits D)
  have hDV : Polynomial.resultant D V =
      (D.roots.map V.eval).prod := by
    simpa [hDmonic.leadingCoeff] using
      Polynomial.resultant_eq_prod_eval D V V.natDegree le_rfl
        (IsAlgClosed.splits D)
  rw [finiteNegativeResidualCoordinateLinearMap_det_eq_resultant_div,
    show Polynomial.resultant
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (lowerRootFactor (finiteEPolynomial A tau)) =
          (D.roots.map L.eval).prod by simpa [D, L] using hDL,
    show Polynomial.resultant
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau)))
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))) =
          (D.roots.map V.eval).prod by simpa [D, V] using hDV,
    ← Multiset.prod_map_div]

/-- A reflected lower-factor evaluation quotient is the conjugate of the
corresponding lower-root inner value. -/
theorem lowerRootFactor_eval_conj_div_conjugateLower_eq_star_inner
    (p : ℂ[X]) (w : ℂ) :
    (lowerRootFactor p).eval (starRingEnd ℂ w) /
        (conjugatePolynomial (lowerRootFactor p)).eval
          (starRingEnd ℂ w) =
      starRingEnd ℂ (lowerRootInnerValue p w) := by
  rw [star_lowerRootInnerValue_eq_inv_conj]
  simp [lowerRootInnerValue]

/-- The residual-coordinate determinant is the product of conjugated
lower-root inner values over the upper roots, with multiplicity. -/
theorem finiteNegativeResidualCoordinateLinearMap_det_eq_innerRootProduct
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) =
      ((upperRootFactor (finiteEPolynomial A tau)).roots.map
        fun w ↦ starRingEnd ℂ
          (lowerRootInnerValue (finiteEPolynomial A tau) w)).prod := by
  rw [finiteNegativeResidualCoordinateLinearMap_det_eq_rootProduct,
    conjugatePolynomial_roots, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro w hw
  exact lowerRootFactor_eval_conj_div_conjugateLower_eq_star_inner
    (finiteEPolynomial A tau) w

end

end RiemannGaussian
