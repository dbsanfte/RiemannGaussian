import RiemannGaussian.FiniteHardyMetricDeterminant
import RiemannGaussian.FiniteAlgebraicHilbert

/-!
# Sylvester coordinates for the finite Hardy projection

This file turns the exact polynomial Sylvester decomposition into the genuine
orthogonal-projection decomposition on boundary `L²(ℝ, ℂ)`.  The first
Sylvester coordinate is packaged as a linear endomorphism of the negative
finite model.  Lean proves that, after the negative boundary embedding and
multiplication by the residual inner function, it is exactly the residual of
orthogonally projecting onto the positive finite model.

The construction is unconditional and therefore remains valid when roots have
multiplicity.  Computing the determinant of this residual-coordinate
endomorphism is a separate algebraic step.
-/

open Filter MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

namespace RiemannGaussian

noncomputable section

/-- The two exact Sylvester coordinates of a negative-model numerator placed
over the common denominator. -/
noncomputable def finiteNegativeSylvesterCoordinatePairLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      (finiteNegativeModelSpace A tau ×
        finiteModelSpace
          (conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)))) :=
  (finiteModelSylvesterLinearEquiv A tau).symm.toLinearMap.comp
    (finiteNegativeCommonNumeratorLinearMap A tau)

/-- The negative-model coordinate of the residual after positive-model
projection. -/
noncomputable def finiteNegativeResidualCoordinateLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau →ₗ[ℂ]
      finiteNegativeModelSpace A tau :=
  (LinearMap.fst ℂ _ _).comp
    (finiteNegativeSylvesterCoordinatePairLinearMap A tau)

/-- Evaluation formula for the pair of Sylvester coordinates. -/
@[simp] theorem finiteNegativeSylvesterCoordinatePairLinearMap_apply
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    finiteNegativeSylvesterCoordinatePairLinearMap A tau q =
      (finiteModelSylvesterLinearEquiv A tau).symm
        (finiteNegativeCommonNumeratorLinearMap A tau q) := by
  rfl

/-- Evaluation formula for the residual Sylvester coordinate. -/
@[simp] theorem finiteNegativeResidualCoordinateLinearMap_apply
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    finiteNegativeResidualCoordinateLinearMap A tau q =
      ((finiteModelSylvesterLinearEquiv A tau).symm
        (finiteNegativeCommonNumeratorLinearMap A tau q)).1 := by
  rfl

/-- Every negative-model numerator has an exact decomposition into a positive
coordinate and the residual-inner multiple of its residual coordinate. -/
theorem finiteNegative_exists_projectionCoordinate_decomposition
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    ∃ qS : finitePositiveModelSpace A tau,
      conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) * (qS : ℂ[X]) +
        conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)) *
          (finiteNegativeResidualCoordinateLinearMap A tau q : ℂ[X]) =
        (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau) := by
  let pair := finiteNegativeSylvesterCoordinatePairLinearMap A tau q
  let qS : finitePositiveModelSpace A tau :=
    ⟨(pair.2 : ℂ[X]), by
      simpa [finitePositiveModelSpace, finiteModelSpace] using pair.2.property⟩
  refine ⟨qS, ?_⟩
  simpa [pair, qS] using finiteNegativeCommonNumerator_decomposition A tau q

/-- Pointwise rational form of the Sylvester decomposition on the real
boundary. -/
theorem finiteNegativeBoundaryValue_decomposition_of_coordinate
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau)
    (qS : finitePositiveModelSpace A tau)
    (hdecomp :
      conjugatePolynomial
            (upperRootFactor (finiteEPolynomial A tau)) * (qS : ℂ[X]) +
        conjugatePolynomial
            (lowerRootFactor (finiteEPolynomial A tau)) *
          (finiteNegativeResidualCoordinateLinearMap A tau q : ℂ[X]) =
        (q : ℂ[X]) * lowerRootFactor (finiteEPolynomial A tau))
    (x : ℝ) :
    finiteModelBoundaryValue
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))) q x =
      finiteModelBoundaryValue
          (lowerRootFactor (finiteEPolynomial A tau)) qS x +
        lowerRootInnerBoundaryValue (finiteEPolynomial A tau) x *
          finiteModelBoundaryValue
            (conjugatePolynomial
              (upperRootFactor (finiteEPolynomial A tau)))
            (finiteNegativeResidualCoordinateLinearMap A tau q) x := by
  let p := finiteEPolynomial A tau
  have hL := lowerRootFactor_eval_real_ne_zero p x
  have hD := conjugate_upperRootFactor_eval_real_ne_zero p x
  have hDstar :
      starRingEnd ℂ ((upperRootFactor p).eval (x : ℂ)) ≠ 0 := by
    simpa only [conjugatePolynomial_eval_real] using hD
  have heval := congrArg (Polynomial.eval (x : ℂ)) hdecomp
  simp only [eval_add, eval_mul] at heval
  dsimp only [p] at hL hD hDstar
  unfold finiteModelBoundaryValue finiteModelValue
    lowerRootInnerBoundaryValue lowerRootInnerValue
  field_simp [hL, hD, hDstar]
  simpa [p, mul_comm, mul_left_comm, mul_assoc] using heval.symm

/-- The polynomial Sylvester identity lifts to an exact equality of genuine
boundary `L²` vectors. -/
theorem finiteNegativeModelBoundaryLp_decomposition
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    ∃ qS : finitePositiveModelSpace A tau,
      finiteNegativeModelBoundaryLpLinearMap A tau q =
        finitePositiveModelBoundaryLpLinearMap A tau qS +
          lowerRootInnerBoundaryLpLinearIsometry
            (finiteEPolynomial A tau)
            (finiteNegativeModelBoundaryLpLinearMap A tau
              (finiteNegativeResidualCoordinateLinearMap A tau q)) := by
  obtain ⟨qS, hdecomp⟩ :=
    finiteNegative_exists_projectionCoordinate_decomposition A tau q
  refine ⟨qS, ?_⟩
  let p := finiteEPolynomial A tau
  let D := conjugatePolynomial (upperRootFactor p)
  let negativeVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finiteNegativeModelBoundaryLpLinearMap A tau q
  let positiveVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finitePositiveModelBoundaryLpLinearMap A tau qS
  let residualVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finiteNegativeModelBoundaryLpLinearMap A tau
      (finiteNegativeResidualCoordinateLinearMap A tau q)
  let shiftedVector : Lp ℂ 2 (volume : Measure ℝ) :=
    lowerRootInnerBoundaryLpLinearIsometry p residualVector
  have hnegativeAe : negativeVector =ᵐ[volume]
      finiteModelBoundaryValue D q := by
    exact finiteModelBoundaryLpLinearMap_ae D
      (conjugate_upperRootFactor_eval_real_ne_zero p) q
  have hpositiveAe : positiveVector =ᵐ[volume]
      finiteModelBoundaryValue (lowerRootFactor p) qS := by
    exact finiteModelBoundaryLpLinearMap_ae (lowerRootFactor p)
      (lowerRootFactor_eval_real_ne_zero p) qS
  have hresidualAe : residualVector =ᵐ[volume]
      finiteModelBoundaryValue D
        (finiteNegativeResidualCoordinateLinearMap A tau q) := by
    exact finiteModelBoundaryLpLinearMap_ae D
      (conjugate_upperRootFactor_eval_real_ne_zero p)
      (finiteNegativeResidualCoordinateLinearMap A tau q)
  have hshiftedAe : shiftedVector =ᵐ[volume]
      fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * residualVector x := by
    simpa [shiftedVector] using
      lowerRootInnerBoundaryLpLinearMap_ae p residualVector
  change negativeVector = positiveVector + shiftedVector
  apply Lp.ext
  filter_upwards [hnegativeAe, hpositiveAe, hresidualAe, hshiftedAe,
      Lp.coeFn_add positiveVector shiftedVector]
    with x hnegative hpositive hresidual hshifted hadd
  rw [hnegative, hadd]
  simp only [Pi.add_apply]
  rw [hpositive, hshifted, hresidual]
  exact finiteNegativeBoundaryValue_decomposition_of_coordinate
    A tau q qS hdecomp x

/-- The Sylvester residual coordinate is the exact residual of orthogonally
projecting the negative boundary vector onto the positive finite model. -/
theorem finiteNegativeModelBoundaryLp_sub_starProjection
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    finiteNegativeModelBoundaryLpLinearMap A tau q -
        (finitePositiveBoundarySubspace A tau).starProjection
          (finiteNegativeModelBoundaryLpLinearMap A tau q) =
      lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)
        (finiteNegativeModelBoundaryLpLinearMap A tau
          (finiteNegativeResidualCoordinateLinearMap A tau q)) := by
  obtain ⟨qS, hboundary⟩ :=
    finiteNegativeModelBoundaryLp_decomposition A tau q
  have horth :
      lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)
          (finiteNegativeModelBoundaryLpLinearMap A tau
            (finiteNegativeResidualCoordinateLinearMap A tau q)) ∈
        (finitePositiveBoundarySubspace A tau)ᗮ := by
    simpa [finitePositiveBoundarySubspace,
      finitePositiveModelBoundaryLpLinearMap,
      finiteNegativeModelBoundaryLpLinearMap] using
      residualInner_negative_mem_finiteModelBoundary_orthogonal
        (finiteEPolynomial A tau)
        (finiteNegativeResidualCoordinateLinearMap A tau q)
  have hprojection :
      (finitePositiveBoundarySubspace A tau).starProjection
          (finiteNegativeModelBoundaryLpLinearMap A tau q) =
        finitePositiveModelBoundaryLpLinearMap A tau qS := by
    apply Submodule.eq_starProjection_of_mem_orthogonal'
    · exact ⟨qS, rfl⟩
    · exact horth
    · exact hboundary
  rw [hprojection]
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hboundary

/-- Operator form of the exact residual factorization on every algebraic
negative-model coordinate. -/
theorem finiteHardyCrossAngleResidual_rangeRestrict
    (A : ℝ[X]) (tau : ℝ) (q : finiteNegativeModelSpace A tau) :
    finiteHardyCrossAngleResidual A tau
        (⟨finiteNegativeModelBoundaryLpLinearMap A tau q, ⟨q, rfl⟩⟩ :
          finiteNegativeBoundarySubspace A tau) =
      lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)
        (finiteNegativeModelBoundaryLpLinearMap A tau
          (finiteNegativeResidualCoordinateLinearMap A tau q)) := by
  rw [finiteHardyCrossAngleResidual_apply]
  change
    finiteNegativeModelBoundaryLpLinearMap A tau q -
        (finitePositiveBoundarySubspace A tau).starProjection
          (finiteNegativeModelBoundaryLpLinearMap A tau q) = _
  exact finiteNegativeModelBoundaryLp_sub_starProjection A tau q

end

end RiemannGaussian
