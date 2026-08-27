import RiemannGaussian.FiniteHardyResidualCoordinateDeterminant
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Multiplicity-aware finite Hardy determinant

This file transports the algebraic residual-coordinate determinant to the
actual boundary Hardy model.  The algebraic model and its boundary range are
linearly equivalent.  Under that equivalence, the genuine orthogonal
projection residual factors as the residual-coordinate endomorphism followed
by multiplication by the residual inner function, which is an isometry.

Mathlib's norm-determinant identity then identifies the determinant of the
actual Hardy complement Gram operator with the squared norm of the algebraic
determinant.  Substitution of the multiset root formula gives the final
unconditional confluent determinant, including repeated upper roots with
their full algebraic multiplicity.
-/

open MeasureTheory Polynomial

namespace RiemannGaussian

noncomputable section

/-- The injective boundary realization identifies the algebraic negative
model with its actual boundary `L²` range. -/
noncomputable def finiteNegativeModelBoundaryLinearEquiv
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeModelSpace A tau ≃ₗ[ℂ]
      finiteNegativeBoundarySubspace A tau :=
  LinearEquiv.ofInjective (finiteNegativeModelBoundaryLpLinearMap A tau)
    (finiteNegativeModelBoundaryLpLinearMap_injective A tau)

/-- The algebraic residual-coordinate endomorphism transported to the actual
negative boundary subspace. -/
noncomputable def finiteNegativeBoundaryResidualCoordinateLinearMap
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeBoundarySubspace A tau →ₗ[ℂ]
      finiteNegativeBoundarySubspace A tau :=
  (finiteNegativeModelBoundaryLinearEquiv A tau).toLinearMap.comp
    ((finiteNegativeResidualCoordinateLinearMap A tau).comp
      (finiteNegativeModelBoundaryLinearEquiv A tau).symm.toLinearMap)

/-- Inclusion of the negative boundary subspace followed by multiplication by
the lower-root inner function is a linear isometry into boundary `L²`. -/
noncomputable def finiteResidualInnerNegativeBoundaryLinearIsometry
    (A : ℝ[X]) (tau : ℝ) :
    finiteNegativeBoundarySubspace A tau →ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  (lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)).comp
    (finiteNegativeBoundarySubspace A tau).subtypeₗᵢ

/-- Transport to the boundary subspace preserves the residual-coordinate
determinant. -/
theorem finiteNegativeBoundaryResidualCoordinateLinearMap_det
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det
        (finiteNegativeBoundaryResidualCoordinateLinearMap A tau) =
      LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau) := by
  exact LinearMap.det_conj
    (finiteNegativeResidualCoordinateLinearMap A tau)
    (finiteNegativeModelBoundaryLinearEquiv A tau)

/-- The genuine Hardy projection residual is the transported algebraic
residual coordinate followed by the residual-inner isometry. -/
theorem finiteHardyCrossAngleResidual_toLinearMap_eq_factorization
    (A : ℝ[X]) (tau : ℝ) :
    (finiteHardyCrossAngleResidual A tau).toLinearMap =
      (finiteResidualInnerNegativeBoundaryLinearIsometry A tau).toLinearMap.comp
        (finiteNegativeBoundaryResidualCoordinateLinearMap A tau) := by
  apply LinearMap.ext
  intro n
  let e := finiteNegativeModelBoundaryLinearEquiv A tau
  let q := e.symm n
  have hn : e q = n := e.apply_symm_apply n
  rw [← hn]
  change finiteHardyCrossAngleResidual A tau
      (⟨finiteNegativeModelBoundaryLpLinearMap A tau q, ⟨q, rfl⟩⟩ :
        finiteNegativeBoundarySubspace A tau) = _
  rw [finiteHardyCrossAngleResidual_rangeRestrict]
  change lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)
      (finiteNegativeModelBoundaryLpLinearMap A tau
        (finiteNegativeResidualCoordinateLinearMap A tau q)) =
    lowerRootInnerBoundaryLpLinearIsometry (finiteEPolynomial A tau)
      ((finiteNegativeBoundaryResidualCoordinateLinearMap A tau)
        (e q) : Lp ℂ 2 (volume : Measure ℝ))
  congr 1
  change finiteNegativeModelBoundaryLpLinearMap A tau
      (finiteNegativeResidualCoordinateLinearMap A tau q) =
    ((finiteNegativeModelBoundaryLinearEquiv A tau)
      ((finiteNegativeResidualCoordinateLinearMap A tau)
        ((finiteNegativeModelBoundaryLinearEquiv A tau).symm (e q))) :
      finiteNegativeBoundarySubspace A tau)
  rw [show e = finiteNegativeModelBoundaryLinearEquiv A tau by rfl,
    (finiteNegativeModelBoundaryLinearEquiv A tau).symm_apply_apply]
  rfl

/-- The norm determinant of the genuine Hardy residual equals the norm of the
algebraic residual-coordinate determinant. -/
theorem finiteHardyCrossAngleResidual_normDet
    (A : ℝ[X]) (tau : ℝ) :
    (finiteHardyCrossAngleResidual A tau).normDet =
      ‖LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau)‖ := by
  let T := finiteNegativeBoundaryResidualCoordinateLinearMap A tau
  let J := finiteResidualInnerNegativeBoundaryLinearIsometry A tau
  calc
    (finiteHardyCrossAngleResidual A tau).normDet =
        (J.toLinearMap.comp T).normDet := by
      rw [finiteHardyCrossAngleResidual_toLinearMap_eq_factorization]
    _ = J.toLinearMap.normDet * T.normDet := by
      exact LinearMap.normDet_comp_of_finrank_eq T J.toLinearMap rfl
    _ = T.normDet := by rw [LinearIsometry.normDet_eq_one, one_mul]
    _ = ‖LinearMap.det T‖ := LinearMap.normDet_eq_norm_det T
    _ = _ := by rw [finiteNegativeBoundaryResidualCoordinateLinearMap_det]

/-- The determinant of the actual Hardy complement Gram operator is the norm
square of the algebraic residual-coordinate determinant. -/
theorem finiteHardyCrossAngleComplementGramOperator_det_eq_residualCoordinateDet
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
      (Complex.normSq
        (LinearMap.det (finiteNegativeResidualCoordinateLinearMap A tau)) : ℂ) := by
  let : CompleteSpace (finiteNegativeBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  let : CompleteSpace (finitePositiveBoundarySubspace A tau) :=
    FiniteDimensional.complete ℂ _
  rw [finiteHardyCrossAngleComplementGramOperator_eq_residual]
  change ContinuousLinearMap.det
      ((finiteHardyCrossAngleResidual A tau).adjoint.comp
        (finiteHardyCrossAngleResidual A tau)) = _
  rw [← (finiteHardyCrossAngleResidual A tau).normDet_sq]
  rw [finiteHardyCrossAngleResidual_normDet, Complex.sq_norm]
  rfl

/-- Unconditional multiplicity-aware finite Hardy determinant: the actual
complement Gram determinant is the squared modulus of the product of the
lower-root inner values over the complete upper-root multiset. -/
theorem finiteHardyCrossAngleComplementGramOperator_det_eq_confluentRootProduct
    (A : ℝ[X]) (tau : ℝ) :
    LinearMap.det
        (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap =
      (Complex.normSq
        ((upperRootFactor (finiteEPolynomial A tau)).roots.map
          fun w ↦ lowerRootInnerValue (finiteEPolynomial A tau) w).prod : ℂ) := by
  rw [finiteHardyCrossAngleComplementGramOperator_det_eq_residualCoordinateDet,
    finiteNegativeResidualCoordinateLinearMap_det_eq_innerRootProduct]
  let s := (upperRootFactor (finiteEPolynomial A tau)).roots.map
    fun w ↦ lowerRootInnerValue (finiteEPolynomial A tau) w
  have hstar :
      ((upperRootFactor (finiteEPolynomial A tau)).roots.map
        fun w ↦ starRingEnd ℂ
          (lowerRootInnerValue (finiteEPolynomial A tau) w)).prod =
        starRingEnd ℂ s.prod := by
    simpa only [s, Multiset.map_map, Function.comp_apply] using
      (map_multiset_prod (starRingEnd ℂ) s).symm
  rw [hstar, Complex.normSq_conj]

/-- The actual confluent complement Gram determinant has nonnegative real
value. -/
theorem finiteHardyCrossAngleComplementGramOperator_det_re_nonneg
    (A : ℝ[X]) (tau : ℝ) :
    0 ≤ (LinearMap.det
      (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap).re := by
  rw [finiteHardyCrossAngleComplementGramOperator_det_eq_confluentRootProduct]
  exact Complex.normSq_nonneg _

/-- Square-root form of the unconditional confluent determinant.  This is the
interface used by the finite hyperbolic and Pick bounds. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_eq_confluentRootProduct
    (A : ℝ[X]) (tau : ℝ) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap).re =
      ‖((upperRootFactor (finiteEPolynomial A tau)).roots.map
        fun w ↦ lowerRootInnerValue (finiteEPolynomial A tau) w).prod‖ := by
  rw [finiteHardyCrossAngleComplementGramOperator_det_eq_confluentRootProduct]
  rfl

/-- Any chosen upper root controls the complete Hardy determinant product.
All remaining residual-inner factors have norm at most one, including when
the chosen root or another root occurs with multiplicity. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_innerValue_of_mem
    (A : ℝ[X]) (tau : ℝ) {w : ℂ}
    (hw : w ∈ (upperRootFactor (finiteEPolynomial A tau)).roots) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap).re ≤
      ‖lowerRootInnerValue (finiteEPolynomial A tau) w‖ := by
  let p := finiteEPolynomial A tau
  obtain ⟨rest, hroots⟩ := Multiset.exists_cons_of_mem hw
  have hrest : ∀ z ∈ rest, 0 < z.im := by
    intro z hz
    have hzfull : z ∈ (upperRootFactor p).roots := by
      rw [hroots]
      simp [hz]
    rw [upperRootFactor_roots, Multiset.mem_filter] at hzfull
    exact hzfull.2
  have hnorm : ∀ s : Multiset ℂ,
      (∀ z ∈ s, 0 < z.im) →
        ‖(s.map fun z ↦ lowerRootInnerValue p z).prod‖ ≤ 1 := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons z s ih =>
        have hz : 0 < z.im := hs z (by simp)
        have hsTail : ∀ y ∈ s, 0 < y.im := by
          intro y hy
          exact hs y (by simp [hy])
        simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
        apply mul_le_one₀
        · exact norm_lowerRootInnerValue_le_one p hz
        · exact norm_nonneg _
        · exact ih hsTail
  have hrestNorm :
      ‖(rest.map fun z ↦ lowerRootInnerValue p z).prod‖ ≤ 1 :=
    hnorm rest hrest
  rw [finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_eq_confluentRootProduct]
  change ‖((upperRootFactor p).roots.map
    fun z ↦ lowerRootInnerValue p z).prod‖ ≤ _
  rw [hroots, Multiset.map_cons, Multiset.prod_cons, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hrestNorm

end

end RiemannGaussian
