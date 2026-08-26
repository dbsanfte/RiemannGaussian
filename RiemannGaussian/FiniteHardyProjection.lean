import RiemannGaussian.FiniteHardyOrthogonality

/-!
# Finite Hardy Cauchy-kernel projection

For the finite residual inner function `S`, this file constructs the exact
finite-model component of an upper-half-plane Cauchy kernel `k_w`.  It proves
the genuine boundary-space orthogonal decomposition

`k_w = k_w^S + conj (S w) • S k_w`

whenever the reflected node is not a zero of the residual denominator.  In
particular, the second term is exactly the residual after orthogonal
projection onto the finite model space.  The final theorem records the full
weighted inner-product identity for two such residuals.
-/

open Filter MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

namespace RiemannGaussian

noncomputable section

/-- Reflection changes the residual inner value into the inverse conjugate
value.  This identity is exact even at zero because inversion is taken in a
field with zero. -/
theorem star_lowerRootInnerValue_eq_inv_conj
    (p : ℂ[X]) (w : ℂ) :
    starRingEnd ℂ (lowerRootInnerValue p w) =
      (lowerRootInnerValue p (starRingEnd ℂ w))⁻¹ := by
  simp [lowerRootInnerValue]

/-- The numerator coordinate of the model component
`k_w - conj (S w) • S k_w`. -/
def finiteModelCauchyProjectionCoordinate
    (p : ℂ[X]) (w : ℂ) : finiteModelSpace (lowerRootFactor p) :=
  -(starRingEnd ℂ (lowerRootInnerValue p w)) •
    finiteInnerDifferenceCoordinate
      (conjugatePolynomial (lowerRootFactor p))
      (lowerRootFactor p) (starRingEnd ℂ w) (by simp)

/-- Pointwise rational identity for the model component throughout the
closed upper half-plane. -/
theorem finiteModelValue_cauchyProjectionCoordinate
    (p : ℂ[X]) {w z : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0)
    (hz : 0 ≤ z.im) :
    finiteModelValue (lowerRootFactor p)
        (finiteModelCauchyProjectionCoordinate p w) z =
      (z - starRingEnd ℂ w)⁻¹ -
        starRingEnd ℂ (lowerRootInnerValue p w) *
          (lowerRootInnerValue p z *
            (z - starRingEnd ℂ w)⁻¹) := by
  have hPz : (lowerRootFactor p).eval z ≠ 0 := by
    by_cases hz0 : z.im = 0
    · have hzReal : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [hz0]
      simpa [hzReal] using lowerRootFactor_eval_real_ne_zero p z.re
    · exact lowerRootFactor_eval_ne_zero_of_im_pos p
        (lt_of_le_of_ne hz (Ne.symm hz0))
  have hzw : z ≠ starRingEnd ℂ w := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [finiteModelCauchyProjectionCoordinate, finiteModelValue_smul]
  rw [finiteModelValue_innerDifferenceCoordinate (by simp) hconj hPz hzw]
  change
    -(starRingEnd ℂ (lowerRootInnerValue p w)) *
        ((lowerRootInnerValue p z -
            lowerRootInnerValue p (starRingEnd ℂ w)) /
          (z - starRingEnd ℂ w)) = _
  rw [star_lowerRootInnerValue_eq_inv_conj]
  field_simp [lowerRootInnerValue, hPz, hconj,
    lowerRootFactor_eval_ne_zero_of_im_pos p hw, hzw]
  ring

/-- Boundary specialization of the pointwise model-component identity. -/
theorem finiteModelBoundaryValue_cauchyProjectionCoordinate
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0)
    (x : ℝ) :
    finiteModelBoundaryValue (lowerRootFactor p)
        (finiteModelCauchyProjectionCoordinate p w) x =
      upperCauchyBoundaryValue w x -
        starRingEnd ℂ (lowerRootInnerValue p w) *
          (lowerRootInnerBoundaryValue p x *
            upperCauchyBoundaryValue w x) := by
  simpa [finiteModelBoundaryValue, upperCauchyBoundaryValue,
    lowerRootInnerBoundaryValue] using
    finiteModelValue_cauchyProjectionCoordinate p hw hconj
      (z := (x : ℂ)) (by simp)

/-- Exact decomposition of a genuine `L²` Cauchy kernel into its finite-model
component and the residual-inner shifted kernel. -/
theorem upperCauchyBoundaryLp_decomposition
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0) :
    upperCauchyBoundaryLp w hw =
      finiteModelBoundaryLpLinearMap
          (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)
          (finiteModelCauchyProjectionCoordinate p w) +
        starRingEnd ℂ (lowerRootInnerValue p w) •
          lowerRootInnerBoundaryLpLinearIsometry p
            (upperCauchyBoundaryLp w hw) := by
  have hshiftedAe :
      lowerRootInnerBoundaryLpLinearIsometry p
          (upperCauchyBoundaryLp w hw) =ᵐ[volume]
        fun x : ℝ ↦ lowerRootInnerBoundaryValue p x *
          upperCauchyBoundaryLp w hw x := by
    simpa only [lowerRootInnerBoundaryLpLinearIsometry_apply] using
      lowerRootInnerBoundaryLpLinearMap_ae p
        (upperCauchyBoundaryLp w hw)
  apply Lp.ext
  filter_upwards [
      upperCauchyBoundaryLp_ae w hw,
      finiteModelBoundaryLpLinearMap_ae
        (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)
        (finiteModelCauchyProjectionCoordinate p w),
      hshiftedAe,
      Lp.coeFn_add
        (finiteModelBoundaryLpLinearMap
          (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)
          (finiteModelCauchyProjectionCoordinate p w))
        (starRingEnd ℂ (lowerRootInnerValue p w) •
          lowerRootInnerBoundaryLpLinearIsometry p
            (upperCauchyBoundaryLp w hw)),
      Lp.coeFn_smul (starRingEnd ℂ (lowerRootInnerValue p w))
        (lowerRootInnerBoundaryLpLinearIsometry p
          (upperCauchyBoundaryLp w hw))]
    with x hk hpositive hshifted hadd hsmul
  rw [hk, hadd]
  simp only [Pi.add_apply]
  rw [hpositive, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hshifted, hk]
  rw [finiteModelBoundaryValue_cauchyProjectionCoordinate p hw hconj x]
  ring

/-- The generic boundary realization of the lower-root finite model. -/
def finiteLowerRootBoundarySubspace (p : ℂ[X]) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.range
    (finiteModelBoundaryLpLinearMap
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p))

instance finiteLowerRootBoundarySubspace_finiteDimensional (p : ℂ[X]) :
    FiniteDimensional ℂ (finiteLowerRootBoundarySubspace p) := by
  change FiniteDimensional ℂ (LinearMap.range
    (finiteModelBoundaryLpLinearMap
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)))
  infer_instance

theorem finiteLowerRootBoundarySubspace_isClosed (p : ℂ[X]) :
    IsClosed (finiteLowerRootBoundarySubspace p :
      Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  Submodule.closed_of_finiteDimensional _

/-- The constructed finite-model component is the actual star projection of
the Cauchy kernel. -/
theorem starProjection_upperCauchyBoundaryLp
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0) :
    (finiteLowerRootBoundarySubspace p).starProjection
        (upperCauchyBoundaryLp w hw) =
      finiteModelBoundaryLpLinearMap
        (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)
        (finiteModelCauchyProjectionCoordinate p w) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal'
  · exact ⟨finiteModelCauchyProjectionCoordinate p w, rfl⟩
  · exact ((finiteLowerRootBoundarySubspace p)ᗮ).smul_mem
      (starRingEnd ℂ (lowerRootInnerValue p w))
      (by simpa [finiteLowerRootBoundarySubspace] using
        residualInner_cauchy_mem_finiteModelBoundary_orthogonal p hw)
  · exact upperCauchyBoundaryLp_decomposition p hw hconj

/-- Coercion form of the exact orthogonal-projection formula. -/
theorem orthogonalProjectionOnto_upperCauchyBoundaryLp
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0) :
    ((finiteLowerRootBoundarySubspace p).orthogonalProjectionOnto
        (upperCauchyBoundaryLp w hw) :
      Lp ℂ 2 (volume : Measure ℝ)) =
      finiteModelBoundaryLpLinearMap
        (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p)
        (finiteModelCauchyProjectionCoordinate p w) := by
  rw [← Submodule.starProjection_apply]
  exact starProjection_upperCauchyBoundaryLp p hw hconj

/-- The exact residual of projecting a Cauchy kernel onto the finite model is
the residual-inner shifted kernel with scalar `conj (S w)`. -/
theorem upperCauchyBoundaryLp_sub_projection
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im)
    (hconj : (lowerRootFactor p).eval (starRingEnd ℂ w) ≠ 0) :
    upperCauchyBoundaryLp w hw -
        ((finiteLowerRootBoundarySubspace p).orthogonalProjectionOnto
          (upperCauchyBoundaryLp w hw) :
          Lp ℂ 2 (volume : Measure ℝ)) =
      starRingEnd ℂ (lowerRootInnerValue p w) •
        lowerRootInnerBoundaryLpLinearIsometry p
          (upperCauchyBoundaryLp w hw) := by
  rw [orthogonalProjectionOnto_upperCauchyBoundaryLp p hw hconj]
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using upperCauchyBoundaryLp_decomposition p hw hconj

/-- Exact weighted inner product of two actual Cauchy-kernel projection
residuals. -/
theorem inner_cauchyBoundaryLp_sub_projections
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0) :
    inner ℂ
        (upperCauchyBoundaryLp w₀ hw₀ -
          ((finiteLowerRootBoundarySubspace p).orthogonalProjectionOnto
            (upperCauchyBoundaryLp w₀ hw₀) :
            Lp ℂ 2 (volume : Measure ℝ)))
        (upperCauchyBoundaryLp w₁ hw₁ -
          ((finiteLowerRootBoundarySubspace p).orthogonalProjectionOnto
            (upperCauchyBoundaryLp w₁ hw₁) :
            Lp ℂ 2 (volume : Measure ℝ))) =
      lowerRootInnerValue p w₀ *
        starRingEnd ℂ (lowerRootInnerValue p w₁) *
          inner ℂ (upperCauchyBoundaryLp w₀ hw₀)
            (upperCauchyBoundaryLp w₁ hw₁) := by
  rw [upperCauchyBoundaryLp_sub_projection p hw₀ hconj₀,
    upperCauchyBoundaryLp_sub_projection p hw₁ hconj₁,
    lowerRootInnerBoundaryLp_weighted_inner]
  simp

end

end RiemannGaussian
