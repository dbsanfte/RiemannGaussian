import RiemannGaussian.FiniteHardyInnerMultiplier
import RiemannGaussian.UpperHalfPlaneIntegral

/-!
# Finite Hardy model orthogonality

This file proves the analytic orthogonality calculation for the finite
residual model.  Multiplication by the residual rational inner function sends
every reflected-upper-root model coordinate into the orthogonal complement of
the lower-root model in the genuine boundary `L²(ℝ, ℂ)` space.  The original
Cauchy-kernel statement is retained as a useful specialization.

The proof reduces the pointwise inner product to a degree-gap-two polynomial
quotient with every pole strictly below the real axis, then applies the
checked upper-half-plane rectangle-contour theorem.
-/

open Filter MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

namespace RiemannGaussian

noncomputable section

/-- The unnormalized upper-half-plane Hardy Cauchy kernel on the real
boundary. -/
def upperCauchyBoundaryValue (w : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - starRingEnd ℂ w)⁻¹

theorem upperCauchyDenominator_eval_real_ne_zero
    {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    (X - C (starRingEnd ℂ w)).eval (x : ℂ) ≠ 0 := by
  simp only [eval_sub, eval_X, eval_C]
  intro hzero
  have him := congrArg Complex.im hzero
  simp at him
  linarith

theorem upperCauchyBoundaryValue_memLp_two
    {w : ℂ} (hw : 0 < w.im) :
    MemLp (upperCauchyBoundaryValue w) 2 := by
  change MemLp (fun x : ℝ ↦ ((x : ℂ) - starRingEnd ℂ w)⁻¹) 2
  simpa only [eval_one, one_div, eval_sub, eval_X, eval_C] using
    (polynomialBoundaryQuotient_memLp_two
      (q := (1 : ℂ[X])) (P := X - C (starRingEnd ℂ w))
      (by simp)
      (upperCauchyDenominator_eval_real_ne_zero hw))

/-- The Cauchy kernel as an actual `L²` equivalence class. -/
noncomputable def upperCauchyBoundaryLp (w : ℂ) (hw : 0 < w.im) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (upperCauchyBoundaryValue_memLp_two hw).toLp
    (upperCauchyBoundaryValue w)

theorem upperCauchyBoundaryLp_ae (w : ℂ) (hw : 0 < w.im) :
    upperCauchyBoundaryLp w hw =ᵐ[volume] upperCauchyBoundaryValue w :=
  MemLp.coeFn_toLp (upperCauchyBoundaryValue_memLp_two hw)

/-- The lower-root denominator, augmented by a Cauchy pole below the real
axis, has no zero in the closed upper half-plane. -/
theorem lowerRootFactor_mul_cauchyDenominator_ne_zero_closedUpper
    (p : ℂ[X]) {w z : ℂ} (hw : 0 < w.im) (hz : 0 ≤ z.im) :
    (lowerRootFactor p * (X - C (starRingEnd ℂ w))).eval z ≠ 0 := by
  rw [eval_mul]
  apply mul_ne_zero
  · by_cases hz0 : z.im = 0
    · have hzReal : (z.re : ℂ) = z := by
        apply Complex.ext
        · simp
        · simp [hz0]
      simpa [hzReal] using lowerRootFactor_eval_real_ne_zero p z.re
    · exact lowerRootFactor_eval_ne_zero_of_im_pos p
        (lt_of_le_of_ne hz (Ne.symm hz0))
  · simp only [eval_sub, eval_X, eval_C]
    intro hzero
    have him := congrArg Complex.im hzero
    simp at him
    linarith

/-- Pointwise cancellation behind Hardy orthogonality.  On the real axis the
conjugate lower-root denominator cancels the numerator of the residual inner
factor, leaving a rational function with all poles below the axis. -/
theorem finiteModelBoundary_inner_residualInner_cauchy
    (p : ℂ[X]) (q : finiteModelSpace (lowerRootFactor p))
    {w : ℂ} (hw : 0 < w.im) (x : ℝ) :
    inner ℂ
        (finiteModelBoundaryValue (lowerRootFactor p) q x)
        (lowerRootInnerBoundaryValue p x *
          upperCauchyBoundaryValue w x) =
      (conjugatePolynomial (q : ℂ[X])).eval (x : ℂ) /
        (lowerRootFactor p * (X - C (starRingEnd ℂ w))).eval (x : ℂ) := by
  have hL := lowerRootFactor_eval_real_ne_zero p x
  have hW := upperCauchyDenominator_eval_real_ne_zero hw x
  unfold finiteModelBoundaryValue finiteModelValue
    lowerRootInnerBoundaryValue lowerRootInnerValue upperCauchyBoundaryValue
  rw [RCLike.inner_apply']
  change
    starRingEnd ℂ
          ((q : ℂ[X]).eval (x : ℂ) /
            (lowerRootFactor p).eval (x : ℂ)) *
        (((conjugatePolynomial (lowerRootFactor p)).eval (x : ℂ) /
            (lowerRootFactor p).eval (x : ℂ)) *
          (((x : ℂ) - starRingEnd ℂ w)⁻¹)) = _
  rw [map_div₀, conjugatePolynomial_eval_real,
    conjugatePolynomial_eval_real]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  field_simp [hL, hW]

/-- The shifted Cauchy kernel `S k_w` is orthogonal in the genuine boundary
`L²` space to every element of the finite residual model `K_S`. -/
theorem finiteModelBoundaryLp_inner_residualInner_cauchy_eq_zero
    (p : ℂ[X]) (q : finiteModelSpace (lowerRootFactor p))
    {w : ℂ} (hw : 0 < w.im) :
    inner ℂ
        (finiteModelBoundaryLpLinearMap
          (lowerRootFactor p)
          (lowerRootFactor_eval_real_ne_zero p) q)
        (lowerRootInnerBoundaryLpLinearIsometry p
          (upperCauchyBoundaryLp w hw)) = 0 := by
  by_cases hq : (q : ℂ[X]) = 0
  · have hq0 : q = 0 := Subtype.ext hq
    rw [hq0, map_zero, inner_zero_left]
  have hqDegree : (q : ℂ[X]).natDegree <
      (lowerRootFactor p).natDegree := by
    apply (natDegree_lt_natDegree_iff hq).2
    rw [degree_eq_natDegree (lowerRootFactor_ne_zero p)]
    exact mem_degreeLT.mp q.property
  have hdenDegree :
      (lowerRootFactor p * (X - C (starRingEnd ℂ w))).natDegree =
        (lowerRootFactor p).natDegree + 1 := by
    rw [natDegree_mul (lowerRootFactor_ne_zero p)
      (X_sub_C_ne_zero _), natDegree_X_sub_C]
  have hdegree :
      (conjugatePolynomial (q : ℂ[X])).natDegree + 2 ≤
        (lowerRootFactor p * (X - C (starRingEnd ℂ w))).natDegree := by
    rw [conjugatePolynomial_natDegree, hdenDegree]
    omega
  let positiveVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finiteModelBoundaryLpLinearMap
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p) q
  let cauchyVector : Lp ℂ 2 (volume : Measure ℝ) :=
    upperCauchyBoundaryLp w hw
  let shiftedVector : Lp ℂ 2 (volume : Measure ℝ) :=
    lowerRootInnerBoundaryLpLinearIsometry p cauchyVector
  have hpositiveAe : positiveVector =ᵐ[volume]
      finiteModelBoundaryValue (lowerRootFactor p) q := by
    exact finiteModelBoundaryLpLinearMap_ae
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p) q
  have hcauchyAe : cauchyVector =ᵐ[volume]
      upperCauchyBoundaryValue w := by
    exact upperCauchyBoundaryLp_ae w hw
  have hshiftedAe : shiftedVector =ᵐ[volume]
      fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * cauchyVector x := by
    simpa [shiftedVector] using
      lowerRootInnerBoundaryLpLinearMap_ae p cauchyVector
  have hpointwise :
      (fun x : ℝ ↦ inner ℂ (positiveVector x) (shiftedVector x)) =ᵐ[volume]
        fun x : ℝ ↦
          (conjugatePolynomial (q : ℂ[X])).eval (x : ℂ) /
            (lowerRootFactor p *
              (X - C (starRingEnd ℂ w))).eval (x : ℂ) := by
    filter_upwards [hpositiveAe, hshiftedAe, hcauchyAe]
      with x hpositive hshifted hcauchy
    rw [hpositive, hshifted, hcauchy]
    exact finiteModelBoundary_inner_residualInner_cauchy p q hw x
  have hintegrable : Integrable
      (fun x : ℝ ↦
        (conjugatePolynomial (q : ℂ[X])).eval (x : ℂ) /
          (lowerRootFactor p *
            (X - C (starRingEnd ℂ w))).eval (x : ℂ)) :=
    (L2.integrable_inner positiveVector shiftedVector).congr hpointwise
  change inner ℂ positiveVector shiftedVector = 0
  rw [L2.inner_def, integral_congr_ae hpointwise]
  exact integral_polynomialQuotient_eq_zero_of_upperHalfPlane
    hdegree
    (fun z hz =>
      lowerRootFactor_mul_cauchyDenominator_ne_zero_closedUpper p hw hz)
    hintegrable

/-- Subspace form of the preceding orthogonality theorem. -/
theorem residualInner_cauchy_mem_finiteModelBoundary_orthogonal
    (p : ℂ[X]) {w : ℂ} (hw : 0 < w.im) :
    lowerRootInnerBoundaryLpLinearIsometry p
        (upperCauchyBoundaryLp w hw) ∈
      (LinearMap.range
        (finiteModelBoundaryLpLinearMap
          (lowerRootFactor p)
          (lowerRootFactor_eval_real_ne_zero p)))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨q, rfl⟩ := hu
  rw [← inner_conj_symm,
    finiteModelBoundaryLp_inner_residualInner_cauchy_eq_zero p q hw,
    map_zero]

/-- The product of the lower-root denominator and the reflected upper-root
denominator has no zero in the closed upper half-plane. -/
theorem lowerRootFactor_mul_conjugateUpperRootFactor_ne_zero_closedUpper
    (p : ℂ[X]) {z : ℂ} (hz : 0 ≤ z.im) :
    (lowerRootFactor p *
      conjugatePolynomial (upperRootFactor p)).eval z ≠ 0 := by
  rw [eval_mul]
  apply mul_ne_zero
  · by_cases hz0 : z.im = 0
    · have hzReal : (z.re : ℂ) = z := by
        apply Complex.ext
        · simp
        · simp [hz0]
      simpa [hzReal] using lowerRootFactor_eval_real_ne_zero p z.re
    · exact lowerRootFactor_eval_ne_zero_of_im_pos p
        (lt_of_le_of_ne hz (Ne.symm hz0))
  · by_cases hz0 : z.im = 0
    · have hzReal : (z.re : ℂ) = z := by
        apply Complex.ext
        · simp
        · simp [hz0]
      simpa [hzReal] using
        conjugate_upperRootFactor_eval_real_ne_zero p z.re
    · exact conjugate_upperRootFactor_eval_ne_zero_of_im_pos p
        (lt_of_le_of_ne hz (Ne.symm hz0))

/-- Pointwise cancellation for arbitrary coordinates in the positive and
negative finite models.  The reflected lower-root factor cancels exactly,
leaving a quotient whose denominator has all roots below the real axis. -/
theorem finiteModelBoundary_inner_residualInner_negative
    (p : ℂ[X])
    (qS : finiteModelSpace (lowerRootFactor p))
    (qB : finiteModelSpace
      (conjugatePolynomial (upperRootFactor p)))
    (x : ℝ) :
    inner ℂ
        (finiteModelBoundaryValue (lowerRootFactor p) qS x)
        (lowerRootInnerBoundaryValue p x *
          finiteModelBoundaryValue
            (conjugatePolynomial (upperRootFactor p)) qB x) =
      (conjugatePolynomial (qS : ℂ[X]) * (qB : ℂ[X])).eval
          (x : ℂ) /
        (lowerRootFactor p *
          conjugatePolynomial (upperRootFactor p)).eval (x : ℂ) := by
  have hL := lowerRootFactor_eval_real_ne_zero p x
  have hD := conjugate_upperRootFactor_eval_real_ne_zero p x
  unfold finiteModelBoundaryValue finiteModelValue
    lowerRootInnerBoundaryValue lowerRootInnerValue
  rw [RCLike.inner_apply']
  change
    starRingEnd ℂ
          ((qS : ℂ[X]).eval (x : ℂ) /
            (lowerRootFactor p).eval (x : ℂ)) *
        (((conjugatePolynomial (lowerRootFactor p)).eval (x : ℂ) /
            (lowerRootFactor p).eval (x : ℂ)) *
          ((qB : ℂ[X]).eval (x : ℂ) /
            (conjugatePolynomial (upperRootFactor p)).eval (x : ℂ))) = _
  rw [map_div₀]
  simp only [eval_mul, conjugatePolynomial_eval_real]
  field_simp [hL, hD]

/-- Multiplication by the residual inner function sends every element of the
negative finite model to a vector orthogonal to every element of the positive
finite model.  This statement is independent of root multiplicities. -/
theorem finiteModelBoundaryLp_inner_residualInner_negative_eq_zero
    (p : ℂ[X])
    (qS : finiteModelSpace (lowerRootFactor p))
    (qB : finiteModelSpace
      (conjugatePolynomial (upperRootFactor p))) :
    inner ℂ
        (finiteModelBoundaryLpLinearMap
          (lowerRootFactor p)
          (lowerRootFactor_eval_real_ne_zero p) qS)
        (lowerRootInnerBoundaryLpLinearIsometry p
          (finiteModelBoundaryLpLinearMap
            (conjugatePolynomial (upperRootFactor p))
            (conjugate_upperRootFactor_eval_real_ne_zero p) qB)) = 0 := by
  by_cases hqS : (qS : ℂ[X]) = 0
  · have hqS0 : qS = 0 := Subtype.ext hqS
    rw [hqS0, map_zero, inner_zero_left]
  by_cases hqB : (qB : ℂ[X]) = 0
  · have hqB0 : qB = 0 := Subtype.ext hqB
    rw [hqB0, map_zero, map_zero, inner_zero_right]
  have hqSDegree : (qS : ℂ[X]).natDegree <
      (lowerRootFactor p).natDegree := by
    apply (natDegree_lt_natDegree_iff hqS).2
    rw [degree_eq_natDegree (lowerRootFactor_ne_zero p)]
    exact mem_degreeLT.mp qS.property
  have hqBDegree : (qB : ℂ[X]).natDegree <
      (conjugatePolynomial (upperRootFactor p)).natDegree := by
    apply (natDegree_lt_natDegree_iff hqB).2
    rw [degree_eq_natDegree
      (conjugatePolynomial_ne_zero (upperRootFactor_ne_zero p))]
    exact mem_degreeLT.mp qB.property
  have hdenDegree :
      (lowerRootFactor p *
          conjugatePolynomial (upperRootFactor p)).natDegree =
        (lowerRootFactor p).natDegree +
          (conjugatePolynomial (upperRootFactor p)).natDegree := by
    rw [natDegree_mul (lowerRootFactor_ne_zero p)
      (conjugatePolynomial_ne_zero (upperRootFactor_ne_zero p))]
  have hnumDegree :
      (conjugatePolynomial (qS : ℂ[X]) *
          (qB : ℂ[X])).natDegree =
        (qS : ℂ[X]).natDegree + (qB : ℂ[X]).natDegree := by
    rw [natDegree_mul (conjugatePolynomial_ne_zero hqS) hqB,
      conjugatePolynomial_natDegree]
  have hdegree :
      (conjugatePolynomial (qS : ℂ[X]) *
            (qB : ℂ[X])).natDegree + 2 ≤
        (lowerRootFactor p *
          conjugatePolynomial (upperRootFactor p)).natDegree := by
    rw [hnumDegree, hdenDegree]
    omega
  let positiveVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finiteModelBoundaryLpLinearMap
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p) qS
  let negativeVector : Lp ℂ 2 (volume : Measure ℝ) :=
    finiteModelBoundaryLpLinearMap
      (conjugatePolynomial (upperRootFactor p))
      (conjugate_upperRootFactor_eval_real_ne_zero p) qB
  let shiftedVector : Lp ℂ 2 (volume : Measure ℝ) :=
    lowerRootInnerBoundaryLpLinearIsometry p negativeVector
  have hpositiveAe : positiveVector =ᵐ[volume]
      finiteModelBoundaryValue (lowerRootFactor p) qS := by
    exact finiteModelBoundaryLpLinearMap_ae
      (lowerRootFactor p) (lowerRootFactor_eval_real_ne_zero p) qS
  have hnegativeAe : negativeVector =ᵐ[volume]
      finiteModelBoundaryValue
        (conjugatePolynomial (upperRootFactor p)) qB := by
    exact finiteModelBoundaryLpLinearMap_ae
      (conjugatePolynomial (upperRootFactor p))
      (conjugate_upperRootFactor_eval_real_ne_zero p) qB
  have hshiftedAe : shiftedVector =ᵐ[volume]
      fun x : ℝ ↦ lowerRootInnerBoundaryValue p x * negativeVector x := by
    simpa [shiftedVector] using
      lowerRootInnerBoundaryLpLinearMap_ae p negativeVector
  have hpointwise :
      (fun x : ℝ ↦ inner ℂ (positiveVector x) (shiftedVector x)) =ᵐ[volume]
        fun x : ℝ ↦
          (conjugatePolynomial (qS : ℂ[X]) * (qB : ℂ[X])).eval
              (x : ℂ) /
            (lowerRootFactor p *
              conjugatePolynomial (upperRootFactor p)).eval (x : ℂ) := by
    filter_upwards [hpositiveAe, hshiftedAe, hnegativeAe]
      with x hpositive hshifted hnegative
    rw [hpositive, hshifted, hnegative]
    exact finiteModelBoundary_inner_residualInner_negative p qS qB x
  have hintegrable : Integrable
      (fun x : ℝ ↦
        (conjugatePolynomial (qS : ℂ[X]) * (qB : ℂ[X])).eval
            (x : ℂ) /
          (lowerRootFactor p *
            conjugatePolynomial (upperRootFactor p)).eval (x : ℂ)) :=
    (L2.integrable_inner positiveVector shiftedVector).congr hpointwise
  change inner ℂ positiveVector shiftedVector = 0
  rw [L2.inner_def, integral_congr_ae hpointwise]
  exact integral_polynomialQuotient_eq_zero_of_upperHalfPlane
    hdegree
    (fun z hz =>
      lowerRootFactor_mul_conjugateUpperRootFactor_ne_zero_closedUpper p hz)
    hintegrable

/-- Subspace form of multiplicity-independent finite-model orthogonality. -/
theorem residualInner_negative_mem_finiteModelBoundary_orthogonal
    (p : ℂ[X])
    (qB : finiteModelSpace
      (conjugatePolynomial (upperRootFactor p))) :
    lowerRootInnerBoundaryLpLinearIsometry p
        (finiteModelBoundaryLpLinearMap
          (conjugatePolynomial (upperRootFactor p))
          (conjugate_upperRootFactor_eval_real_ne_zero p) qB) ∈
      (LinearMap.range
        (finiteModelBoundaryLpLinearMap
          (lowerRootFactor p)
          (lowerRootFactor_eval_real_ne_zero p)))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨qS, rfl⟩ := hu
  rw [← inner_conj_symm,
    finiteModelBoundaryLp_inner_residualInner_negative_eq_zero p qS qB,
    map_zero]

end

end RiemannGaussian
