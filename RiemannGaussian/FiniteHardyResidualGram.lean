import RiemannGaussian.FiniteHardyProjection
import RiemannGaussian.SymmetricPickMetricDeterminant

/-!
# The actual finite Hardy residual Gram matrix

This file identifies, entry by entry, the Gram matrix of two genuine
Cauchy-kernel orthogonal-projection residuals with the weighted Hermitian
matrix used by the two-node metric determinant calculation.  It also proves
that distinct upper-half-plane Cauchy vectors are linearly independent, so
their base Gram determinant is strictly positive.

Consequently the determinant ratio is exactly the squared modulus of the
product of the two residual-inner values.  This ratio theorem does not assume
that the two generalized metric modes are distinct.
-/

open MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal Matrix

namespace RiemannGaussian

noncomputable section

theorem upperCauchyBoundaryValue_continuous
    {w : ℂ} (hw : 0 < w.im) :
    Continuous (upperCauchyBoundaryValue w) := by
  unfold upperCauchyBoundaryValue
  simpa using
    (polynomialBoundaryQuotient_continuous
      (q := (1 : ℂ[X]))
      (P := X - C (starRingEnd ℂ w))
      (upperCauchyDenominator_eval_real_ne_zero hw))

/-- Boundary Cauchy vectors at distinct upper-half-plane nodes cannot be
scalar multiples in `L²`. -/
theorem upperCauchyBoundaryLp_ne_smul_of_ne
    {w₀ w₁ : ℂ} (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hne : w₀ ≠ w₁) (c : ℂ) :
    upperCauchyBoundaryLp w₁ hw₁ ≠
      c • upperCauchyBoundaryLp w₀ hw₀ := by
  intro heq
  have h₁ := upperCauchyBoundaryLp_ae w₁ hw₁
  rw [heq] at h₁
  have hae : upperCauchyBoundaryValue w₁ =ᵐ[volume]
      fun x : ℝ ↦ c * upperCauchyBoundaryValue w₀ x := by
    filter_upwards [h₁, upperCauchyBoundaryLp_ae w₀ hw₀,
      Lp.coeFn_smul c (upperCauchyBoundaryLp w₀ hw₀)]
      with x h₁x h₀x hsmul
    rw [← h₁x, hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₀x]
  have hfun : upperCauchyBoundaryValue w₁ =
      fun x : ℝ ↦ c * upperCauchyBoundaryValue w₀ x :=
    ((upperCauchyBoundaryValue_continuous hw₁).ae_eq_iff_eq volume
      (continuous_const.mul
        (upperCauchyBoundaryValue_continuous hw₀))).mp hae
  have hzero := congrFun hfun 0
  have hone := congrFun hfun 1
  have hw₀zero := upperCauchyDenominator_eval_real_ne_zero hw₀ 0
  have hw₁zero := upperCauchyDenominator_eval_real_ne_zero hw₁ 0
  have hw₀one := upperCauchyDenominator_eval_real_ne_zero hw₀ 1
  have hw₁one := upperCauchyDenominator_eval_real_ne_zero hw₁ 1
  have h₀zero : (0 : ℂ) - starRingEnd ℂ w₀ ≠ 0 := by
    simpa using hw₀zero
  have h₁zero : (0 : ℂ) - starRingEnd ℂ w₁ ≠ 0 := by
    simpa using hw₁zero
  have hw₀star : starRingEnd ℂ w₀ ≠ 0 := by
    simpa using h₀zero
  have hw₁star : starRingEnd ℂ w₁ ≠ 0 := by
    simpa using h₁zero
  have h₀one : (1 : ℂ) - starRingEnd ℂ w₀ ≠ 0 := by
    simpa using hw₀one
  have h₁one : (1 : ℂ) - starRingEnd ℂ w₁ ≠ 0 := by
    simpa using hw₁one
  unfold upperCauchyBoundaryValue at hzero hone
  norm_num at hzero hone
  field_simp [hw₀star, hw₁star] at hzero
  field_simp [h₀one, h₁one] at hone
  apply hne
  have hc : c = 1 := by
    linear_combination -hzero - hone
  have hstar : starRingEnd ℂ w₀ = starRingEnd ℂ w₁ := by
    rw [hc, mul_one] at hzero
    exact hzero
  exact (starRingEnd ℂ).injective hstar

/-- The residual left after projecting a boundary Cauchy vector onto the
finite lower-root model. -/
def finiteHardyCauchyProjectionResidual
    (p : ℂ[X]) (w : ℂ) (hw : 0 < w.im) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  upperCauchyBoundaryLp w hw -
    ((finiteLowerRootBoundarySubspace p).orthogonalProjectionOnto
      (upperCauchyBoundaryLp w hw) :
      Lp ℂ 2 (volume : Measure ℝ))

/-- The Gram matrix of two unnormalized upper-half-plane Cauchy vectors.
The row-column convention is `G i j = inner (k j) (k i)`, matching the
existing Hermitian-matrix definitions. -/
def twoUpperCauchyGramMatrix
    (w₀ w₁ : ℂ) (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ (upperCauchyBoundaryLp w₀ hw₀)
        (upperCauchyBoundaryLp w₀ hw₀),
      inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
        (upperCauchyBoundaryLp w₀ hw₀);
     inner ℂ (upperCauchyBoundaryLp w₀ hw₀)
        (upperCauchyBoundaryLp w₁ hw₁),
      inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
        (upperCauchyBoundaryLp w₁ hw₁)]

/-- The Gram matrix of the two actual orthogonal-projection residuals. -/
def twoFiniteHardyResidualGramMatrix
    (p : ℂ[X]) (w₀ w₁ : ℂ)
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ (finiteHardyCauchyProjectionResidual p w₀ hw₀)
        (finiteHardyCauchyProjectionResidual p w₀ hw₀),
      inner ℂ (finiteHardyCauchyProjectionResidual p w₁ hw₁)
        (finiteHardyCauchyProjectionResidual p w₀ hw₀);
     inner ℂ (finiteHardyCauchyProjectionResidual p w₀ hw₀)
        (finiteHardyCauchyProjectionResidual p w₁ hw₁),
      inner ℂ (finiteHardyCauchyProjectionResidual p w₁ hw₁)
        (finiteHardyCauchyProjectionResidual p w₁ hw₁)]

theorem twoUpperCauchyGramMatrix_eq_twoHermitianMatrix
    (w₀ w₁ : ℂ) (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im) :
    twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁ =
      twoHermitianMatrix
        (‖upperCauchyBoundaryLp w₀ hw₀‖ ^ 2)
        (‖upperCauchyBoundaryLp w₁ hw₁‖ ^ 2)
        (inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
          (upperCauchyBoundaryLp w₀ hw₀)) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [twoUpperCauchyGramMatrix, twoHermitianMatrix,
      inner_self_eq_norm_sq_to_K]
  · simp [twoUpperCauchyGramMatrix, twoHermitianMatrix]
  · simp [twoUpperCauchyGramMatrix, twoHermitianMatrix, inner_conj_symm]
  · simp [twoUpperCauchyGramMatrix, twoHermitianMatrix,
      inner_self_eq_norm_sq_to_K]

/-- Strict Cauchy--Schwarz gives positivity of the base two-node Gram
determinant whenever the nodes are distinct. -/
theorem twoUpperCauchyGram_twoHermitianDet_pos
    {w₀ w₁ : ℂ} (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hne : w₀ ≠ w₁) :
    0 < twoHermitianDet
      (‖upperCauchyBoundaryLp w₀ hw₀‖ ^ 2)
      (‖upperCauchyBoundaryLp w₁ hw₁‖ ^ 2)
      (inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
        (upperCauchyBoundaryLp w₀ hw₀)) := by
  let k₀ := upperCauchyBoundaryLp w₀ hw₀
  let k₁ := upperCauchyBoundaryLp w₁ hw₁
  have hk₁ : k₁ ≠ 0 := by
    simpa [k₁, k₀] using
      upperCauchyBoundaryLp_ne_smul_of_ne hw₀ hw₁ hne (0 : ℂ)
  have hk₀ : k₀ ≠ 0 := by
    simpa [k₁, k₀] using
      upperCauchyBoundaryLp_ne_smul_of_ne hw₁ hw₀ hne.symm (0 : ℂ)
  have hnotEq : ‖inner ℂ k₁ k₀‖ ≠ ‖k₁‖ * ‖k₀‖ := by
    intro heq
    obtain ⟨c, _hc, hsmul⟩ :=
      (norm_inner_eq_norm_iff hk₁ hk₀).mp heq
    exact upperCauchyBoundaryLp_ne_smul_of_ne hw₁ hw₀ hne.symm c
      (by simpa [k₁, k₀] using hsmul)
  have hstrict : ‖inner ℂ k₁ k₀‖ < ‖k₁‖ * ‖k₀‖ :=
    lt_of_le_of_ne (norm_inner_le_norm k₁ k₀) hnotEq
  have hnormProduct : 0 < ‖k₁‖ * ‖k₀‖ :=
    mul_pos (norm_pos_iff.mpr hk₁) (norm_pos_iff.mpr hk₀)
  have hsum : 0 < ‖k₁‖ * ‖k₀‖ + ‖inner ℂ k₁ k₀‖ :=
    add_pos_of_pos_of_nonneg hnormProduct (norm_nonneg _)
  have hsquare : ‖inner ℂ k₁ k₀‖ ^ 2 <
      (‖k₁‖ * ‖k₀‖) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hstrict) hsum]
  unfold twoHermitianDet
  rw [← Complex.sq_norm]
  dsimp [k₀, k₁] at hsquare ⊢
  nlinarith [sq_nonneg
    (‖upperCauchyBoundaryLp w₁ hw₁‖ *
      ‖upperCauchyBoundaryLp w₀ hw₀‖)]

theorem twoUpperCauchyGramMatrix_det_ne_zero
    {w₀ w₁ : ℂ} (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hne : w₀ ≠ w₁) :
    Matrix.det (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) ≠ 0 := by
  rw [twoUpperCauchyGramMatrix_eq_twoHermitianMatrix,
    twoHermitianMatrix_det]
  exact_mod_cast (twoUpperCauchyGram_twoHermitianDet_pos hw₀ hw₁ hne).ne'

/-- Entrywise identification of the actual Hardy residual Gram with the
weighted Hermitian matrix. -/
theorem twoFiniteHardyResidualGramMatrix_eq_weighted
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0) :
    twoFiniteHardyResidualGramMatrix p w₀ w₁ hw₀ hw₁ =
      twoValueWeightedHermitianMatrix
        (‖upperCauchyBoundaryLp w₀ hw₀‖ ^ 2)
        (‖upperCauchyBoundaryLp w₁ hw₁‖ ^ 2)
        (inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
          (upperCauchyBoundaryLp w₀ hw₀))
        (starRingEnd ℂ (lowerRootInnerValue p w₀))
        (starRingEnd ℂ (lowerRootInnerValue p w₁)) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [twoFiniteHardyResidualGramMatrix,
      finiteHardyCauchyProjectionResidual]
  · rw [inner_cauchyBoundaryLp_sub_projections p hw₀ hw₀ hconj₀ hconj₀]
    simp [twoValueWeightedHermitianMatrix, Complex.normSq_eq_conj_mul_self,
      inner_self_eq_norm_sq_to_K]
    left
    ring
  · rw [inner_cauchyBoundaryLp_sub_projections p hw₁ hw₀ hconj₁ hconj₀]
    simp [twoValueWeightedHermitianMatrix]
    ring
  · rw [inner_cauchyBoundaryLp_sub_projections p hw₀ hw₁ hconj₀ hconj₁]
    simp [twoValueWeightedHermitianMatrix, inner_conj_symm]
    ring
  · rw [inner_cauchyBoundaryLp_sub_projections p hw₁ hw₁ hconj₁ hconj₁]
    simp [twoValueWeightedHermitianMatrix, Complex.normSq_eq_conj_mul_self,
      inner_self_eq_norm_sq_to_K]
    left
    ring

/-- The actual two-node residual-versus-base Gram pencil. -/
def twoFiniteHardyCauchyMetricPencil
    (p : ℂ[X]) (w₀ w₁ : ℂ)
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im) (μ : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  twoFiniteHardyResidualGramMatrix p w₀ w₁ hw₀ hw₁ -
    μ • twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁

/-- The actual Hardy metric pencil is literally the previously checked
weighted Gram pencil. -/
theorem twoFiniteHardyCauchyMetricPencil_eq_weighted
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0)
    (μ : ℂ) :
    twoFiniteHardyCauchyMetricPencil p w₀ w₁ hw₀ hw₁ μ =
      twoValueWeightedGramPencil
        (‖upperCauchyBoundaryLp w₀ hw₀‖ ^ 2)
        (‖upperCauchyBoundaryLp w₁ hw₁‖ ^ 2)
        (inner ℂ (upperCauchyBoundaryLp w₁ hw₁)
          (upperCauchyBoundaryLp w₀ hw₀))
        (starRingEnd ℂ (lowerRootInnerValue p w₀))
        (starRingEnd ℂ (lowerRootInnerValue p w₁)) μ := by
  rw [twoFiniteHardyCauchyMetricPencil,
    twoFiniteHardyResidualGramMatrix_eq_weighted p hw₀ hw₁ hconj₀ hconj₁,
    twoUpperCauchyGramMatrix_eq_twoHermitianMatrix]
  rfl

/-- Determinant of the actual residual Gram matrix. -/
theorem twoFiniteHardyResidualGramMatrix_det
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0) :
    Matrix.det
        (twoFiniteHardyResidualGramMatrix p w₀ w₁ hw₀ hw₁) =
      (Complex.normSq
          (lowerRootInnerValue p w₀ * lowerRootInnerValue p w₁) : ℂ) *
        Matrix.det (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) := by
  rw [twoFiniteHardyResidualGramMatrix_eq_weighted p hw₀ hw₁ hconj₀ hconj₁,
    twoValueWeightedHermitianMatrix_det,
    twoUpperCauchyGramMatrix_eq_twoHermitianMatrix,
    twoHermitianMatrix_det]
  simp

/-- Determinant ratio under the minimal nondegeneracy hypothesis on the base
Gram matrix. -/
theorem twoFiniteHardyResidualGramMatrix_det_ratio
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0)
    (hbase : Matrix.det
      (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) ≠ 0) :
    Matrix.det
          (twoFiniteHardyResidualGramMatrix p w₀ w₁ hw₀ hw₁) /
        Matrix.det (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) =
      (Complex.normSq
        (lowerRootInnerValue p w₀ * lowerRootInnerValue p w₁) : ℂ) := by
  rw [twoFiniteHardyResidualGramMatrix_det p hw₀ hw₁ hconj₀ hconj₁]
  exact mul_div_cancel_right₀ _ hbase

/-- For distinct upper nodes, strict Cauchy--Schwarz automatically discharges
the base-Gram nondegeneracy hypothesis. -/
theorem twoFiniteHardyResidualGramMatrix_det_ratio_of_ne
    (p : ℂ[X]) {w₀ w₁ : ℂ}
    (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im) (hne : w₀ ≠ w₁)
    (hconj₀ : (lowerRootFactor p).eval (starRingEnd ℂ w₀) ≠ 0)
    (hconj₁ : (lowerRootFactor p).eval (starRingEnd ℂ w₁) ≠ 0) :
    Matrix.det
          (twoFiniteHardyResidualGramMatrix p w₀ w₁ hw₀ hw₁) /
        Matrix.det (twoUpperCauchyGramMatrix w₀ w₁ hw₀ hw₁) =
      (Complex.normSq
        (lowerRootInnerValue p w₀ * lowerRootInnerValue p w₁) : ℂ) :=
  twoFiniteHardyResidualGramMatrix_det_ratio p hw₀ hw₁ hconj₀ hconj₁
    (twoUpperCauchyGramMatrix_det_ne_zero hw₀ hw₁ hne)

end

end RiemannGaussian
