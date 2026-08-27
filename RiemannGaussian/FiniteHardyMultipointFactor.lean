import RiemannGaussian.FiniteHardyMultipointDenominator

/-!
# Complete core-factor maximum estimate

This file cancels a complete multiset of upper-half-plane interpolation roots
from a rational numerator.  Its reflected root polynomial has the same degree
and supplies a finite Blaschke product with unit real-boundary norm.  Applying
the checked rational maximum principle to the residual quotient gives the
full multiplicity-aware pseudo-hyperbolic product estimate.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-- The monic polynomial with the supplied multiset of roots, retaining every
root occurrence. -/
def multisetRootPolynomial (zeros : Multiset ℂ) : ℂ[X] :=
  (zeros.map fun alpha => X - C alpha).prod

/-- The monic polynomial whose roots are the conjugates of the supplied root
multiset. -/
def reflectedMultisetRootPolynomial (zeros : Multiset ℂ) : ℂ[X] :=
  (zeros.map fun alpha => X - C (starRingEnd ℂ alpha)).prod

/-- The multiset root polynomial is monic. -/
theorem multisetRootPolynomial_monic (zeros : Multiset ℂ) :
    (multisetRootPolynomial zeros).Monic := by
  exact monic_multisetProd_X_sub_C zeros

/-- The reflected multiset root polynomial is monic. -/
theorem reflectedMultisetRootPolynomial_monic (zeros : Multiset ℂ) :
    (reflectedMultisetRootPolynomial zeros).Monic := by
  simpa [reflectedMultisetRootPolynomial, Multiset.map_map,
    Function.comp_def] using
    monic_multisetProd_X_sub_C (zeros.map (starRingEnd ℂ))

/-- The degree of the multiset root polynomial is the multiset cardinality. -/
@[simp] theorem multisetRootPolynomial_natDegree (zeros : Multiset ℂ) :
    (multisetRootPolynomial zeros).natDegree = zeros.card := by
  simp [multisetRootPolynomial]

/-- Reflection preserves the cardinality-counted root-polynomial degree. -/
@[simp] theorem reflectedMultisetRootPolynomial_natDegree
    (zeros : Multiset ℂ) :
    (reflectedMultisetRootPolynomial zeros).natDegree = zeros.card := by
  simpa [reflectedMultisetRootPolynomial, Multiset.map_map,
    Function.comp_def] using
    natDegree_multiset_prod_X_sub_C_eq_card
      (zeros.map (starRingEnd ℂ))

/-- Evaluation of the multiset root polynomial is the product of the linear
root differences. -/
@[simp] theorem multisetRootPolynomial_eval (zeros : Multiset ℂ) (z : ℂ) :
    (multisetRootPolynomial zeros).eval z =
      (zeros.map fun alpha => z - alpha).prod := by
  simp [multisetRootPolynomial, Polynomial.eval_multiset_prod]

/-- Evaluation of the reflected polynomial is the product of the reflected
linear root differences. -/
@[simp] theorem reflectedMultisetRootPolynomial_eval
    (zeros : Multiset ℂ) (z : ℂ) :
    (reflectedMultisetRootPolynomial zeros).eval z =
      (zeros.map fun alpha => z - starRingEnd ℂ alpha).prod := by
  simp [reflectedMultisetRootPolynomial, Polynomial.eval_multiset_prod]

/-- The quotient of a root polynomial by its reflected polynomial is exactly
the corresponding multiset upper-half-plane Blaschke product. -/
theorem multisetUpperHalfPlaneBlaschke_eq_rootPolynomial_div_reflected
    (zeros : Multiset ℂ) (z : ℂ) :
    multisetUpperHalfPlaneBlaschke zeros z =
      (multisetRootPolynomial zeros).eval z /
        (reflectedMultisetRootPolynomial zeros).eval z := by
  rw [multisetRootPolynomial_eval, reflectedMultisetRootPolynomial_eval]
  unfold multisetUpperHalfPlaneBlaschke elementaryUpperHalfPlaneBlaschke
  exact Multiset.prod_map_div (G := ℂ) (m := zeros)
    (f := fun alpha => z - alpha)
    (g := fun alpha => z - starRingEnd ℂ alpha)

/-- A reflected polynomial built from upper-half-plane roots has no zero on
the closed upper half-plane. -/
theorem reflectedMultisetRootPolynomial_eval_ne_zero
    {zeros : Multiset ℂ} (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    {z : ℂ} (hz : 0 ≤ z.im) :
    (reflectedMultisetRootPolynomial zeros).eval z ≠ 0 := by
  rw [reflectedMultisetRootPolynomial_eval]
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨alpha, halpha, heq⟩ := Multiset.mem_map.mp hzero
  have him := congrArg Complex.im heq
  simp at him
  linarith [hzeros alpha halpha]

/-- A finite multiset upper-half-plane Blaschke product has unit norm on the
real boundary. -/
theorem norm_multisetUpperHalfPlaneBlaschke_real
    {zeros : Multiset ℂ} (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    (x : ℝ) :
    ‖multisetUpperHalfPlaneBlaschke zeros (x : ℂ)‖ = 1 := by
  induction zeros using Multiset.induction_on with
  | empty => simp [multisetUpperHalfPlaneBlaschke]
  | @cons alpha zeros ih =>
      have halpha : 0 < alpha.im := hzeros alpha (by simp)
      have htail : ∀ beta ∈ zeros, 0 < beta.im := by
        intro beta hbeta
        exact hzeros beta (by simp [hbeta])
      have hden : (x : ℂ) - starRingEnd ℂ alpha ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        simp at him
        linarith
      have hfactor :
          ‖elementaryUpperHalfPlaneBlaschke alpha (x : ℂ)‖ = 1 := by
        unfold elementaryUpperHalfPlaneBlaschke
        rw [norm_div, show ‖(x : ℂ) - alpha‖ =
            ‖(x : ℂ) - starRingEnd ℂ alpha‖ by
          calc
            ‖(x : ℂ) - alpha‖ =
                ‖starRingEnd ℂ ((x : ℂ) - alpha)‖ :=
              (Complex.norm_conj _).symm
            _ = ‖(x : ℂ) - starRingEnd ℂ alpha‖ := by simp,
          div_self (norm_ne_zero_iff.mpr hden)]
      simp only [multisetUpperHalfPlaneBlaschke,
        Multiset.map_cons, Multiset.prod_cons, norm_mul, hfactor, one_mul]
      simpa only [multisetUpperHalfPlaneBlaschke] using ih htail

/-- The norm of the multiset Blaschke product is exactly the complete product
of upper-half-plane pseudo-hyperbolic distances. -/
theorem norm_multisetUpperHalfPlaneBlaschke_eq_product_distance
    (zeros : Multiset ℂ) (z : ℂ) :
    ‖multisetUpperHalfPlaneBlaschke zeros z‖ =
      (zeros.map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod := by
  induction zeros using Multiset.induction_on with
  | empty => simp [multisetUpperHalfPlaneBlaschke]
  | @cons alpha zeros ih =>
      simp only [multisetUpperHalfPlaneBlaschke,
        Multiset.map_cons, Multiset.prod_cons, norm_mul]
      rw [show ‖(zeros.map fun beta =>
          elementaryUpperHalfPlaneBlaschke beta z).prod‖ =
        (zeros.map fun beta =>
          upperHalfPlanePseudoHyperbolicDistance z beta).prod by
            simpa only [multisetUpperHalfPlaneBlaschke] using ih]
      rfl

/-- Replacing a root polynomial by its reflected polynomial in a product
does not change the product degree. -/
theorem reflectedMultisetRootPolynomial_mul_degree_eq
    (zeros : Multiset ℂ) (R : ℂ[X]) :
    (reflectedMultisetRootPolynomial zeros * R).degree =
      (multisetRootPolynomial zeros * R).degree := by
  rw [degree_mul, degree_mul]
  congr 1
  rw [degree_eq_natDegree (reflectedMultisetRootPolynomial_monic zeros).ne_zero,
    degree_eq_natDegree (multisetRootPolynomial_monic zeros).ne_zero,
    reflectedMultisetRootPolynomial_natDegree,
    multisetRootPolynomial_natDegree]

/-- On the real boundary, cancelling the unit-norm Blaschke factor preserves
the norm bound for the reflected-factor residual quotient. -/
theorem reflectedFactorQuotient_norm_le_of_original_real
    {zeros : Multiset ℂ} (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    {N D R : ℂ[X]} {C : ℝ}
    (hfactor : N = multisetRootPolynomial zeros * R)
    (hD : ∀ x : ℝ, D.eval (x : ℂ) ≠ 0)
    (hbound : ∀ x : ℝ, ‖N.eval (x : ℂ) / D.eval (x : ℂ)‖ ≤ C)
    (x : ℝ) :
    ‖(reflectedMultisetRootPolynomial zeros * R).eval (x : ℂ) /
        D.eval (x : ℂ)‖ ≤ C := by
  have hreflected :
      (reflectedMultisetRootPolynomial zeros).eval (x : ℂ) ≠ 0 :=
    reflectedMultisetRootPolynomial_eval_ne_zero hzeros
      (show 0 ≤ ((x : ℂ)).im by simp)
  have hunit :
      ‖(multisetRootPolynomial zeros).eval (x : ℂ) /
          (reflectedMultisetRootPolynomial zeros).eval (x : ℂ)‖ = 1 := by
    rw [← multisetUpperHalfPlaneBlaschke_eq_rootPolynomial_div_reflected]
    exact norm_multisetUpperHalfPlaneBlaschke_real hzeros x
  have hidentity :
      N.eval (x : ℂ) / D.eval (x : ℂ) =
        ((multisetRootPolynomial zeros).eval (x : ℂ) /
          (reflectedMultisetRootPolynomial zeros).eval (x : ℂ)) *
        ((reflectedMultisetRootPolynomial zeros * R).eval (x : ℂ) /
          D.eval (x : ℂ)) := by
    rw [hfactor, eval_mul, eval_mul]
    field_simp [hreflected, hD x]
  have hfull := hbound x
  rw [hidentity, norm_mul, hunit, one_mul] at hfull
  exact hfull

/-- Multiplicity-aware finite Blaschke maximum estimate.  If a rational
numerator contains every supplied upper-half-plane root factor, then its norm
is bounded by twice their complete pseudo-hyperbolic distance product. -/
theorem polynomial_div_norm_le_two_mul_multisetRootDistanceProduct
    (zeros : Multiset ℂ) (hzeros : ∀ alpha ∈ zeros, 0 < alpha.im)
    (N D R : ℂ[X])
    (hfactor : N = multisetRootPolynomial zeros * R)
    (hdegree : N.degree ≤ D.degree)
    (hupper : ∀ z : ℂ, 0 ≤ z.im → D.eval z ≠ 0)
    (hboundary : ∀ x : ℝ, ‖N.eval (x : ℂ) / D.eval (x : ℂ)‖ ≤ 2)
    {z : ℂ} (hz : 0 ≤ z.im) :
    ‖N.eval z / D.eval z‖ ≤
      2 * (zeros.map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod := by
  let P₀ := multisetRootPolynomial zeros
  let P₁ := reflectedMultisetRootPolynomial zeros
  let q := P₁ * R
  have hqDegree : q.degree ≤ D.degree := by
    rw [show q.degree = (P₀ * R).degree by
      exact reflectedMultisetRootPolynomial_mul_degree_eq zeros R]
    rw [← hfactor]
    exact hdegree
  have hqBound : ‖q.eval z / D.eval z‖ ≤ 2 := by
    apply polynomial_div_norm_le_of_upperHalfPlane_boundary q D
      hqDegree hupper _ hz
    exact reflectedFactorQuotient_norm_le_of_original_real
      hzeros hfactor (fun x => hupper (x : ℂ) (by simp)) hboundary
  have hP₁ : P₁.eval z ≠ 0 :=
    reflectedMultisetRootPolynomial_eval_ne_zero hzeros hz
  have hD : D.eval z ≠ 0 := hupper z hz
  have hidentity :
      N.eval z / D.eval z =
        (P₀.eval z / P₁.eval z) * (q.eval z / D.eval z) := by
    rw [hfactor]
    dsimp only [P₀, P₁, q]
    rw [eval_mul, eval_mul]
    field_simp [hP₁, hD]
    symm
    exact mul_inv_cancel_right₀ hP₁ _
  have hfactorNorm : ‖P₀.eval z / P₁.eval z‖ =
      (zeros.map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod := by
    rw [← multisetUpperHalfPlaneBlaschke_eq_rootPolynomial_div_reflected]
    exact norm_multisetUpperHalfPlaneBlaschke_eq_product_distance zeros z
  rw [hidentity, norm_mul, hfactorNorm]
  have hprod : 0 ≤ (zeros.map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod := by
    apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨alpha, _, rfl⟩ := Multiset.mem_map.mp hr
    exact norm_nonneg _
  calc
    _ ≤ (zeros.map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod * 2 :=
      mul_le_mul_of_nonneg_left hqBound hprod
    _ = 2 * (zeros.map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod := mul_comm _ _

/-- The explicit common-transform rational difference for `-S` and `B` is
bounded by twice the complete inside-core distance product. -/
theorem finiteCommonUnitDiskTransformDifference_norm_le_two_mul_insideProduct
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {center : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : 0 ≤ w.im) :
    ‖(finiteCommonUnitDiskTransformDifferenceNumerator A tau a).eval w /
        (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval w‖ ≤
      2 * ((insideInfluenceDiskRoots center upperResidual).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance w alpha).prod := by
  let core := insideInfluenceDiskRoots center upperResidual
  have hcore : ∀ alpha ∈ core, 0 < alpha.im := by
    intro alpha halphaCore
    exact halpha alpha (Multiset.mem_of_mem_filter halphaCore)
  have hdiv := insideInfluenceDiskRootPolynomial_dvd_finiteCommonTransformDifference
    (z := center) hA htau hroots halpha a
  change multisetRootPolynomial core ∣
    finiteCommonUnitDiskTransformDifferenceNumerator A tau a at hdiv
  obtain ⟨R, hfactor⟩ := hdiv
  apply polynomial_div_norm_le_two_mul_multisetRootDistanceProduct
    core hcore
    (finiteCommonUnitDiskTransformDifferenceNumerator A tau a)
    (finiteCommonUnitDiskTransformDifferenceDenominator A tau a) R hfactor
    (finiteCommonUnitDiskTransformDifferenceNumerator_degree_le A tau ha)
    (fun z hz =>
      finiteCommonUnitDiskTransformDifferenceDenominator_eval_ne_zero A tau ha hz)
    (finiteCommonUnitDiskTransformDifference_norm_le_two_real A tau ha) hw

/-- Function-level form of the complete inside-core estimate: after a common
disk automorphism, the finite `-S` and `B` values differ by at most twice the
full inside-core pseudo-hyperbolic product. -/
theorem finiteCommonUnitDiskTransform_sub_norm_le_two_mul_insideProduct
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {center : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : 0 < w.im) :
    ‖unitDiskAutomorphism a
          (-lowerRootInnerValue (finiteEPolynomial A tau) w) -
        unitDiskAutomorphism a
          (upperRootBlaschkeValue (finiteEPolynomial A tau) w)‖ ≤
      2 * ((insideInfluenceDiskRoots center upperResidual).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance w alpha).prod := by
  rw [finiteCommonUnitDiskTransformDifference_eq_div_eval A tau ha hw]
  exact finiteCommonUnitDiskTransformDifference_norm_le_two_mul_insideProduct
    hA htau hroots halpha ha hw.le

end

end RiemannGaussian
