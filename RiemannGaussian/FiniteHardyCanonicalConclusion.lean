import RiemannGaussian.FiniteHardyMultipointConclusion
import RiemannGaussian.FiniteRealRootDecomposition

/-!
# Canonical finite multipoint Hardy conclusion

The finite multipoint Hardy argument was originally stated for named real and
upper root multisets together with an exact decomposition hypothesis.  Every
real polynomial already has canonical multisets with precisely those
properties.  This file instantiates the complete finite argument with them.

After this specialization, the only root-geometric inputs left are the
quantitative ones: the canonical influence core must contain at least two
roots and those roots must share a positive height lower bound.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- The canonical multiplicity-aware upper-root influence core of a real
polynomial at an upper-half-plane evaluation point. -/
def canonicalInsideInfluenceDiskRoots (A : ℝ[X]) (z : ℂ) : Multiset ℂ :=
  insideInfluenceDiskRoots z (realPolynomialUpperRootMultiset A)

/-- Every occurrence in the canonical influence core is an upper-half-plane
root of the base polynomial. -/
theorem canonicalInsideInfluenceDiskRoots_mem_upperRoots
    {A : ℝ[X]} {z alpha : ℂ}
    (halpha : alpha ∈ canonicalInsideInfluenceDiskRoots A z) :
    alpha ∈ realPolynomialUpperRootMultiset A := by
  exact Multiset.mem_of_mem_filter halpha

/-- Every occurrence in the canonical influence core has positive imaginary
part. -/
theorem canonicalInsideInfluenceDiskRoots_im_pos
    {A : ℝ[X]} {z : ℂ} :
    ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z, 0 < alpha.im := by
  intro alpha halpha
  exact realPolynomialUpperRootMultiset_im_pos A alpha
    (canonicalInsideInfluenceDiskRoots_mem_upperRoots halpha)

/-- The canonical influence core has no repeated occurrences when the base
polynomial is separable. -/
theorem canonicalInsideInfluenceDiskRoots_nodup
    {A : ℝ[X]} (hA : A.Separable) (z : ℂ) :
    (canonicalInsideInfluenceDiskRoots A z).Nodup := by
  exact (realPolynomialUpperRootMultiset_nodup hA).filter _

/-- Canonical form of the strict complete-core pseudo-hyperbolic product
bound at a root of the finite homotopy. -/
theorem
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hcard : 2 ≤ (canonicalInsideInfluenceDiskRoots A z).card)
    (hminHeight : ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z,
      a0 ≤ alpha.im) :
    ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
        pairHyperbolicThreshold eta a0 := by
  exact
    insideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
      hA heta ha0 hz hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      (realPolynomialRealRootMultiset_im_eq_zero A)
      (realPolynomialUpperRootMultiset_im_pos A)
      hcard hminHeight

/-- Canonical form of the sharp common-transform bound for the residual inner
value at an upper root of the finite homotopy. -/
theorem norm_lowerRootInnerValue_le_two_mul_canonicalInsideProduct_div_one_add_sq
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A tau).eval z = 0)
    (hproductOne :
      ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod < 1) :
    ‖lowerRootInnerValue (finiteEPolynomial A tau) z‖ ≤
      2 * ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
          upperHalfPlanePseudoHyperbolicDistance z alpha).prod /
        (1 + ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
          upperHalfPlanePseudoHyperbolicDistance z alpha).prod ^ 2) := by
  exact norm_lowerRootInnerValue_le_two_mul_insideProduct_div_one_add_sq
    hA htau hz hroot
    (realPolynomial_roots_eq_real_add_conjugatePairs A)
    (realPolynomialUpperRootMultiset_im_pos A) hproductOne

/-- Canonical end-to-end strict residual-inner bound.  Its only root data are
the size and common positive height of the canonical influence core. -/
theorem norm_lowerRootInnerValue_lt_closed_bound_of_canonicalInsideCore
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hcard : 2 ≤ (canonicalInsideInfluenceDiskRoots A z).card)
    (hminHeight : ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z,
      a0 ≤ alpha.im) :
    ‖lowerRootInnerValue (finiteEPolynomial A eta) z‖ <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  exact norm_lowerRootInnerValue_lt_closed_bound_of_insideCore
    hA heta ha0 hz hroot
    (realPolynomial_roots_eq_real_add_conjugatePairs A)
    (realPolynomialRealRootMultiset_im_eq_zero A)
    (realPolynomialUpperRootMultiset_im_pos A)
    hcard hminHeight

/-- Canonical end-to-end finite Hardy determinant bound.  No arbitrary root
enumeration or qualitative root-decomposition premise remains. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_canonicalInsideCore
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hcard : 2 ≤ (canonicalInsideInfluenceDiskRoots A z).card)
    (hminHeight : ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z,
      a0 ≤ alpha.im) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_insideCore
      hA heta ha0 hz hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      (realPolynomialRealRootMultiset_im_eq_zero A)
      (realPolynomialUpperRootMultiset_im_pos A)
      hcard hminHeight

end

end RiemannGaussian
