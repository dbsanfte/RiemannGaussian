import RiemannGaussian.FiniteHardyMultipointConclusion
import RiemannGaussian.FiniteRealRootDecomposition

/-!
# Canonical finite multipoint Hardy conclusion

The finite multipoint Hardy argument was originally stated for named real and
upper root multisets together with an exact decomposition hypothesis.  Every
real polynomial already has canonical multisets with precisely those
properties.  This file instantiates the complete finite argument with them.

After this specialization, the pole budget proves that the canonical core is
nonempty.  A finite-stage positive height floor is automatic, so the exact
remaining alternative is a singleton core versus the already-closed
multipoint determinant regime.  Uniform control along an approximating
sequence is deliberately not asserted here.
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

/-- The full negative logarithmic-derivative budget is carried by the
canonical inside influence core. -/
theorem
    canonicalInsideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
      onePairLogDerivativeContribution eta alpha z).sum).im ≤ -1 := by
  exact
    insideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA heta hz hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      (realPolynomialRealRootMultiset_im_eq_zero A)
      (realPolynomialUpperRootMultiset_im_pos A)

/-- At every upper root of a positive finite homotopy, the canonical
influence core contains at least one root occurrence. -/
theorem canonicalInsideInfluenceDiskRoots_card_pos_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    0 < (canonicalInsideInfluenceDiskRoots A z).card := by
  exact insideInfluenceDiskRoots_card_pos_of_finiteE_root
    hA heta hz hroot
    (realPolynomial_roots_eq_real_add_conjugatePairs A)
    (realPolynomialRealRootMultiset_im_eq_zero A)
    (realPolynomialUpperRootMultiset_im_pos A)

/-- The exact remaining cardinality alternative: a canonical influence core
at a finite homotopy root is either a singleton or is in the multipoint
regime. -/
theorem canonicalInsideInfluenceDiskRoots_card_eq_one_or_two_le_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (canonicalInsideInfluenceDiskRoots A z).card = 1 ∨
      2 ≤ (canonicalInsideInfluenceDiskRoots A z).card := by
  have hpos := canonicalInsideInfluenceDiskRoots_card_pos_of_finiteE_root
    hA heta hz hroot
  omega

/-- A finite multiset of positive real values has a common positive lower
bound.  The empty case is included and receives the vacuous bound `1`. -/
theorem exists_pos_lowerBound_of_multiset
    {ι : Type*} (s : Multiset ι) (f : ι → ℝ)
    (hpos : ∀ x ∈ s, 0 < f x) :
    ∃ a0 : ℝ, 0 < a0 ∧ ∀ x ∈ s, a0 ≤ f x := by
  induction s using Multiset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | @cons x s ih =>
      have hx : 0 < f x := hpos x (by simp)
      have hs : ∀ y ∈ s, 0 < f y := by
        intro y hy
        exact hpos y (by simp [hy])
      obtain ⟨a0, ha0, hbound⟩ := ih hs
      refine ⟨min (f x) a0, lt_min hx ha0, ?_⟩
      intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound y hy)

/-- The canonical influence core always has a positive common height floor.
This is a per-polynomial statement; it does not assert uniformity along an
approximating sequence. -/
theorem exists_pos_canonicalInsideInfluenceDiskRoots_im_lowerBound
    (A : ℝ[X]) (z : ℂ) :
    ∃ a0 : ℝ, 0 < a0 ∧
      ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z, a0 ≤ alpha.im := by
  exact exists_pos_lowerBound_of_multiset
    (canonicalInsideInfluenceDiskRoots A z) Complex.im
    canonicalInsideInfluenceDiskRoots_im_pos

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

/-- The scalar closed bound is strictly below one whenever both parameters
are positive. -/
theorem eta_div_sqrt_eta_sq_add_height_sq_lt_one
    {eta a0 : ℝ} (heta : 0 < eta) (ha0 : 0 < a0) :
    eta / Real.sqrt (eta ^ 2 + a0 ^ 2) < 1 := by
  have hsum : 0 < eta ^ 2 + a0 ^ 2 := by positivity
  have hsqrtPos : 0 < Real.sqrt (eta ^ 2 + a0 ^ 2) :=
    Real.sqrt_pos.2 hsum
  apply (div_lt_one hsqrtPos).2
  have hsqrtNonneg : 0 ≤ Real.sqrt (eta ^ 2 + a0 ^ 2) :=
    Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (eta ^ 2 + a0 ^ 2)) ^ 2 =
      eta ^ 2 + a0 ^ 2 := by
    exact Real.sq_sqrt hsum.le
  nlinarith [sq_pos_of_pos ha0]

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

/-- At every upper root of a positive finite homotopy, either the canonical
core is exactly the unresolved singleton case or the complete finite Hardy
determinant has a strict quantitative bound for some positive height floor. -/
theorem
    canonicalInsideCore_card_eq_one_or_exists_finiteHardy_sqrt_det_strict_bound
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (canonicalInsideInfluenceDiskRoots A z).card = 1 ∨
      ∃ a0 : ℝ, 0 < a0 ∧
        Real.sqrt
            (LinearMap.det
              (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
          eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  rcases
      canonicalInsideInfluenceDiskRoots_card_eq_one_or_two_le_of_finiteE_root
        hA heta hz hroot with hsingle | hmulti
  · exact Or.inl hsingle
  · right
    obtain ⟨a0, ha0, hmin⟩ :=
      exists_pos_canonicalInsideInfluenceDiskRoots_im_lowerBound A z
    exact ⟨a0, ha0,
      finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_canonicalInsideCore
        hA heta ha0 hz hroot hmulti hmin⟩

/-- Parameter-free form of the finite cardinality dichotomy: outside the
singleton-core case, the complete finite Hardy determinant is strictly
contractive. -/
theorem canonicalInsideCore_card_eq_one_or_finiteHardy_sqrt_det_lt_one
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (canonicalInsideInfluenceDiskRoots A z).card = 1 ∨
      Real.sqrt
          (LinearMap.det
            (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
        1 := by
  rcases
      canonicalInsideCore_card_eq_one_or_exists_finiteHardy_sqrt_det_strict_bound
        hA heta hz hroot with hsingle | ⟨a0, ha0, hdet⟩
  · exact Or.inl hsingle
  · exact Or.inr
      (hdet.trans (eta_div_sqrt_eta_sq_add_height_sq_lt_one heta ha0))

end

end RiemannGaussian
