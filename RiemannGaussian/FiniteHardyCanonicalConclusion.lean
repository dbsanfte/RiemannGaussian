import RiemannGaussian.FiniteHardyMultipointConclusion
import RiemannGaussian.FiniteRealRootDecomposition

/-!
# Canonical finite multipoint Hardy conclusion

The finite multipoint Hardy argument was originally stated for named real and
upper root multisets together with an exact decomposition hypothesis.  Every
real polynomial already has canonical multisets with precisely those
properties.  This file instantiates the complete finite argument with them.

After this specialization, the pole budget proves that the canonical core is
nonempty.  The influence-disk geometry puts every core root strictly above
the pinned point, making the fixed value `z.im` a common height floor.  A
cardinality-free cost theorem then gives the same closed determinant bound to
singleton and multipoint cores, uniformly across every finite model sharing
the pinned root.
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

/-- Every root in the canonical inside core lies strictly above the pinned
evaluation point.  Thus the fixed height `z.im` is a common lower bound,
uniformly across all finite approximants sharing `z`. -/
theorem canonicalInsideInfluenceDiskRoots_center_im_lt
    {A : ℝ[X]} {z : ℂ} (hz : 0 < z.im) :
    ∀ alpha ∈ canonicalInsideInfluenceDiskRoots A z, z.im < alpha.im := by
  intro alpha halpha
  have halphaPos : 0 < alpha.im :=
    canonicalInsideInfluenceDiskRoots_im_pos alpha halpha
  have halphaInside : alpha ∈
      insideInfluenceDiskRoots z (realPolynomialUpperRootMultiset A) := by
    simpa [canonicalInsideInfluenceDiskRoots] using halpha
  have hinside := (Multiset.mem_filter.mp halphaInside).2
  by_contra hnot
  have hle : alpha.im ≤ z.im := le_of_not_gt hnot
  nlinarith [sq_nonneg (z.re - alpha.re)]

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

/-- Cardinality-free canonical product bound at the fixed, limit-stable
height floor `z.im`.  It covers singleton and multipoint cores uniformly. -/
theorem
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_le_threshold_centerHeight
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod ≤
        pairHyperbolicThreshold eta z.im := by
  apply upperRootPseudoHyperbolicProduct_le_threshold_of_im_sum
    heta hz hz
  · exact canonicalInsideInfluenceDiskRoots_im_pos
  · intro alpha halpha
    exact finiteE_root_ne_upperResidual hA heta hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      alpha (canonicalInsideInfluenceDiskRoots_mem_upperRoots halpha)
  · intro alpha halpha
    exact (canonicalInsideInfluenceDiskRoots_center_im_lt hz alpha halpha).le
  · exact
      canonicalInsideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
        hA heta hz hroot

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

/-- A nonstrict threshold bound for the canonical core product gives the
closed residual-inner bound. -/
theorem norm_lowerRootInnerValue_le_closed_bound_of_canonicalProduct
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hproduct :
      ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod ≤
          pairHyperbolicThreshold eta a0) :
    ‖lowerRootInnerValue (finiteEPolynomial A eta) z‖ ≤
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  let R := ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
    upperHalfPlanePseudoHyperbolicDistance z alpha).prod
  have hR : 0 ≤ R := by
    apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨alpha, _, rfl⟩ := Multiset.mem_map.mp hr
    exact norm_nonneg _
  have hRthreshold : R ≤ pairHyperbolicThreshold eta a0 := by
    simpa [R] using hproduct
  have hROne : R < 1 :=
    hRthreshold.trans_lt (pairHyperbolicThreshold_lt_one heta ha0)
  have hscalar :=
    norm_lowerRootInnerValue_le_two_mul_canonicalInsideProduct_div_one_add_sq
      hA heta.ne' hz hroot (by simpa [R] using hROne)
  exact norm_le_closed_quartet_bound_of_pick_bound heta ha0 hR
    hRthreshold (by simpa [R] using hscalar)

/-- Determinant form of the nonstrict product-to-bound implication. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_closed_bound_of_canonicalProduct
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hproduct :
      ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod ≤
          pairHyperbolicThreshold eta a0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re ≤
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  have hzUpper := finiteE_root_mem_upperRootFactor_roots hA.ne_zero hz hroot
  exact (finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_innerValue_of_mem
      A eta hzUpper).trans
    (norm_lowerRootInnerValue_le_closed_bound_of_canonicalProduct
      hA heta ha0 hz hroot hproduct)

/-- Any strict threshold bound for the complete canonical core product feeds
directly through the sharp scalar terminal step.  This statement is agnostic
about whether the core is a singleton or multipoint. -/
theorem norm_lowerRootInnerValue_lt_closed_bound_of_canonicalProduct
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hproduct :
      ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
          pairHyperbolicThreshold eta a0) :
    ‖lowerRootInnerValue (finiteEPolynomial A eta) z‖ <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  let R := ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
    upperHalfPlanePseudoHyperbolicDistance z alpha).prod
  have hR : 0 ≤ R := by
    apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨alpha, _, rfl⟩ := Multiset.mem_map.mp hr
    exact norm_nonneg _
  have hRthreshold : R < pairHyperbolicThreshold eta a0 := by
    simpa [R] using hproduct
  have hROne : R < 1 :=
    hRthreshold.trans (pairHyperbolicThreshold_lt_one heta ha0)
  have hscalar :=
    norm_lowerRootInnerValue_le_two_mul_canonicalInsideProduct_div_one_add_sq
      hA heta.ne' hz hroot (by simpa [R] using hROne)
  exact norm_lt_closed_quartet_bound_of_pick_bound heta ha0 hR
    hRthreshold (by simpa [R] using hscalar)

/-- Determinant form of the preceding product-to-bound implication. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_canonicalProduct
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hproduct :
      ((canonicalInsideInfluenceDiskRoots A z).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
          pairHyperbolicThreshold eta a0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  have hzUpper := finiteE_root_mem_upperRootFactor_roots hA.ne_zero hz hroot
  exact (finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_innerValue_of_mem
      A eta hzUpper).trans_lt
    (norm_lowerRootInnerValue_lt_closed_bound_of_canonicalProduct
      hA heta ha0 hz hroot hproduct)

/-- Uniform finite residual-inner bound using only the fixed pinned height.
It applies to singleton and multipoint cores alike. -/
theorem norm_lowerRootInnerValue_le_closed_bound_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    ‖lowerRootInnerValue (finiteEPolynomial A eta) z‖ ≤
      eta / Real.sqrt (eta ^ 2 + z.im ^ 2) := by
  apply norm_lowerRootInnerValue_le_closed_bound_of_canonicalProduct
    hA heta hz hz hroot
  exact
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_le_threshold_centerHeight
      hA heta hz hroot

/-- Uniform finite Hardy determinant bound using only the fixed pinned
height. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_closed_bound_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re ≤
      eta / Real.sqrt (eta ^ 2 + z.im ^ 2) := by
  apply
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_closed_bound_of_canonicalProduct
      hA heta hz hz hroot
  exact
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_le_threshold_centerHeight
      hA heta hz hroot

/-- The preceding fixed bound is uniformly separated from one. -/
theorem finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_one_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
      1 := by
  exact
    (finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_closed_bound_of_finiteE_root
      hA heta hz hroot).trans_lt
        (eta_div_sqrt_eta_sq_add_height_sq_lt_one heta hz)

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
  apply norm_lowerRootInnerValue_lt_closed_bound_of_canonicalProduct
    hA heta ha0 hz hroot
  exact
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
      hA heta ha0 hz hroot hcard hminHeight

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
  apply
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_canonicalProduct
      hA heta ha0 hz hroot
  exact
    canonicalInsideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
      hA heta ha0 hz hroot hcard hminHeight

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
