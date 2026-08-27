import RiemannGaussian.FiniteHardyCanonicalConclusion

/-!
# The singleton finite Hardy frontier

The canonical pole budget leaves one finite cardinality exception to the
strict multipoint argument: the inside influence core may contain exactly one
root.  This file analyzes that exception.

The universal one-pair energy inequality is strict unless the pair root and
the pinned homotopy root have the same real part.  Consequently a singleton
core still yields the complete strict Hardy determinant bound whenever its
unique root is not vertically aligned.  The only surviving finite exception
is therefore an explicitly named, vertically aligned singleton.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- A singleton canonical core has a unique named root carrying all the
canonical membership, geometry, and pole-budget data. -/
theorem exists_canonicalInsideCore_singleton_root_data
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hsingle : (canonicalInsideInfluenceDiskRoots A z).card = 1) :
    ∃ alpha : ℂ,
      canonicalInsideInfluenceDiskRoots A z = {alpha} ∧
      alpha ∈ realPolynomialUpperRootMultiset A ∧
      0 < alpha.im ∧ z ≠ alpha ∧
      (z.re - alpha.re) ^ 2 + z.im ^ 2 < alpha.im ^ 2 ∧
      (onePairLogDerivativeContribution eta alpha z).im ≤ -1 := by
  obtain ⟨alpha, hcore⟩ := Multiset.card_eq_one.mp hsingle
  have halphaCore : alpha ∈ canonicalInsideInfluenceDiskRoots A z := by
    rw [hcore]
    simp
  have halphaUpper : alpha ∈ realPolynomialUpperRootMultiset A :=
    canonicalInsideInfluenceDiskRoots_mem_upperRoots halphaCore
  have halphaPos : 0 < alpha.im :=
    realPolynomialUpperRootMultiset_im_pos A alpha halphaUpper
  have hne : z ≠ alpha :=
    finiteE_root_ne_upperResidual hA heta hroot
      (realPolynomial_roots_eq_real_add_conjugatePairs A)
      alpha halphaUpper
  have hinside :
      (z.re - alpha.re) ^ 2 + z.im ^ 2 < alpha.im ^ 2 := by
    change alpha ∈ insideInfluenceDiskRoots z
      (realPolynomialUpperRootMultiset A) at halphaCore
    exact (Multiset.mem_filter.mp halphaCore).2
  have hbudget :=
    canonicalInsideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA heta hz hroot
  rw [hcore] at hbudget
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hbudget
  exact ⟨alpha, hcore, halphaUpper, halphaPos, hne, hinside, hbudget⟩

/-- If the unique canonical core root is not vertically aligned with the
pinned homotopy root, its pseudo-hyperbolic radius lies strictly below the
exact one-pair threshold. -/
theorem canonicalInsideCore_singleton_radius_lt_threshold_of_re_ne
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z alpha : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hcore : canonicalInsideInfluenceDiskRoots A z = {alpha})
    (hre : z.re ≠ alpha.re) :
    upperHalfPlanePseudoHyperbolicDistance z alpha <
      pairHyperbolicThreshold eta alpha.im := by
  have halphaCore : alpha ∈ canonicalInsideInfluenceDiskRoots A z := by
    rw [hcore]
    simp
  have halphaPos : 0 < alpha.im :=
    canonicalInsideInfluenceDiskRoots_im_pos alpha halphaCore
  have henergy :=
    onePairLogDerivativeContribution_im_gt_neg_cost_complex_of_re_ne
      heta hz halphaPos hre
  have hbudget :=
    canonicalInsideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA heta hz hroot
  rw [hcore] at hbudget
  simp only [Multiset.map_singleton, Multiset.sum_singleton] at hbudget
  apply radius_lt_pairHyperbolicThreshold_of_one_lt_cost heta halphaPos
  linarith

/-- A nonaligned singleton core satisfies the same strict finite Hardy
determinant bound as the multipoint core, with its unique root height as the
height parameter. -/
theorem
    finiteHardy_sqrt_det_lt_closed_bound_of_canonicalInsideCore_singleton_re_ne
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z alpha : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hcore : canonicalInsideInfluenceDiskRoots A z = {alpha})
    (hre : z.re ≠ alpha.re) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
      eta / Real.sqrt (eta ^ 2 + alpha.im ^ 2) := by
  have halphaCore : alpha ∈ canonicalInsideInfluenceDiskRoots A z := by
    rw [hcore]
    simp
  have halphaPos : 0 < alpha.im :=
    canonicalInsideInfluenceDiskRoots_im_pos alpha halphaCore
  apply
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_canonicalProduct
      hA heta halphaPos hz hroot
  have hradius := canonicalInsideCore_singleton_radius_lt_threshold_of_re_ne
    hA heta hz hroot hcore hre
  rw [hcore]
  simpa using hradius

/-- Refined finite alternative.  At any pinned upper homotopy root, either
the canonical core is a vertically aligned singleton or the complete Hardy
determinant has a strict quantitative bound. -/
theorem
    exists_aligned_canonicalInsideCore_singleton_or_finiteHardy_strict_bound
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (∃ alpha : ℂ,
        canonicalInsideInfluenceDiskRoots A z = {alpha} ∧
          alpha.re = z.re) ∨
      ∃ a0 : ℝ, 0 < a0 ∧
        Real.sqrt
            (LinearMap.det
              (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
          eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  rcases
      canonicalInsideCore_card_eq_one_or_exists_finiteHardy_sqrt_det_strict_bound
        hA heta hz hroot with hsingle | hstrict
  · obtain ⟨alpha, hcore⟩ := Multiset.card_eq_one.mp hsingle
    by_cases haligned : alpha.re = z.re
    · exact Or.inl ⟨alpha, hcore, haligned⟩
    · right
      have halphaCore : alpha ∈ canonicalInsideInfluenceDiskRoots A z := by
        rw [hcore]
        simp
      have halphaPos : 0 < alpha.im :=
        canonicalInsideInfluenceDiskRoots_im_pos alpha halphaCore
      exact ⟨alpha.im, halphaPos,
        finiteHardy_sqrt_det_lt_closed_bound_of_canonicalInsideCore_singleton_re_ne
          hA heta hz hroot hcore (Ne.symm haligned)⟩
  · exact Or.inr hstrict

/-- Parameter-free form of the refined alternative: the complete finite
Hardy determinant is strictly contractive unless the canonical core is a
vertically aligned singleton. -/
theorem
    exists_aligned_canonicalInsideCore_singleton_or_finiteHardy_sqrt_det_lt_one
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0) :
    (∃ alpha : ℂ,
        canonicalInsideInfluenceDiskRoots A z = {alpha} ∧
          alpha.re = z.re) ∨
      Real.sqrt
          (LinearMap.det
            (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
        1 := by
  rcases
      exists_aligned_canonicalInsideCore_singleton_or_finiteHardy_strict_bound
        hA heta hz hroot with haligned | ⟨a0, ha0, hdet⟩
  · exact Or.inl haligned
  · exact Or.inr
      (hdet.trans (eta_div_sqrt_eta_sq_add_height_sq_lt_one heta ha0))

end

end RiemannGaussian
