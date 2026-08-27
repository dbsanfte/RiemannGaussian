import RiemannGaussian.FiniteHardyRootPickBridge
import RiemannGaussian.SymmetricQuartetFiniteRoots

/-!
# Inside-core interpolation bridge for the finite Hardy model

This file turns the root-multiset decomposition used by the weighted
hyperbolic-energy theorem into the exact interpolation and Pick data needed
by the finite Hardy argument.  All statements retain multiset membership;
no root occurrence is discarded.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-- Every member of the named upper residual multiset is a genuine zero of
the base polynomial.  This is extracted from the complete root-multiset
decomposition, rather than added as a separate hypothesis. -/
theorem base_eval_eq_zero_of_mem_upperResidual
    {A : ℝ[X]} (hA : A.Separable)
    {realResidual upperResidual : Multiset ℂ}
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    {alpha : ℂ} (halpha : alpha ∈ upperResidual) :
    A.eval₂ Complex.ofRealHom alpha = 0 := by
  have halphaRoots : alpha ∈ (A.map Complex.ofRealHom).roots := by
    rw [hroots]
    simp [conjugatePairRootMultiset, halpha]
  have halphaIsRoot :=
    (Polynomial.mem_roots (Polynomial.map_ne_zero hA.ne_zero)).mp halphaRoots
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using halphaIsRoot

/-- A positive-imaginary zero of the finite homotopy is a member of its
upper-root factor multiset, with its root occurrence retained. -/
theorem finiteE_root_mem_upperRootFactor_roots
    {A : ℝ[X]} (hA : A ≠ 0) {tau : ℝ} {z : ℂ}
    (hz : 0 < z.im) (hroot : (finiteEPolynomial A tau).eval z = 0) :
    z ∈ (upperRootFactor (finiteEPolynomial A tau)).roots := by
  rw [upperRootFactor_roots, Multiset.mem_filter]
  exact ⟨(Polynomial.mem_roots
    (finiteEPolynomial_ne_zero hA tau)).mpr hroot, hz⟩

/-- Every member of the influence-disk core supplies the exact interpolation
identity and the two root-level Schwarz--Pick inequalities.  This is the
multiplicity-aware family of local data that the missing collective argument
must consume. -/
theorem insideInfluenceDiskRoots_finiteRoot_schwarzPick_data
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A tau).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im) :
    ∀ alpha ∈ insideInfluenceDiskRoots z upperResidual,
      finiteInnerValue A tau alpha = -finiteBlaschkeValue A tau alpha ∧
      ‖finiteBlaschkeValue A tau alpha‖ ≤
          upperHalfPlanePseudoHyperbolicDistance z alpha ∧
      ‖(finiteInnerValue A tau z + finiteBlaschkeValue A tau alpha) /
          (1 + finiteInnerValue A tau z *
            starRingEnd ℂ (finiteBlaschkeValue A tau alpha))‖ ≤
        upperHalfPlanePseudoHyperbolicDistance z alpha := by
  intro alpha halphaInside
  have halphaUpper : alpha ∈ upperResidual :=
    Multiset.mem_of_mem_filter halphaInside
  have halphaIm : 0 < alpha.im := halpha alpha halphaUpper
  have halphaRoot : A.eval₂ Complex.ofRealHom alpha = 0 :=
    base_eval_eq_zero_of_mem_upperResidual hA hroots halphaUpper
  have hzUpper := finiteE_root_mem_upperRootFactor_roots
    hA.ne_zero hz hroot
  have hdata := finiteRoot_residualBlaschke_schwarzPick_data
    hA htau hzUpper halphaIm halphaRoot
  exact ⟨finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
      hA htau halphaRoot, hdata.1, hdata.2⟩

/-- The complete Hardy determinant obeys the checked one-root Pick bound at
every member of the influence-disk core.  The universal quantifier is the
interface to a future collective comparison; it does not replace the core
product by a selected factor. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_each_insideRootPickBound
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A tau).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im) :
    ∀ alpha ∈ insideInfluenceDiskRoots z upperResidual,
      Real.sqrt
          (LinearMap.det
            (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap).re ≤
        2 * upperHalfPlanePseudoHyperbolicDistance z alpha /
          (1 + upperHalfPlanePseudoHyperbolicDistance z alpha ^ 2) := by
  intro alpha halphaInside
  have halphaUpper : alpha ∈ upperResidual :=
    Multiset.mem_of_mem_filter halphaInside
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_singleBaseRootPickBound
      hA htau
      (finiteE_root_mem_upperRootFactor_roots hA.ne_zero hz hroot)
      (halpha alpha halphaUpper)
      (base_eval_eq_zero_of_mem_upperResidual hA hroots halphaUpper)

/-- End-to-end finite interface at the collective frontier.  The logarithmic-
derivative pole equation supplies a strict bound for the complete core
radius product, while the same core supplies all interpolation and
Schwarz--Pick data.  The two conclusions are kept distinct: the theorem does
not assume that the radius product is a Hardy determinant product. -/
theorem finiteE_insideInfluenceDisk_product_and_schwarzPick_data
    {A : ℝ[X]} (hA : A.Separable) {eta a0 : ℝ} {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (heta : 0 < eta) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (hcard : 2 ≤ (insideInfluenceDiskRoots z upperResidual).card)
    (hminHeight : ∀ alpha ∈ insideInfluenceDiskRoots z upperResidual,
      a0 ≤ alpha.im) :
    ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
        pairHyperbolicThreshold eta a0 ∧
      ∀ alpha ∈ insideInfluenceDiskRoots z upperResidual,
        finiteInnerValue A eta alpha = -finiteBlaschkeValue A eta alpha ∧
        ‖finiteBlaschkeValue A eta alpha‖ ≤
            upperHalfPlanePseudoHyperbolicDistance z alpha ∧
        ‖(finiteInnerValue A eta z + finiteBlaschkeValue A eta alpha) /
            (1 + finiteInnerValue A eta z *
              starRingEnd ℂ (finiteBlaschkeValue A eta alpha))‖ ≤
          upperHalfPlanePseudoHyperbolicDistance z alpha := by
  constructor
  · exact
      insideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
        hA heta ha0 hz hroot hroots hreal halpha hcard hminHeight
  · exact insideInfluenceDiskRoots_finiteRoot_schwarzPick_data
      hA heta.ne' hz hroot hroots halpha

end

end RiemannGaussian
