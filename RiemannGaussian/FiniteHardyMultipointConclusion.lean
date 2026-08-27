import RiemannGaussian.FiniteHardyMultipointFactor
import RiemannGaussian.SymmetricQuartetPickDefect

/-!
# End-to-end finite multipoint Hardy conclusion

This file feeds the complete inside-core transform bound through the radial
disk-automorphism identity and then through the strict hyperbolic-energy
threshold.  The result is a strict bound for both the residual inner value at
the candidate root and the unconditional confluent Hardy determinant.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- If the complete inside-core distance product is below one, the checked
common-transform estimate gives the sharp Cayley-radius bound for the residual
inner value at an upper root of the finite homotopy. -/
theorem norm_lowerRootInnerValue_le_two_mul_insideProduct_div_one_add_sq
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A tau).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (hproductOne :
      ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
        upperHalfPlanePseudoHyperbolicDistance z alpha).prod < 1) :
    ‖lowerRootInnerValue (finiteEPolynomial A tau) z‖ ≤
      2 * ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
          upperHalfPlanePseudoHyperbolicDistance z alpha).prod /
        (1 + ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
          upperHalfPlanePseudoHyperbolicDistance z alpha).prod ^ 2) := by
  let p := finiteEPolynomial A tau
  let R := ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
    upperHalfPlanePseudoHyperbolicDistance z alpha).prod
  have hR : 0 ≤ R := by
    apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨alpha, _, rfl⟩ := Multiset.mem_map.mp hr
    exact norm_nonneg _
  have hROne : R < 1 := by simpa [R] using hproductOne
  have hzUpper : z ∈ (upperRootFactor p).roots := by
    exact finiteE_root_mem_upperRootFactor_roots hA.ne_zero hz hroot
  have hUzero : (upperRootFactor p).eval z = 0 :=
    (Polynomial.mem_roots (upperRootFactor_ne_zero p)).mp hzUpper
  have hBzero : upperRootBlaschkeValue p z = 0 := by
    simp [upperRootBlaschkeValue, hUzero]
  have hf : ‖-lowerRootInnerValue p z‖ ≤ 1 := by
    rw [norm_neg]
    exact norm_lowerRootInnerValue_le_one p hz
  by_cases hs : -lowerRootInnerValue p z = 0
  · have hs' : lowerRootInnerValue p z = 0 := neg_eq_zero.mp hs
    rw [show lowerRootInnerValue (finiteEPolynomial A tau) z = 0 by
      simpa [p] using hs', norm_zero]
    positivity
  · let a := radialDiskPoint R (-lowerRootInnerValue p z)
    have haNorm : ‖a‖ = R := norm_radialDiskPoint hR hs
    have ha : ‖a‖ < 1 := haNorm.trans_lt hROne
    have hcommon := finiteCommonUnitDiskTransform_sub_norm_le_two_mul_insideProduct
      (center := z) (a := a) (w := z) hA htau hroots halpha ha hz
    have hcommon' :
        ‖unitDiskAutomorphism a (-lowerRootInnerValue p z) -
          unitDiskAutomorphism a 0‖ ≤ 2 * R := by
      simpa only [p, R, hBzero] using hcommon
    have hscalar := norm_le_two_mul_div_one_add_sq_of_radialAutomorphism_sub
      (s := -lowerRootInnerValue p z) (r := R) hR hROne hf
      (by simpa only [a] using hcommon')
    simpa [p, R] using hscalar

/-- The finite pole equation and the complete inside-core estimate give the
strict closed bound for the residual inner value. -/
theorem norm_lowerRootInnerValue_lt_closed_bound_of_insideCore
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
    ‖lowerRootInnerValue (finiteEPolynomial A eta) z‖ <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  let R := ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
    upperHalfPlanePseudoHyperbolicDistance z alpha).prod
  have hR : 0 ≤ R := by
    apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨alpha, _, rfl⟩ := Multiset.mem_map.mp hr
    exact norm_nonneg _
  have hthreshold :=
    insideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
      hA heta ha0 hz hroot hroots hreal halpha hcard hminHeight
  have hRthreshold : R < pairHyperbolicThreshold eta a0 := by
    simpa [R] using hthreshold
  have hROne : R < 1 := by
    exact hRthreshold.trans (pairHyperbolicThreshold_lt_one heta ha0)
  have hscalar :=
    norm_lowerRootInnerValue_le_two_mul_insideProduct_div_one_add_sq
      hA heta.ne' hz hroot hroots halpha (by simpa [R] using hROne)
  exact norm_lt_closed_quartet_bound_of_pick_bound heta ha0 hR
    hRthreshold (by simpa [R] using hscalar)

/-- End-to-end collective finite Hardy bound.  The actual confluent
complement Gram determinant is strictly below the exact one-pair threshold
whenever the influence core contains at least two roots and has the stated
positive common height lower bound. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_closed_bound_of_insideCore
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
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A eta).toLinearMap).re <
      eta / Real.sqrt (eta ^ 2 + a0 ^ 2) := by
  have hzUpper := finiteE_root_mem_upperRootFactor_roots hA.ne_zero hz hroot
  exact (finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_innerValue_of_mem
      A eta hzUpper).trans_lt
    (norm_lowerRootInnerValue_lt_closed_bound_of_insideCore
      hA heta ha0 hz hroot hroots hreal halpha hcard hminHeight)

end

end RiemannGaussian
