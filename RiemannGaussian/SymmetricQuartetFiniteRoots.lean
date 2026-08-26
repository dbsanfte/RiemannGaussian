import RiemannGaussian.SymmetricQuartetHardyMetric

/-!
# Exact finite-root expansion for an isolated symmetric quartet

This file proves the polynomial logarithmic-derivative formula as a sum over
all roots with multiplicity.  It then specializes an even separable quartic
with one named off-axis root to its four forced symmetric roots.  At the
natural weight `m = eta`, the literal quartet background is exactly zero, so
the direct finite Hardy determinant estimate has no background hypothesis.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The four distinct locations of a symmetric off-axis quartet, represented
as a finset so sums do not depend on an ordering choice. -/
def symmetricQuartetRootFinset (tau a : ℝ) : Finset ℂ :=
  {symmetricPickAlphaPlus tau a,
    starRingEnd ℂ (symmetricPickAlphaPlus tau a),
    symmetricPickAlphaMinus tau a,
    starRingEnd ℂ (symmetricPickAlphaMinus tau a)}

/-- A genuine off-axis quartet has four distinct points. -/
theorem symmetricQuartetRootFinset_card
    {tau a : ℝ} (htau : tau ≠ 0) (ha : 0 < a) :
    (symmetricQuartetRootFinset tau a).card = 4 := by
  have hPlusMinus :
      symmetricPickAlphaPlus tau a ≠ symmetricPickAlphaMinus tau a := by
    simpa [symmetricPickPole, symmetricPickAlphaPlus,
      symmetricPickAlphaMinus] using
        symmetricPickPole_ne_reflected_of_ne_zero (v := a) htau
  have hUpperLowerPlus : symmetricPickAlphaPlus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, upperHalfPlanePoint] at him
    linarith
  have hUpperLowerCross : symmetricPickAlphaPlus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
      upperHalfPlanePoint] at him
    linarith
  have hLowerPlusUpperMinus :
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) ≠
        symmetricPickAlphaMinus tau a := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
      upperHalfPlanePoint] at him
    linarith
  have hLowerPlusLowerMinus :
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) ≠
        starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    exact fun h => hPlusMinus ((starRingEnd ℂ).injective h)
  have hUpperMinusLowerMinus : symmetricPickAlphaMinus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaMinus, upperHalfPlanePoint] at him
    linarith
  simp [symmetricQuartetRootFinset, hPlusMinus, hUpperLowerPlus,
    hUpperLowerCross, hLowerPlusUpperMinus, hLowerPlusLowerMinus,
    hUpperMinusLowerMinus]

/-- Away from the zeros of `A`, its scaled negative logarithmic derivative is
the exact sum of the simple fractions attached to every complex root, counted
with multiplicity. -/
theorem finiteNegativeLogDerivativeValue_eq_root_sum
    {A : ℝ[X]} {η : ℝ} {z : ℂ}
    (hAz : A.eval₂ Complex.ofRealHom z ≠ 0) :
    finiteNegativeLogDerivativeValue A η z =
      ((A.map Complex.ofRealHom).roots.map fun w =>
        -(η : ℂ) / (z - w)).sum := by
  let p := A.map Complex.ofRealHom
  have hpz : p.eval z ≠ 0 := by
    simpa [p, Polynomial.eval_map] using hAz
  have hlog := (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz
  unfold finiteNegativeLogDerivativeValue
  rw [← Polynomial.eval_map, ← Polynomial.eval_map,
    ← Polynomial.derivative_map]
  change -(η : ℂ) * p.derivative.eval z / p.eval z = _
  calc
    -(η : ℂ) * p.derivative.eval z / p.eval z =
        -(η : ℂ) * (p.derivative.eval z / p.eval z) := by ring
    _ = -(η : ℂ) *
        (p.roots.map fun w => 1 / (z - w)).sum := by rw [hlog]
    _ = (p.roots.map fun w => -(η : ℂ) / (z - w)).sum := by
      simpa [div_eq_mul_inv] using
        (Multiset.sum_map_mul_left
          (s := p.roots) (a := -(η : ℂ))
          (f := fun w => 1 / (z - w))).symm

/-- The complete root multiset of an even separable quartic with one genuine
off-axis upper root is exactly the corresponding symmetric quartet. -/
theorem realQuartic_mapped_roots_eq_symmetricQuartet
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4) {tau a : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0) :
    (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val := by
  have hAlphaNegConj :
      negConj (symmetricPickAlphaPlus tau a) =
        symmetricPickAlphaMinus tau a := by
    simp [negConj, symmetricPickAlphaPlus, symmetricPickAlphaMinus]
  have hAMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaMinus tau a) = 0 := by
    rw [← hAlphaNegConj,
      realPolynomial_eval₂_negConj_eq_conj_of_even hEven, hAPlus, map_zero]
  have hConjPlus : A.eval₂ Complex.ofRealHom
      (starRingEnd ℂ (symmetricPickAlphaPlus tau a)) = 0 := by
    change aeval (starRingEnd ℂ (symmetricPickAlphaPlus tau a)) A = 0
    rw [Polynomial.aeval_conj]
    change starRingEnd ℂ
      (A.eval₂ Complex.ofRealHom (symmetricPickAlphaPlus tau a)) = 0
    rw [hAPlus, map_zero]
  have hConjMinus : A.eval₂ Complex.ofRealHom
      (starRingEnd ℂ (symmetricPickAlphaMinus tau a)) = 0 := by
    change aeval (starRingEnd ℂ (symmetricPickAlphaMinus tau a)) A = 0
    rw [Polynomial.aeval_conj]
    change starRingEnd ℂ
      (A.eval₂ Complex.ofRealHom (symmetricPickAlphaMinus tau a)) = 0
    rw [hAMinus, map_zero]
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro w hw
    simp only [symmetricQuartetRootFinset, Finset.mem_insert,
      Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simpa [Polynomial.eval_map] using hAPlus
    · simpa [Polynomial.eval_map] using hConjPlus
    · simpa [Polynomial.eval_map] using hAMinus
    · simpa [Polynomial.eval_map] using hConjMinus
  · rw [Polynomial.natDegree_map, hdegreeA,
      symmetricQuartetRootFinset_card htau ha]
  · exact Polynomial.map_ne_zero hA.ne_zero

/-- Evaluation of a function over the quartet finset expands to its four
named values in the chosen presentation order. -/
theorem symmetricQuartetRootFinset_sum
    {tau a : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (f : ℂ → ℂ) :
    ((symmetricQuartetRootFinset tau a).val.map f).sum =
      f (symmetricPickAlphaPlus tau a) +
        f (starRingEnd ℂ (symmetricPickAlphaPlus tau a)) +
      f (symmetricPickAlphaMinus tau a) +
        f (starRingEnd ℂ (symmetricPickAlphaMinus tau a)) := by
  have hPlusMinus :
      symmetricPickAlphaPlus tau a ≠ symmetricPickAlphaMinus tau a := by
    simpa [symmetricPickPole, symmetricPickAlphaPlus,
      symmetricPickAlphaMinus] using
        symmetricPickPole_ne_reflected_of_ne_zero (v := a) htau
  have hUpperLowerPlus : symmetricPickAlphaPlus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, upperHalfPlanePoint] at him
    linarith
  have hUpperLowerCross : symmetricPickAlphaPlus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
      upperHalfPlanePoint] at him
    linarith
  have hLowerPlusUpperMinus :
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) ≠
        symmetricPickAlphaMinus tau a := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaPlus, symmetricPickAlphaMinus,
      upperHalfPlanePoint] at him
    linarith
  have hLowerPlusLowerMinus :
      starRingEnd ℂ (symmetricPickAlphaPlus tau a) ≠
        starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    exact fun h => hPlusMinus ((starRingEnd ℂ).injective h)
  have hUpperMinusLowerMinus : symmetricPickAlphaMinus tau a ≠
      starRingEnd ℂ (symmetricPickAlphaMinus tau a) := by
    intro h
    have him := congrArg Complex.im h
    simp [symmetricPickAlphaMinus, upperHalfPlanePoint] at him
    linarith
  change (∑ w ∈ symmetricQuartetRootFinset tau a, f w) = _
  simp [symmetricQuartetRootFinset, hPlusMinus, hUpperLowerPlus,
    hUpperLowerCross, hLowerPlusUpperMinus, hLowerPlusLowerMinus,
    hUpperMinusLowerMinus]
  ring

/-- For an isolated even quartic, the complete finite logarithmic derivative
is exactly its symmetric-quartet contribution at the natural root weight. -/
theorem finiteNegativeLogDerivativeValue_eq_symmetricQuartet_of_quartic
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4) {η tau a : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    {z : ℂ} (hAz : A.eval₂ Complex.ofRealHom z ≠ 0) :
    finiteNegativeLogDerivativeValue A η z =
      symmetricQuartetLogDerivativeContribution η tau a z := by
  rw [finiteNegativeLogDerivativeValue_eq_root_sum hAz,
    realQuartic_mapped_roots_eq_symmetricQuartet
      hA hEven hdegreeA htau ha hAPlus]
  rw [symmetricQuartetRootFinset_sum htau ha]
  simp [symmetricQuartetLogDerivativeContribution,
    onePairLogDerivativeContribution, symmetricPickAlphaPlus,
    symmetricPickAlphaMinus]
  ring

/-- At the natural weight `m = eta`, an isolated even quartic has identically
zero literal quartet background away from its roots. -/
theorem finiteQuartetLogDerivativeBackground_eq_zero_of_even_quartic
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4) {η tau a : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    {z : ℂ} (hAz : A.eval₂ Complex.ofRealHom z ≠ 0) :
    finiteQuartetLogDerivativeBackground A η η tau a z = 0 := by
  unfold finiteQuartetLogDerivativeBackground
  rw [finiteNegativeLogDerivativeValue_eq_symmetricQuartet_of_quartic
    hA hEven hdegreeA htau ha hAPlus hAz]
  ring

/-- Hole-free isolated-quartet determinant estimate.  At the natural weight,
the exact finite root expansion discharges the final background-sign
hypothesis of the direct finite frontier. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_quartic_E_root_selfWeight
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4)
    {η tau a x v : ℝ}
    (hη : 0 < η) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hroot : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      η ^ 2 / (η ^ 2 + a ^ 2) := by
  have hAPole : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA hη.ne' hroot
  have hbackground : 0 ≤
      (finiteQuartetLogDerivativeBackground A η η tau a
        (symmetricPickPole x v)).im := by
    rw [finiteQuartetLogDerivativeBackground_eq_zero_of_even_quartic
      hA hEven hdegreeA htau ha hAPlus hAPole]
    simp
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_quartic_E_root
      hA hEven hdegreeA hη hη htau ha hv hx hAPlus hroot hbackground

/-! ## Larger finite models with a real residual divisor -/

/-- If the complete root multiset splits into the named quartet plus a
residual multiset, the literal quartet background is exactly the root sum over
that residual, away from zeros of `A`. -/
theorem finiteQuartetLogDerivativeBackground_eq_residual_root_sum
    {A : ℝ[X]} {η tau a : ℝ} {residual : Multiset ℂ} {z : ℂ}
    (htau : tau ≠ 0) (ha : 0 < a)
    (hAz : A.eval₂ Complex.ofRealHom z ≠ 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val + residual) :
    finiteQuartetLogDerivativeBackground A η η tau a z =
      (residual.map fun w => -(η : ℂ) / (z - w)).sum := by
  unfold finiteQuartetLogDerivativeBackground
  rw [finiteNegativeLogDerivativeValue_eq_root_sum hAz, hroots,
    Multiset.map_add, Multiset.sum_add,
    symmetricQuartetRootFinset_sum htau ha]
  simp [symmetricQuartetLogDerivativeContribution,
    onePairLogDerivativeContribution, symmetricPickAlphaPlus,
    symmetricPickAlphaMinus]
  ring

/-- A nonnegative-weight root on the real axis contributes nonnegative
imaginary part to the negative logarithmic derivative in the upper half-plane.
-/
theorem rootLogDerivativeContribution_im_nonneg_of_real
    {η : ℝ} (hη : 0 ≤ η) {z w : ℂ} (hz : 0 < z.im) (hw : w.im = 0) :
    0 ≤ (-(η : ℂ) / (z - w)).im := by
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, neg_zero, zero_mul,
    zero_div, zero_sub]
  rw [hw, sub_zero]
  have hnorm : 0 ≤ Complex.normSq (z - w) := Complex.normSq_nonneg _
  simpa only [neg_div, neg_mul, neg_neg] using
    div_nonneg (mul_nonneg hη hz.le) hnorm

/-- A finite multiset of real residual roots has nonnegative total imaginary
logarithmic-derivative contribution throughout the upper half-plane. -/
theorem residualRootLogDerivativeSum_im_nonneg_of_real
    {η : ℝ} (hη : 0 ≤ η) {residual : Multiset ℂ} {z : ℂ}
    (hz : 0 < z.im) (hreal : ∀ w ∈ residual, w.im = 0) :
    0 ≤ ((residual.map fun w => -(η : ℂ) / (z - w)).sum).im := by
  induction residual using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
      apply add_nonneg
      · exact rootLogDerivativeContribution_im_nonneg_of_real
          hη hz (hreal w (by simp))
      · apply ih
        intro u hu
        exact hreal u (by simp [hu])

/-- The literal quartet background has nonnegative imaginary part whenever
every residual root in its exact multiset decomposition is real. -/
theorem finiteQuartetLogDerivativeBackground_im_nonneg_of_real_residual
    {A : ℝ[X]} {η tau a : ℝ} {residual : Multiset ℂ} {z : ℂ}
    (hη : 0 ≤ η) (htau : tau ≠ 0) (ha : 0 < a) (hz : 0 < z.im)
    (hAz : A.eval₂ Complex.ofRealHom z ≠ 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val + residual)
    (hreal : ∀ w ∈ residual, w.im = 0) :
    0 ≤ (finiteQuartetLogDerivativeBackground A η η tau a z).im := by
  rw [finiteQuartetLogDerivativeBackground_eq_residual_root_sum
    htau ha hAz hroots]
  exact residualRootLogDerivativeSum_im_nonneg_of_real hη hz hreal

/-- End-to-end finite theorem for one symmetric off-axis quartet and an
arbitrary finite residual divisor supported on the real axis.  Exact root
expansion proves the required Herglotz background sign, so it is not an
assumption. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_E_root_real_residual
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    {η tau a x v : ℝ} {residual : Multiset ℂ}
    (hη : 0 < η) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hbaseCount : upperHalfPlaneRootCount (finiteEPolynomial A 0) = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hroot : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val + residual)
    (hreal : ∀ w ∈ residual, w.im = 0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      η ^ 2 / (η ^ 2 + a ^ 2) := by
  have hAPole : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA hη.ne' hroot
  have hvalue :
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
        -Complex.I :=
    (finiteNegativeLogDerivativeValue_eq_neg_I_iff hAPole).mpr hroot
  have hpole : symmetricQuartetLogDerivativeContribution η tau a
        (symmetricPickPole x v) +
      finiteQuartetLogDerivativeBackground A η η tau a
        (symmetricPickPole x v) = -Complex.I := by
    calc
      symmetricQuartetLogDerivativeContribution η tau a
            (symmetricPickPole x v) +
          finiteQuartetLogDerivativeBackground A η η tau a
            (symmetricPickPole x v) =
          finiteNegativeLogDerivativeValue A η
            (symmetricPickPole x v) := by
        unfold finiteQuartetLogDerivativeBackground
        ring
      _ = -Complex.I := hvalue
  have hbackground : 0 ≤
      (finiteQuartetLogDerivativeBackground A η η tau a
        (symmetricPickPole x v)).im :=
    finiteQuartetLogDerivativeBackground_im_nonneg_of_real_residual
      hη.le htau ha (by simpa using hv) hAPole hroots hreal
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition_baseCount
      hA hEven hη hη htau ha hv hx hbaseCount hAPlus
      (finiteNegativeLogDerivativeValue_eq_quartet_add_background
        A η η tau a) hbackground hpole

end

end RiemannGaussian
