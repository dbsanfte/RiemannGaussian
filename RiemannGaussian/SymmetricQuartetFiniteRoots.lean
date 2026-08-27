import RiemannGaussian.SymmetricQuartetHardyMetric
import RiemannGaussian.WeightedHyperbolicEnergy

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

/-! ## Off-axis residual pairs outside their influence disks -/

/-- The root multiset generated by a multiset of chosen upper roots and their
complex conjugates, with multiplicities retained. -/
def conjugatePairRootMultiset (upper : Multiset ℂ) : Multiset ℂ :=
  upper + upper.map (starRingEnd ℂ)

/-- The root sum over a conjugate-pair multiset is exactly the sum of the
corresponding two-root logarithmic-derivative contributions. -/
theorem conjugatePairRootMultiset_logDerivative_sum
    (η : ℝ) (upper : Multiset ℂ) (z : ℂ) :
    ((conjugatePairRootMultiset upper).map fun w =>
        -(η : ℂ) / (z - w)).sum =
      (upper.map fun alpha =>
        onePairLogDerivativeContribution η alpha z).sum := by
  unfold conjugatePairRootMultiset onePairLogDerivativeContribution
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.sum_map_add]
  rfl

/-- A multiset of conjugate off-axis pairs contributes nonnegative imaginary
part at an upper-half-plane point if that point lies outside every pair's
influence disk. -/
theorem conjugatePairRootLogDerivativeSum_im_nonneg_of_height_sq_le
    {η : ℝ} (hη : 0 ≤ η) {upper : Multiset ℂ} {z : ℂ}
    (hz : 0 < z.im)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha)
    (houtside : ∀ alpha ∈ upper, alpha.im ^ 2 ≤
      (z.re - alpha.re) ^ 2 + z.im ^ 2) :
    0 ≤ (((conjugatePairRootMultiset upper).map fun w =>
      -(η : ℂ) / (z - w)).sum).im := by
  rw [conjugatePairRootMultiset_logDerivative_sum]
  induction upper using Multiset.induction_on with
  | empty => simp
  | cons alpha s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
      apply add_nonneg
      · exact onePairLogDerivativeContribution_im_nonneg_of_height_sq_le
          hη hz (halpha alpha (by simp)) (hne alpha (by simp))
          (houtside alpha (by simp))
      · apply ih
        · intro beta hbeta
          exact halpha beta (by simp [hbeta])
        · intro beta hbeta
          exact hne beta (by simp [hbeta])
        · intro beta hbeta
          exact houtside beta (by simp [hbeta])

/-- Residual upper roots whose conjugate-pair contribution is nonnegative at
`z`, expressed by the closed influence-disk complement. -/
def outsideInfluenceDiskRoots (z : ℂ) (upper : Multiset ℂ) : Multiset ℂ :=
  upper.filter fun alpha =>
    alpha.im ^ 2 ≤ (z.re - alpha.re) ^ 2 + z.im ^ 2

/-- Residual upper roots whose conjugate-pair contribution can be negative at
`z`, expressed by the open influence disk. -/
def insideInfluenceDiskRoots (z : ℂ) (upper : Multiset ℂ) : Multiset ℂ :=
  upper.filter fun alpha =>
    (z.re - alpha.re) ^ 2 + z.im ^ 2 < alpha.im ^ 2

/-- The outside- and inside-disk multisets form an exact multiplicity-aware
partition of the upper roots. -/
@[simp] theorem outsideInfluenceDiskRoots_add_insideInfluenceDiskRoots
    (z : ℂ) (upper : Multiset ℂ) :
    outsideInfluenceDiskRoots z upper + insideInfluenceDiskRoots z upper =
      upper := by
  unfold outsideInfluenceDiskRoots insideInfluenceDiskRoots
  have hpred :
      (fun alpha : ℂ =>
        (z.re - alpha.re) ^ 2 + z.im ^ 2 < alpha.im ^ 2) =
      (fun alpha : ℂ =>
        ¬alpha.im ^ 2 ≤ (z.re - alpha.re) ^ 2 + z.im ^ 2) := by
    funext alpha
    apply propext
    exact not_le.symm
  simpa only [hpred] using
    (Multiset.filter_add_not
      (p := fun alpha : ℂ =>
        alpha.im ^ 2 ≤ (z.re - alpha.re) ^ 2 + z.im ^ 2) upper)

/-- Exact splitting of the pair logarithmic-derivative sum into its harmless
outside-disk part and its potentially negative inside-disk part. -/
theorem onePairLogDerivativeContribution_sum_eq_outside_add_inside
    (η : ℝ) (z : ℂ) (upper : Multiset ℂ) :
    (upper.map fun alpha =>
        onePairLogDerivativeContribution η alpha z).sum =
      ((outsideInfluenceDiskRoots z upper).map fun alpha =>
        onePairLogDerivativeContribution η alpha z).sum +
      ((insideInfluenceDiskRoots z upper).map fun alpha =>
        onePairLogDerivativeContribution η alpha z).sum := by
  nth_rw 1 [← outsideInfluenceDiskRoots_add_insideInfluenceDiskRoots z upper]
  rw [Multiset.map_add, Multiset.sum_add]

/-- The outside-disk portion of the exact partition is nonnegative. -/
theorem outsideInfluenceDiskRoots_logDerivativeSum_im_nonneg
    {η : ℝ} (hη : 0 ≤ η) {upper : Multiset ℂ} {z : ℂ}
    (hz : 0 < z.im)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    0 ≤ (((outsideInfluenceDiskRoots z upper).map fun alpha =>
      onePairLogDerivativeContribution η alpha z).sum).im := by
  rw [← conjugatePairRootMultiset_logDerivative_sum]
  apply conjugatePairRootLogDerivativeSum_im_nonneg_of_height_sq_le hη hz
  · intro alpha halphaMem
    exact halpha alpha (Multiset.mem_of_mem_filter halphaMem)
  · intro alpha halphaMem
    exact hne alpha (Multiset.mem_of_mem_filter halphaMem)
  · intro alpha halphaMem
    exact (Multiset.mem_filter.mp halphaMem).2

/-- After the exact partition, the inside-disk sum is no larger than the
complete off-axis-pair sum.  Thus every negative pole condition transfers to
this sharply isolated finite core. -/
theorem insideInfluenceDiskRoots_logDerivativeSum_im_le
    {η : ℝ} (hη : 0 ≤ η) {upper : Multiset ℂ} {z : ℂ}
    (hz : 0 < z.im)
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im)
    (hne : ∀ alpha ∈ upper, z ≠ alpha) :
    (((insideInfluenceDiskRoots z upper).map fun alpha =>
      onePairLogDerivativeContribution η alpha z).sum).im ≤
        ((upper.map fun alpha =>
          onePairLogDerivativeContribution η alpha z).sum).im := by
  have houtside := outsideInfluenceDiskRoots_logDerivativeSum_im_nonneg
    hη hz halpha hne
  have hsplit := onePairLogDerivativeContribution_sum_eq_outside_add_inside
    η z upper
  have him := congrArg Complex.im hsplit
  rw [Complex.add_im] at him
  linarith

/-- At positive weight, every member of the inside-disk core contributes
strictly negatively; the geometric partition is the exact sign partition. -/
theorem insideInfluenceDiskRoots_logDerivativeContribution_im_neg
    {η : ℝ} (hη : 0 < η) {upper : Multiset ℂ} {z alpha : ℂ}
    (hz : 0 < z.im)
    (halpha : ∀ beta ∈ upper, 0 < beta.im)
    (hne : ∀ beta ∈ upper, z ≠ beta)
    (halphaInside : alpha ∈ insideInfluenceDiskRoots z upper) :
    (onePairLogDerivativeContribution η alpha z).im < 0 := by
  apply (onePairLogDerivativeContribution_im_neg_iff_height_sq_lt
    hη hz
      (halpha alpha (Multiset.mem_of_mem_filter halphaInside))
      (hne alpha (Multiset.mem_of_mem_filter halphaInside))).mpr
  exact (Multiset.mem_filter.mp halphaInside).2

/-- A root of a positive finite homotopy cannot also be one of the named
upper roots of its separable base polynomial. -/
theorem finiteE_root_ne_upperResidual
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual) :
    ∀ alpha ∈ upperResidual, z ≠ alpha := by
  have hAz : A.eval₂ Complex.ofRealHom z ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA heta.ne' hroot
  have hpolyNe : A.map Complex.ofRealHom ≠ 0 :=
    Polynomial.map_ne_zero hA.ne_zero
  intro alpha halphaMem heq
  apply hAz
  rw [heq]
  have halphaRoots : alpha ∈ (A.map Complex.ofRealHom).roots := by
    rw [hroots]
    simp [conjugatePairRootMultiset, halphaMem]
  have halphaIsRoot := (Polynomial.mem_roots hpolyNe).mp halphaRoots
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using halphaIsRoot

/-- The complete negative logarithmic-derivative budget transfers to the
inside influence core.  This is the cardinality-free quantitative statement
underlying the multipoint product theorem. -/
theorem
    insideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im) :
    (((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
      onePairLogDerivativeContribution eta alpha z).sum).im ≤ -1 := by
  have hAz : A.eval₂ Complex.ofRealHom z ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA heta.ne' hroot
  have hne : ∀ alpha ∈ upperResidual, z ≠ alpha :=
    finiteE_root_ne_upperResidual hA heta hroot hroots
  have hvalue : finiteNegativeLogDerivativeValue A eta z = -Complex.I :=
    (finiteNegativeLogDerivativeValue_eq_neg_I_iff hAz).mpr hroot
  have hsumAll :
      (((A.map Complex.ofRealHom).roots.map fun w =>
        -(eta : ℂ) / (z - w)).sum) = -Complex.I := by
    rw [← finiteNegativeLogDerivativeValue_eq_root_sum hAz]
    exact hvalue
  have hdecomp :
      (realResidual.map fun w => -(eta : ℂ) / (z - w)).sum +
        (upperResidual.map fun alpha =>
          onePairLogDerivativeContribution eta alpha z).sum =
        -Complex.I := by
    calc
      (realResidual.map fun w => -(eta : ℂ) / (z - w)).sum +
          (upperResidual.map fun alpha =>
            onePairLogDerivativeContribution eta alpha z).sum =
        ((realResidual + conjugatePairRootMultiset upperResidual).map
          fun w => -(eta : ℂ) / (z - w)).sum := by
            rw [Multiset.map_add, Multiset.sum_add,
              conjugatePairRootMultiset_logDerivative_sum]
      _ = (((A.map Complex.ofRealHom).roots.map fun w =>
          -(eta : ℂ) / (z - w)).sum) := by rw [hroots]
      _ = -Complex.I := hsumAll
  have hrealNonneg : 0 ≤
      ((realResidual.map fun w => -(eta : ℂ) / (z - w)).sum).im :=
    residualRootLogDerivativeSum_im_nonneg_of_real heta.le hz hreal
  have him := congrArg Complex.im hdecomp
  rw [Complex.add_im] at him
  simp only [Complex.neg_im, Complex.I_im] at him
  have hpairSum :
      ((upperResidual.map fun alpha =>
        onePairLogDerivativeContribution eta alpha z).sum).im ≤ -1 := by
    linarith
  exact (insideInfluenceDiskRoots_logDerivativeSum_im_le
    heta.le hz halpha hne).trans hpairSum

/-- The inside influence core is necessarily nonempty at every upper root of
a positive finite homotopy. -/
theorem insideInfluenceDiskRoots_card_pos_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A eta).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im) :
    0 < (insideInfluenceDiskRoots z upperResidual).card := by
  have hbudget :=
    insideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA heta hz hroot hroots hreal halpha
  by_contra hcard
  have hzero : insideInfluenceDiskRoots z upperResidual = 0 := by
    apply Multiset.card_eq_zero.mp
    exact Nat.eq_zero_of_not_pos hcard
  rw [hzero] at hbudget
  norm_num at hbudget

/-- Weighted multi-pair consequence for an exact finite polynomial model.
At a root of `A + I*eta*A'`, real residual roots contribute nonnegatively, so
the complete off-axis pair sum has imaginary part at most `-1`.  The exact
influence-disk partition transfers that budget to its strictly negative core,
and the unequal-height energy theorem bounds the product of every core radius
using any common positive lower bound on its heights. -/
theorem
    insideInfluenceDiskRootPseudoHyperbolicProduct_lt_threshold_of_finiteE_root
    {A : ℝ[X]} (hA : A.Separable) {η a0 : ℝ} {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (hη : 0 < η) (ha0 : 0 < a0) (hz : 0 < z.im)
    (hroot : (finiteEPolynomial A η).eval z = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (hcard : 2 ≤ (insideInfluenceDiskRoots z upperResidual).card)
    (hminHeight : ∀ alpha ∈ insideInfluenceDiskRoots z upperResidual,
      a0 ≤ alpha.im) :
    ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
      upperHalfPlanePseudoHyperbolicDistance z alpha).prod <
        pairHyperbolicThreshold η a0 := by
  have hne : ∀ alpha ∈ upperResidual, z ≠ alpha := by
    exact finiteE_root_ne_upperResidual hA hη hroot hroots
  have hinsideSum :
      (((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
        onePairLogDerivativeContribution η alpha z).sum).im ≤ -1 :=
    insideInfluenceDiskRoots_logDerivativeSum_im_le_neg_one_of_finiteE_root
      hA hη hz hroot hroots hreal halpha
  apply upperRootPseudoHyperbolicProduct_lt_threshold_of_im_sum
    hη ha0 hz hcard
  · intro alpha halphaMem
    exact halpha alpha (Multiset.mem_of_mem_filter halphaMem)
  · intro alpha halphaMem
    exact hne alpha (Multiset.mem_of_mem_filter halphaMem)
  · exact hminHeight
  · exact hinsideSum

/-- Exact background positivity for a residual divisor consisting of real
roots and conjugate off-axis pairs whose influence disks avoid the evaluation
point.  The conclusion is derived from the complete root multiset, not assumed.
-/
theorem
    finiteQuartetLogDerivativeBackground_im_nonneg_of_real_and_outside_pairs
    {A : ℝ[X]} {η tau a : ℝ}
    {realResidual upperResidual : Multiset ℂ} {z : ℂ}
    (hη : 0 ≤ η) (htau : tau ≠ 0) (ha : 0 < a) (hz : 0 < z.im)
    (hAz : A.eval₂ Complex.ofRealHom z ≠ 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val +
        (realResidual + conjugatePairRootMultiset upperResidual))
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (hne : ∀ alpha ∈ upperResidual, z ≠ alpha)
    (houtside : ∀ alpha ∈ upperResidual, alpha.im ^ 2 ≤
      (z.re - alpha.re) ^ 2 + z.im ^ 2) :
    0 ≤ (finiteQuartetLogDerivativeBackground A η η tau a z).im := by
  rw [finiteQuartetLogDerivativeBackground_eq_residual_root_sum
    htau ha hAz hroots, Multiset.map_add, Multiset.sum_add, Complex.add_im]
  exact add_nonneg
    (residualRootLogDerivativeSum_im_nonneg_of_real hη hz hreal)
    (conjugatePairRootLogDerivativeSum_im_nonneg_of_height_sq_le
      hη hz halpha hne houtside)

/-- End-to-end finite determinant theorem with real residual roots and
additional conjugate off-axis pairs.  Instead of assuming a Herglotz
background, it proves the sign from the exact roots under the explicit
geometric condition that the candidate pole lies outside every residual
pair's influence disk. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_E_root_real_and_outside_pair_residual
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    {η tau a x v : ℝ}
    {realResidual upperResidual : Multiset ℂ}
    (hη : 0 < η) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hbaseCount : upperHalfPlaneRootCount (finiteEPolynomial A 0) = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hroot : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hroots : (A.map Complex.ofRealHom).roots =
      (symmetricQuartetRootFinset tau a).val +
        (realResidual + conjugatePairRootMultiset upperResidual))
    (hreal : ∀ w ∈ realResidual, w.im = 0)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (houtside : ∀ alpha ∈ upperResidual, alpha.im ^ 2 ≤
      ((symmetricPickPole x v).re - alpha.re) ^ 2 +
        (symmetricPickPole x v).im ^ 2) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      η ^ 2 / (η ^ 2 + a ^ 2) := by
  have hAPole : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA hη.ne' hroot
  have hpolyNe : A.map Complex.ofRealHom ≠ 0 :=
    Polynomial.map_ne_zero hA.ne_zero
  have hne : ∀ alpha ∈ upperResidual,
      symmetricPickPole x v ≠ alpha := by
    intro alpha halphaMem heq
    apply hAPole
    rw [heq]
    have halphaRoots : alpha ∈ (A.map Complex.ofRealHom).roots := by
      rw [hroots]
      simp [conjugatePairRootMultiset, halphaMem]
    have halphaIsRoot := (Polynomial.mem_roots hpolyNe).mp halphaRoots
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using halphaIsRoot
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
    finiteQuartetLogDerivativeBackground_im_nonneg_of_real_and_outside_pairs
      hη.le htau ha (by simpa using hv) hAPole hroots hreal halpha hne
        houtside
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition_baseCount
      hA hEven hη hη htau ha hv hx hbaseCount hAPlus
      (finiteNegativeLogDerivativeValue_eq_quartet_add_background
        A η η tau a) hbackground hpole

end

end RiemannGaussian
