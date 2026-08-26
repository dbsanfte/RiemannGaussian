import RiemannGaussian.FiniteHardyCauchyBasis
import RiemannGaussian.FiniteERootCountEndpoint
import RiemannGaussian.FiniteNegConjSymmetry
import RiemannGaussian.SymmetricQuartetPickDefect

/-!
# Symmetric-quartet specialization of the finite Hardy metric

This file identifies the literal upper-root Blaschke factor of a degree-two
finite negative Hardy model with the symmetric two-pole Blaschke product.
Consequently the interpolation hypotheses in the separation-free quartet
bound follow from the two stated roots of the original real polynomial.

The final theorem composes that scalar bound with the actual Hardy
cross-angle determinant.  It does not assume a generalized eigenbasis or
distinct metric modes.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- An upper-half-plane root of a polynomial is a root of its literal upper
root factor. -/
theorem upperRootFactor_eval_eq_zero_of_eval_eq_zero
    {p : ℂ[X]} (hp : p ≠ 0) {w : ℂ} (hw : 0 < w.im)
    (hroot : p.eval w = 0) :
    (upperRootFactor p).eval w = 0 := by
  apply (mem_roots (upperRootFactor_ne_zero p)).mp
  rw [upperRootFactor_roots, Multiset.mem_filter]
  exact ⟨(mem_roots hp).mpr hroot, hw⟩

/-- Two distinct roots exhaust a degree-two upper root factor, including
multiplicity. -/
theorem upperRootFactor_roots_eq_pair
    {p : ℂ[X]} {w₀ w₁ : ℂ}
    (hroot₀ : (upperRootFactor p).eval w₀ = 0)
    (hroot₁ : (upperRootFactor p).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor p).natDegree = 2) :
    (upperRootFactor p).roots = ({w₀, w₁} : Finset ℂ).val := by
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hroot₀
    · exact hroot₁
  · simpa [hdegree] using (Finset.card_pair hne).ge
  · exact upperRootFactor_ne_zero p

/-- Product formula for a degree-two upper root factor whose two roots have
been named explicitly. -/
theorem upperRootBlaschkeValue_eq_two_factors
    {p : ℂ[X]} {w₀ w₁ : ℂ}
    (hroot₀ : (upperRootFactor p).eval w₀ = 0)
    (hroot₁ : (upperRootFactor p).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor p).natDegree = 2)
    (z : ℂ) :
    upperRootBlaschkeValue p z =
      elementaryUpperHalfPlaneBlaschke w₀ z *
        elementaryUpperHalfPlaneBlaschke w₁ z := by
  rw [upperRootBlaschkeValue_eq_prod,
    ← upperRootFactor_roots,
    upperRootFactor_roots_eq_pair hroot₀ hroot₁ hne hdegree]
  have hnotMem : w₀ ∉ ({w₁} : Finset ℂ) := by
    simpa using hne
  rw [Finset.insert_val_of_notMem hnotMem]
  simp [elementaryUpperHalfPlaneBlaschke]

/-- The two symmetric upper-half-plane points are distinct exactly when
their nonnegative/negative real coordinates do not collapse at zero. -/
theorem symmetricPickPole_ne_reflected_of_ne_zero
    {x v : ℝ} (hx : x ≠ 0) :
    symmetricPickPole x v ≠ symmetricPickPole (-x) v := by
  intro h
  have hre := congrArg Complex.re h
  simp [symmetricPickPole, upperHalfPlanePoint] at hre
  apply hx
  linarith

/-- Distinct upper-half-plane coordinate points have strictly positive
pseudo-hyperbolic numerator square. -/
theorem pairHyperbolicUpperSq_pos_of_upperHalfPlanePoint_ne
    {x v c a : ℝ}
    (hne : upperHalfPlanePoint x v ≠ upperHalfPlanePoint c a) :
    0 < pairHyperbolicUpperSq (x - c) v a := by
  by_contra hnot
  have hle : pairHyperbolicUpperSq (x - c) v a ≤ 0 := le_of_not_gt hnot
  have hxc : x = c := by
    unfold pairHyperbolicUpperSq at hle
    nlinarith [sq_nonneg (x - c), sq_nonneg (v - a)]
  have hva : v = a := by
    unfold pairHyperbolicUpperSq at hle
    nlinarith [sq_nonneg (x - c), sq_nonneg (v - a)]
  apply hne
  simp [upperHalfPlanePoint, hxc, hva]

/-- The finite Blaschke factor is the symmetric two-pole product once its
degree-two numerator roots are the symmetric candidate poles. -/
theorem finiteBlaschkeValue_eq_symmetricPickBlaschke
    {A : ℝ[X]} (hA : A.Separable) {η x v : ℝ}
    (hx : x ≠ 0) (hv : 0 < v)
    (hrootPlus : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hrootMinus : (finiteEPolynomial A η).eval
      (symmetricPickPole (-x) v) = 0)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2) :
    finiteBlaschkeValue A η = symmetricPickBlaschke x v := by
  have hne := symmetricPickPole_ne_reflected_of_ne_zero (v := v) hx
  have hupperPlus : 0 < (symmetricPickPole x v).im := by
    simpa using hv
  have hupperMinus : 0 < (symmetricPickPole (-x) v).im := by
    simpa using hupperPlus
  have hfactorPlus :
      (upperRootFactor (finiteEPolynomial A η)).eval
          (symmetricPickPole x v) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero η) hupperPlus hrootPlus
  have hfactorMinus :
      (upperRootFactor (finiteEPolynomial A η)).eval
          (symmetricPickPole (-x) v) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero η) hupperMinus hrootMinus
  funext z
  simpa [finiteBlaschkeValue, symmetricPickBlaschke,
    symmetricTwoPointBlaschke, upperHalfPlaneBlaschkeFactor,
    symmetricPickPole, elementaryUpperHalfPlaneBlaschke] using
      upperRootBlaschkeValue_eq_two_factors
        hfactorPlus hfactorMinus hne hdegree z

/-- Once the degree-two finite Blaschke numerator is the symmetric pole
pair, every zero of the original real polynomial supplies the required
interpolation value for the residual inner factor. -/
theorem finiteInnerValue_eq_neg_symmetricPickBlaschke_at_root
    {A : ℝ[X]} (hA : A.Separable) {η x v : ℝ}
    (hη : η ≠ 0) (hx : x ≠ 0) (hv : 0 < v)
    (hrootPlus : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hrootMinus : (finiteEPolynomial A η).eval
      (symmetricPickPole (-x) v) = 0)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    lowerRootInnerValue (finiteEPolynomial A η) gamma =
      -symmetricPickBlaschke x v gamma := by
  change finiteInnerValue A η gamma = _
  rw [finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
      hA hη hgamma,
    finiteBlaschkeValue_eq_symmetricPickBlaschke
      hA hx hv hrootPlus hrootMinus hdegree]

/-- The square root of the real Hardy complement determinant is exactly the
modulus of the product of its two residual root values. -/
theorem finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_eq_rootValues
    {A : ℝ[X]} (hA : A.Separable) {η : ℝ} (hη : η ≠ 0)
    {w₀ w₁ : ℂ} (hw₀ : 0 < w₀.im) (hw₁ : 0 < w₁.im)
    (hroot₀ : (upperRootFactor (finiteEPolynomial A η)).eval w₀ = 0)
    (hroot₁ : (upperRootFactor (finiteEPolynomial A η)).eval w₁ = 0)
    (hne : w₀ ≠ w₁)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re =
      ‖lowerRootInnerValue (finiteEPolynomial A η) w₀ *
        lowerRootInnerValue (finiteEPolynomial A η) w₁‖ := by
  rw [finiteHardyCrossAngleComplementGramOperator_det_eq_rootValues
    hA hη hw₀ hw₁ hroot₀ hroot₁ hne hdegree]
  rfl

/-- End-to-end separation-free quartet estimate for the actual finite Hardy
cross-angle determinant.  The two interpolation hypotheses used by the Pick
argument are derived here from the polynomial roots and are not assumptions.

The square root is the product of the two metric-complement magnitudes at
the determinant level; no choice of individual modes is needed. -/
theorem finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound
    {A : ℝ[X]} (hA : A.Separable)
    {η m tau a x v : ℝ} {background : ℂ}
    (hη : η ≠ 0) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hrootPlus : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hrootMinus : (finiteEPolynomial A η).eval
      (symmetricPickPole (-x) v) = 0)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hAMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaMinus tau a) = 0)
    (hupperPlus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hupperMinus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ background.im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (upperHalfPlanePoint x v) + background = -Complex.I)
    (hreflect :
      lowerRootInnerValue (finiteEPolynomial A η)
          (symmetricPickPole (-x) v) =
        starRingEnd ℂ
          (lowerRootInnerValue (finiteEPolynomial A η)
            (symmetricPickPole x v))) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hwPlus : 0 < (symmetricPickPole x v).im := by
    simpa using hv
  have hwMinus : 0 < (symmetricPickPole (-x) v).im := by
    simpa using hv
  have hfactorPlus :
      (upperRootFactor (finiteEPolynomial A η)).eval
          (symmetricPickPole x v) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero η) hwPlus hrootPlus
  have hfactorMinus :
      (upperRootFactor (finiteEPolynomial A η)).eval
          (symmetricPickPole (-x) v) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero η) hwMinus hrootMinus
  have hne : symmetricPickPole x v ≠ symmetricPickPole (-x) v :=
    symmetricPickPole_ne_reflected_of_ne_zero hx
  have hinterpPlus :
      lowerRootInnerValue (finiteEPolynomial A η)
          (symmetricPickAlphaPlus tau a) =
        -symmetricPickBlaschke x v
          (symmetricPickAlphaPlus tau a) :=
    finiteInnerValue_eq_neg_symmetricPickBlaschke_at_root
      hA hη hx hv hrootPlus hrootMinus hdegree hAPlus
  have hinterpMinus :
      lowerRootInnerValue (finiteEPolynomial A η)
          (symmetricPickAlphaMinus tau a) =
        -symmetricPickBlaschke x v
          (symmetricPickAlphaMinus tau a) :=
    finiteInnerValue_eq_neg_symmetricPickBlaschke_at_root
      hA hη hx hv hrootPlus hrootMinus hdegree hAMinus
  rw [finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_eq_rootValues
    hA hη hwPlus hwMinus hfactorPlus hfactorMinus hne hdegree]
  exact norm_lowerRootInnerValue_pole_product_lt_closed_quartet_bound_sq
    (finiteEPolynomial A η) hm htau ha hv hupperPlus hupperMinus
    hbackground hpole hinterpPlus hinterpMinus hreflect

/-! ## Polynomial logarithmic-derivative pole bridge -/

/-- The scaled negative logarithmic derivative whose `-I` level set is the
zero set of `A + I η A'`, away from the zeros of `A`. -/
def finiteNegativeLogDerivativeValue
    (A : ℝ[X]) (η : ℝ) (z : ℂ) : ℂ :=
  -(η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z /
    A.eval₂ Complex.ofRealHom z

/-- The `-I` value of the totalized logarithmic derivative itself forces its
denominator to be nonzero. -/
theorem finiteNegativeLogDerivativeValue_denominator_ne_zero_of_eq_neg_I
    {A : ℝ[X]} {η : ℝ} {z : ℂ}
    (hvalue : finiteNegativeLogDerivativeValue A η z = -Complex.I) :
    A.eval₂ Complex.ofRealHom z ≠ 0 := by
  intro hzero
  rw [finiteNegativeLogDerivativeValue, hzero, div_zero] at hvalue
  exact (neg_ne_zero.mpr Complex.I_ne_zero) hvalue.symm

/-- For an even real base polynomial, the scaled negative logarithmic
derivative is anti-equivariant under reflection in the imaginary axis. -/
theorem finiteNegativeLogDerivativeValue_negConj
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (η : ℝ) (z : ℂ) :
    finiteNegativeLogDerivativeValue A η (negConj z) =
      -starRingEnd ℂ (finiteNegativeLogDerivativeValue A η z) := by
  unfold finiteNegativeLogDerivativeValue
  rw [
    realPolynomial_eval₂_negConj_eq_conj_of_even hEven,
    realPolynomial_derivative_eval₂_negConj_eq_neg_conj_of_even hEven]
  simp only [map_div₀, map_mul, map_neg, starRingEnd_apply]
  have hηstar : star (η : ℂ) = (η : ℂ) := by simp
  rw [hηstar]
  ring

/-- Exact algebraic equivalence between the finite pole equation and a root
of the homotopy polynomial. -/
theorem finiteNegativeLogDerivativeValue_eq_neg_I_iff
    {A : ℝ[X]} {η : ℝ} {z : ℂ}
    (hAz : A.eval₂ Complex.ofRealHom z ≠ 0) :
    finiteNegativeLogDerivativeValue A η z = -Complex.I ↔
      (finiteEPolynomial A η).eval z = 0 := by
  rw [finiteNegativeLogDerivativeValue, finiteEPolynomial_eval]
  constructor
  · intro h
    have hmul := (div_eq_iff hAz).mp h
    have hderiv :
        (η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z =
          Complex.I * A.eval₂ Complex.ofRealHom z := by
      calc
        (η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z =
            -(-(η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z) := by
              ring
        _ = -((-Complex.I) * A.eval₂ Complex.ofRealHom z) := by
              rw [hmul]
        _ = Complex.I * A.eval₂ Complex.ofRealHom z := by ring
    rw [mul_assoc, hderiv, ← mul_assoc]
    have hII : Complex.I * Complex.I = (-1 : ℂ) := by
      calc
        Complex.I * Complex.I = Complex.I ^ 2 := by ring
        _ = -1 := Complex.I_sq
    rw [hII]
    ring
  · intro h
    have hIderiv :
        Complex.I * ((η : ℂ) *
          A.derivative.eval₂ Complex.ofRealHom z) =
            -A.eval₂ Complex.ofRealHom z := by
      linear_combination h
    have hderiv :
        (η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z =
          Complex.I * A.eval₂ Complex.ofRealHom z := by
      calc
        (η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z =
            (-Complex.I) *
              (Complex.I * ((η : ℂ) *
                A.derivative.eval₂ Complex.ofRealHom z)) := by
              rw [← mul_assoc]
              have hnegII : (-Complex.I) * Complex.I = (1 : ℂ) := by
                calc
                  (-Complex.I) * Complex.I = -(Complex.I ^ 2) := by ring
                  _ = -(-1) := by rw [Complex.I_sq]
                  _ = 1 := by ring
              rw [hnegII, one_mul]
        _ = (-Complex.I) *
            (-A.eval₂ Complex.ofRealHom z) := by rw [hIderiv]
        _ = Complex.I * A.eval₂ Complex.ofRealHom z := by ring
    apply (div_eq_iff hAz).mpr
    calc
      -(η : ℂ) * A.derivative.eval₂ Complex.ofRealHom z =
          -((η : ℂ) *
            A.derivative.eval₂ Complex.ofRealHom z) := by ring
      _ = -(Complex.I * A.eval₂ Complex.ofRealHom z) := by rw [hderiv]
      _ = -Complex.I * A.eval₂ Complex.ofRealHom z := by ring

/-- A root of the finite homotopy polynomial cannot also be a zero of the
separable base polynomial at a nonzero parameter. -/
theorem finiteE_root_base_eval_ne_zero
    {A : ℝ[X]} (hA : A.Separable) {η : ℝ} (hη : η ≠ 0) {z : ℂ}
    (hroot : (finiteEPolynomial A η).eval z = 0) :
    A.eval₂ Complex.ofRealHom z ≠ 0 := by
  intro hzero
  exact (finiteE_eval_ne_zero_at_root hA hη hzero) hroot

/-- A conjugate pair contribution is anti-equivariant under reflection in
the imaginary axis, provided its upper zero is reflected at the same time. -/
theorem onePairLogDerivativeContribution_neg_conj
    (m : ℝ) (alpha z : ℂ) :
    onePairLogDerivativeContribution m (-starRingEnd ℂ alpha)
        (-starRingEnd ℂ z) =
      -starRingEnd ℂ (onePairLogDerivativeContribution m alpha z) := by
  unfold onePairLogDerivativeContribution
  simp only [map_add, map_div₀, map_neg, map_sub,
    starRingEnd_apply, star_star]
  simp only [sub_neg_eq_add]
  have hmstar : star (m : ℂ) = (m : ℂ) := by simp
  rw [hmstar]
  rw [show -star z + star alpha = -(star z - star alpha) by ring,
    show -star z + alpha = -(star z - alpha) by ring]
  rw [div_neg, div_neg]
  ring

/-- The full symmetric quartet logarithmic derivative has the same
anti-equivariance. -/
theorem symmetricQuartetLogDerivativeContribution_neg_conj
    (m tau a : ℝ) (z : ℂ) :
    symmetricQuartetLogDerivativeContribution m tau a
        (-starRingEnd ℂ z) =
      -starRingEnd ℂ
        (symmetricQuartetLogDerivativeContribution m tau a z) := by
  unfold symmetricQuartetLogDerivativeContribution
  rw [show upperHalfPlanePoint (-tau) a =
      -starRingEnd ℂ (upperHalfPlanePoint tau a) by simp]
  rw [onePairLogDerivativeContribution_neg_conj,
    show onePairLogDerivativeContribution m (upperHalfPlanePoint tau a)
        (-starRingEnd ℂ z) =
      -starRingEnd ℂ
        (onePairLogDerivativeContribution m
          (-starRingEnd ℂ (upperHalfPlanePoint tau a)) z) by
      simpa using onePairLogDerivativeContribution_neg_conj
        m (-starRingEnd ℂ (upperHalfPlanePoint tau a)) z]
  simp

/-- In an exact quartet-plus-background decomposition for an even base
polynomial, negative-conjugation symmetry of the background is forced rather
than assumed. -/
theorem logDerivativeBackground_negConj
    {A : ℝ[X]} (hEven : A.comp (-X) = A)
    (η m tau a : ℝ) (background : ℂ → ℂ)
    (hdecompose : ∀ z,
      finiteNegativeLogDerivativeValue A η z =
        symmetricQuartetLogDerivativeContribution m tau a z + background z)
    (z : ℂ) :
    background (negConj z) = -starRingEnd ℂ (background z) := by
  calc
    background (negConj z) =
        finiteNegativeLogDerivativeValue A η (negConj z) -
          symmetricQuartetLogDerivativeContribution m tau a (negConj z) := by
      rw [hdecompose (negConj z)]
      ring
    _ = -starRingEnd ℂ (finiteNegativeLogDerivativeValue A η z) -
        (-starRingEnd ℂ
          (symmetricQuartetLogDerivativeContribution m tau a z)) := by
      rw [finiteNegativeLogDerivativeValue_negConj hEven,
        show negConj z = -starRingEnd ℂ z by rfl,
        symmetricQuartetLogDerivativeContribution_neg_conj]
    _ = -starRingEnd ℂ
        (finiteNegativeLogDerivativeValue A η z -
          symmetricQuartetLogDerivativeContribution m tau a z) := by
      simp only [map_sub]
      ring
    _ = -starRingEnd ℂ (background z) := by
      rw [hdecompose z]
      simp only [map_sub, map_add]
      ring

/-- The literal residual after subtracting one named symmetric quartet from
the finite negative logarithmic derivative. -/
def finiteQuartetLogDerivativeBackground
    (A : ℝ[X]) (η m tau a : ℝ) (z : ℂ) : ℂ :=
  finiteNegativeLogDerivativeValue A η z -
    symmetricQuartetLogDerivativeContribution m tau a z

/-- The quartet-plus-background decomposition for the literal residual is an
exact identity, with no analytic assumption. -/
theorem finiteNegativeLogDerivativeValue_eq_quartet_add_background
    (A : ℝ[X]) (η m tau a : ℝ) (z : ℂ) :
    finiteNegativeLogDerivativeValue A η z =
      symmetricQuartetLogDerivativeContribution m tau a z +
        finiteQuartetLogDerivativeBackground A η m tau a z := by
  unfold finiteQuartetLogDerivativeBackground
  ring

/-- The finite Hardy quartet estimate with its two candidate `E`-root
hypotheses derived from an exact logarithmic-derivative decomposition.

The pole equation is assumed only at `x + I*v`.  Anti-equivariance of the
quartet contribution and the stated reflection law for the background force
the same equation at `-x + I*v`; the logarithmic-derivative bridge then turns
both equations into roots of `A + I eta A'`. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_logDerivativeDecomposition
    {A : ℝ[X]} (hA : A.Separable)
    {η m tau a x v : ℝ} {background : ℂ → ℂ}
    (hη : η ≠ 0) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hAMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaMinus tau a) = 0)
    (hAPolePlus : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0)
    (hAPoleMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickPole (-x) v) ≠ 0)
    (hdecompose : ∀ z,
      finiteNegativeLogDerivativeValue A η z =
        symmetricQuartetLogDerivativeContribution m tau a z + background z)
    (hupperPlus : 0 < pairHyperbolicUpperSq (x - tau) v a)
    (hupperMinus : 0 < pairHyperbolicUpperSq (x + tau) v a)
    (hbackground : 0 ≤ (background (symmetricPickPole x v)).im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (symmetricPickPole x v) +
      background (symmetricPickPole x v) = -Complex.I)
    (hbackgroundReflect :
      background (symmetricPickPole (-x) v) =
        -starRingEnd ℂ (background (symmetricPickPole x v)))
    (hreflect :
      lowerRootInnerValue (finiteEPolynomial A η)
          (symmetricPickPole (-x) v) =
        starRingEnd ℂ
          (lowerRootInnerValue (finiteEPolynomial A η)
            (symmetricPickPole x v))) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hfinitePlus :
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
        -Complex.I := by
    calc
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
          symmetricQuartetLogDerivativeContribution m tau a
              (symmetricPickPole x v) +
            background (symmetricPickPole x v) :=
        hdecompose (symmetricPickPole x v)
      _ = -Complex.I := hpole
  have hrootPlus :
      (finiteEPolynomial A η).eval (symmetricPickPole x v) = 0 :=
    (finiteNegativeLogDerivativeValue_eq_neg_I_iff hAPolePlus).mp hfinitePlus
  have hquartetReflect :
      symmetricQuartetLogDerivativeContribution m tau a
          (symmetricPickPole (-x) v) =
        -starRingEnd ℂ
          (symmetricQuartetLogDerivativeContribution m tau a
            (symmetricPickPole x v)) := by
    simpa only [neg_conj_symmetricPickPole] using
      symmetricQuartetLogDerivativeContribution_neg_conj
        m tau a (symmetricPickPole x v)
  have hpoleMinus :
      symmetricQuartetLogDerivativeContribution m tau a
          (symmetricPickPole (-x) v) +
        background (symmetricPickPole (-x) v) = -Complex.I := by
    calc
      symmetricQuartetLogDerivativeContribution m tau a
            (symmetricPickPole (-x) v) +
          background (symmetricPickPole (-x) v) =
          -starRingEnd ℂ
              (symmetricQuartetLogDerivativeContribution m tau a
                (symmetricPickPole x v)) +
            -starRingEnd ℂ
              (background (symmetricPickPole x v)) := by
        rw [hquartetReflect, hbackgroundReflect]
      _ = -starRingEnd ℂ
          (symmetricQuartetLogDerivativeContribution m tau a
              (symmetricPickPole x v) +
            background (symmetricPickPole x v)) := by
        simp only [map_add]
        ring
      _ = -starRingEnd ℂ (-Complex.I) := by rw [hpole]
      _ = -Complex.I := by simp
  have hfiniteMinus :
      finiteNegativeLogDerivativeValue A η (symmetricPickPole (-x) v) =
        -Complex.I := by
    calc
      finiteNegativeLogDerivativeValue A η (symmetricPickPole (-x) v) =
          symmetricQuartetLogDerivativeContribution m tau a
              (symmetricPickPole (-x) v) +
            background (symmetricPickPole (-x) v) :=
        hdecompose (symmetricPickPole (-x) v)
      _ = -Complex.I := hpoleMinus
  have hrootMinus :
      (finiteEPolynomial A η).eval (symmetricPickPole (-x) v) = 0 :=
    (finiteNegativeLogDerivativeValue_eq_neg_I_iff hAPoleMinus).mp hfiniteMinus
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound
      hA hη hm htau ha hv hx hrootPlus hrootMinus hdegree hAPlus hAMinus
      hupperPlus hupperMinus hbackground hpole hreflect

/-- Evenness of the real base polynomial discharges every reflection
hypothesis in the logarithmic-derivative quartet theorem.  It forces the
second symmetric zero of `A`, background reflection through the exact
decomposition, the second pole denominator to be nonzero, and the
residual-inner reflected-value identity.  The decomposition and pole equation
already force the first denominator to be nonzero; this in turn proves both
pseudo-hyperbolic numerator squares positive from the two zero values of `A`.
Thus the positive pole equation is the only local pole assumption. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    {η m tau a x v : ℝ} {background : ℂ → ℂ}
    (hη : η ≠ 0) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hdegree : (upperRootFactor
      (finiteEPolynomial A η)).natDegree = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hdecompose : ∀ z,
      finiteNegativeLogDerivativeValue A η z =
        symmetricQuartetLogDerivativeContribution m tau a z + background z)
    (hbackground : 0 ≤ (background (symmetricPickPole x v)).im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (symmetricPickPole x v) +
      background (symmetricPickPole x v) = -Complex.I) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hfinitePlus :
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
        -Complex.I := by
    calc
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
          symmetricQuartetLogDerivativeContribution m tau a
              (symmetricPickPole x v) +
            background (symmetricPickPole x v) :=
        hdecompose (symmetricPickPole x v)
      _ = -Complex.I := hpole
  have hAPolePlus : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0 :=
    finiteNegativeLogDerivativeValue_denominator_ne_zero_of_eq_neg_I
      hfinitePlus
  have hAlphaNegConj :
      negConj (symmetricPickAlphaPlus tau a) =
        symmetricPickAlphaMinus tau a := by
    simp [negConj, symmetricPickAlphaPlus, symmetricPickAlphaMinus]
  have hAMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaMinus tau a) = 0 := by
    rw [← hAlphaNegConj,
      realPolynomial_eval₂_negConj_eq_conj_of_even hEven, hAPlus, map_zero]
  have hpoleNeAlphaPlus :
      symmetricPickPole x v ≠ symmetricPickAlphaPlus tau a := by
    intro heq
    apply hAPolePlus
    rw [heq]
    exact hAPlus
  have hpoleNeAlphaMinus :
      symmetricPickPole x v ≠ symmetricPickAlphaMinus tau a := by
    intro heq
    apply hAPolePlus
    rw [heq]
    exact hAMinus
  have hupperPlus : 0 < pairHyperbolicUpperSq (x - tau) v a :=
    pairHyperbolicUpperSq_pos_of_upperHalfPlanePoint_ne (by
      simpa [symmetricPickPole, symmetricPickAlphaPlus] using
        hpoleNeAlphaPlus)
  have hupperMinus : 0 < pairHyperbolicUpperSq (x + tau) v a := by
    have h := pairHyperbolicUpperSq_pos_of_upperHalfPlanePoint_ne (by
      simpa [symmetricPickPole, symmetricPickAlphaMinus] using
        hpoleNeAlphaMinus)
    rw [← sub_neg_eq_add]
    exact h
  have hPoleNegConj :
      negConj (symmetricPickPole x v) = symmetricPickPole (-x) v := by
    simp [negConj]
  have hAPoleMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickPole (-x) v) ≠ 0 := by
    rw [← hPoleNegConj,
      realPolynomial_eval₂_negConj_eq_conj_of_even hEven]
    intro hzero
    apply hAPolePlus
    have hstar := congrArg (starRingEnd ℂ) hzero
    simpa using hstar
  have hbackgroundReflect :
      background (symmetricPickPole (-x) v) =
        -starRingEnd ℂ (background (symmetricPickPole x v)) := by
    rw [← hPoleNegConj]
    exact logDerivativeBackground_negConj
      hEven η m tau a background hdecompose (symmetricPickPole x v)
  have hreflect :
      lowerRootInnerValue (finiteEPolynomial A η)
          (symmetricPickPole (-x) v) =
        starRingEnd ℂ
          (lowerRootInnerValue (finiteEPolynomial A η)
            (symmetricPickPole x v)) := by
    rw [← hPoleNegConj]
    exact finiteE_lowerRootInnerValue_negConj_eq_conj
      hEven η (symmetricPickPole x v)
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_logDerivativeDecomposition
      hA hη hm htau ha hv hx hdegree hAPlus hAMinus hAPolePlus
      hAPoleMinus hdecompose hupperPlus hupperMinus hbackground hpole
      hbackgroundReflect hreflect

/-- An even separable quartic with one genuinely off-axis upper root has
exactly two upper roots at the zero homotopy endpoint.  The reflected upper
root supplies the lower bound; the general real-polynomial upper/lower count
bound and degree four supply the upper bound. -/
theorem finiteEPolynomial_zero_upperRootCount_eq_two_of_quartic_even_root
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4) {tau a : ℝ}
    (htau : tau ≠ 0) (ha : 0 < a)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0) :
    upperHalfPlaneRootCount (finiteEPolynomial A 0) = 2 := by
  have hAlphaNegConj :
      negConj (symmetricPickAlphaPlus tau a) =
        symmetricPickAlphaMinus tau a := by
    simp [negConj, symmetricPickAlphaPlus, symmetricPickAlphaMinus]
  have hAMinus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaMinus tau a) = 0 := by
    rw [← hAlphaNegConj,
      realPolynomial_eval₂_negConj_eq_conj_of_even hEven, hAPlus, map_zero]
  have hrootPlus : (finiteEPolynomial A 0).eval
      (symmetricPickAlphaPlus tau a) = 0 := by
    simpa using hAPlus
  have hrootMinus : (finiteEPolynomial A 0).eval
      (symmetricPickAlphaMinus tau a) = 0 := by
    simpa using hAMinus
  have himPlus : 0 < (symmetricPickAlphaPlus tau a).im := by
    simpa [symmetricPickAlphaPlus, upperHalfPlanePoint] using ha
  have himMinus : 0 < (symmetricPickAlphaMinus tau a).im := by
    simpa [symmetricPickAlphaMinus, upperHalfPlanePoint] using ha
  have hfactorPlus :
      (upperRootFactor (finiteEPolynomial A 0)).eval
          (symmetricPickAlphaPlus tau a) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero 0) himPlus hrootPlus
  have hfactorMinus :
      (upperRootFactor (finiteEPolynomial A 0)).eval
          (symmetricPickAlphaMinus tau a) = 0 :=
    upperRootFactor_eval_eq_zero_of_eval_eq_zero
      (finiteEPolynomial_ne_zero hA.ne_zero 0) himMinus hrootMinus
  have hne :
      symmetricPickAlphaPlus tau a ≠ symmetricPickAlphaMinus tau a := by
    simpa [symmetricPickPole, symmetricPickAlphaPlus,
      symmetricPickAlphaMinus] using
        symmetricPickPole_ne_reflected_of_ne_zero (v := a) htau
  let q := upperRootFactor (finiteEPolynomial A 0)
  have hq : q ≠ 0 := upperRootFactor_ne_zero _
  have hsubset :
      ({symmetricPickAlphaPlus tau a,
          symmetricPickAlphaMinus tau a} : Finset ℂ) ⊆
        q.roots.toFinset := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Multiset.mem_toFinset]
    rcases hw with rfl | rfl
    · exact (mem_roots hq).mpr hfactorPlus
    · exact (mem_roots hq).mpr hfactorMinus
  have htwoToFinset : 2 ≤ q.roots.toFinset.card := by
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_pair hne] at hcard
    exact hcard
  have htwoRoots : 2 ≤ q.roots.card :=
    htwoToFinset.trans q.roots.toFinset_card_le
  have hlower : 2 ≤
      upperHalfPlaneRootCount (finiteEPolynomial A 0) := by
    rw [← upperRootFactor_natDegree]
    change 2 ≤ q.natDegree
    rw [← IsAlgClosed.card_roots_eq_natDegree]
    exact htwoRoots
  have hupper :
      upperHalfPlaneRootCount (finiteEPolynomial A 0) ≤ 2 := by
    have htwice := twice_finiteEPolynomial_zero_upper_le_natDegree hA.ne_zero
    rw [hdegreeA] at htwice
    omega
  exact le_antisymm hupper hlower

/-- Positive-parameter root-count invariance replaces the raw degree-two
hypothesis by the corresponding upper-root count of the base polynomial at
the zero endpoint. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition_baseCount
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    {η m tau a x v : ℝ} {background : ℂ → ℂ}
    (hη : 0 < η) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hbaseCount :
      upperHalfPlaneRootCount (finiteEPolynomial A 0) = 2)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hdecompose : ∀ z,
      finiteNegativeLogDerivativeValue A η z =
        symmetricQuartetLogDerivativeContribution m tau a z + background z)
    (hbackground : 0 ≤ (background (symmetricPickPole x v)).im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (symmetricPickPole x v) +
      background (symmetricPickPole x v) = -Complex.I) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hdegree :
      (upperRootFactor (finiteEPolynomial A η)).natDegree = 2 := by
    rw [upperRootFactor_natDegree,
      finiteEPolynomial_upperRootCount_eq_zero_of_pos hA hη,
      hbaseCount]
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition
      hA hEven hη.ne' hm htau ha hv hx hdegree hAPlus hdecompose
      hbackground hpole

/-- Fully structural isolated-quartet version of the finite Hardy estimate.
For an even separable quartic, the one named upper zero and its positivity
data determine the zero-endpoint root count, so no root or factor degree is
assumed anywhere in this statement. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_quartic_logDerivativeDecomposition
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4)
    {η m tau a x v : ℝ} {background : ℂ → ℂ}
    (hη : 0 < η) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hdecompose : ∀ z,
      finiteNegativeLogDerivativeValue A η z =
        symmetricQuartetLogDerivativeContribution m tau a z + background z)
    (hbackground : 0 ≤ (background (symmetricPickPole x v)).im)
    (hpole : symmetricQuartetLogDerivativeContribution m tau a
        (symmetricPickPole x v) +
      background (symmetricPickPole x v) = -Complex.I) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hbaseCount :
      upperHalfPlaneRootCount (finiteEPolynomial A 0) = 2 :=
    finiteEPolynomial_zero_upperRootCount_eq_two_of_quartic_even_root
      hA hEven hdegreeA htau ha hAPlus
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_logDerivativeDecomposition_baseCount
      hA hEven hη hm htau ha hv hx hbaseCount hAPlus hdecompose
      hbackground hpole

/-- Direct finite isolated-quartet frontier.  Naming a symmetric upper root of
`A + I eta A'` makes the pole equation automatic.  The background is the
literal residual obtained by subtracting the named quartet, so its
decomposition is definitional.  The only substantive analytic input left is
nonnegativity of that residual's imaginary part at the selected pole. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_quartic_E_root
    {A : ℝ[X]} (hA : A.Separable) (hEven : A.comp (-X) = A)
    (hdegreeA : A.natDegree = 4)
    {η m tau a x v : ℝ}
    (hη : 0 < η) (hm : 0 < m) (htau : tau ≠ 0)
    (ha : 0 < a) (hv : 0 < v) (hx : x ≠ 0)
    (hAPlus : A.eval₂ Complex.ofRealHom
      (symmetricPickAlphaPlus tau a) = 0)
    (hroot : (finiteEPolynomial A η).eval
      (symmetricPickPole x v) = 0)
    (hbackground : 0 ≤
      (finiteQuartetLogDerivativeBackground A η m tau a
        (symmetricPickPole x v)).im) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A η).toLinearMap).re <
      m ^ 2 / (m ^ 2 + a ^ 2) := by
  have hAPole : A.eval₂ Complex.ofRealHom
      (symmetricPickPole x v) ≠ 0 :=
    finiteE_root_base_eval_ne_zero hA hη.ne' hroot
  have hvalue :
      finiteNegativeLogDerivativeValue A η (symmetricPickPole x v) =
        -Complex.I :=
    (finiteNegativeLogDerivativeValue_eq_neg_I_iff hAPole).mpr hroot
  have hpole : symmetricQuartetLogDerivativeContribution m tau a
        (symmetricPickPole x v) +
      finiteQuartetLogDerivativeBackground A η m tau a
        (symmetricPickPole x v) = -Complex.I := by
    calc
      symmetricQuartetLogDerivativeContribution m tau a
            (symmetricPickPole x v) +
          finiteQuartetLogDerivativeBackground A η m tau a
            (symmetricPickPole x v) =
          finiteNegativeLogDerivativeValue A η
            (symmetricPickPole x v) := by
        unfold finiteQuartetLogDerivativeBackground
        ring
      _ = -Complex.I := hvalue
  exact
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_lt_quartetBound_of_even_quartic_logDerivativeDecomposition
      hA hEven hdegreeA hη hm htau ha hv hx hAPlus
      (finiteNegativeLogDerivativeValue_eq_quartet_add_background
        A η m tau a) hbackground hpole

end

end RiemannGaussian
