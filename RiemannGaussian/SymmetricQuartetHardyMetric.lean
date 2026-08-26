import RiemannGaussian.FiniteHardyCauchyBasis
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

end

end RiemannGaussian
