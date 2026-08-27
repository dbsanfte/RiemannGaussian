import RiemannGaussian.FiniteHardyMultipointScalar
import RiemannGaussian.FiniteHardyInsideCoreBridge

/-!
# Rational cancellation for the finite multipoint Pick argument

This file represents a common disk transform of two rational functions by
explicit numerator and denominator polynomials.  It then proves that every
inside-core interpolation node is an actual numerator root and that the
complete core-root polynomial divides the transformed difference numerator.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-- Polynomial numerator obtained by applying a disk automorphism to a
rational value `N / D`. -/
def unitDiskTransformNumerator (a : ℂ) (N D : ℂ[X]) : ℂ[X] :=
  N - C a * D

/-- Polynomial denominator obtained by applying a disk automorphism to a
rational value `N / D`. -/
def unitDiskTransformDenominator (a : ℂ) (N D : ℂ[X]) : ℂ[X] :=
  D - C (starRingEnd ℂ a) * N

/-- Cross-multiplied numerator of the difference between two rational
functions after applying the same disk automorphism. -/
def commonUnitDiskTransformDifferenceNumerator
    (a : ℂ) (N₀ D₀ N₁ D₁ : ℂ[X]) : ℂ[X] :=
  unitDiskTransformNumerator a N₀ D₀ *
      unitDiskTransformDenominator a N₁ D₁ -
    unitDiskTransformNumerator a N₁ D₁ *
      unitDiskTransformDenominator a N₀ D₀

/-- Cross-multiplied denominator of the same common-transform difference. -/
def commonUnitDiskTransformDifferenceDenominator
    (a : ℂ) (N₀ D₀ N₁ D₁ : ℂ[X]) : ℂ[X] :=
  unitDiskTransformDenominator a N₀ D₀ *
    unitDiskTransformDenominator a N₁ D₁

/-- Evaluation of a disk automorphism on a rational value is represented by
the transformed numerator and denominator polynomials. -/
theorem unitDiskAutomorphism_div_eq_transform_eval
    {a : ℂ} {N D : ℂ[X]} {z : ℂ}
    (hD : D.eval z ≠ 0)
    (htrans : (unitDiskTransformDenominator a N D).eval z ≠ 0) :
    unitDiskAutomorphism a (N.eval z / D.eval z) =
      (unitDiskTransformNumerator a N D).eval z /
        (unitDiskTransformDenominator a N D).eval z := by
  have htrans' : D.eval z - starRingEnd ℂ a * N.eval z ≠ 0 := by
    simpa [unitDiskTransformDenominator] using htrans
  unfold unitDiskAutomorphism unitDiskTransformNumerator
    unitDiskTransformDenominator
  simp only [eval_sub, eval_mul, eval_C]
  field_simp [hD, htrans']

/-- Exact rational evaluation of the commonly transformed difference. -/
theorem commonUnitDiskTransformDifference_eq_div_eval
    {a : ℂ} {N₀ D₀ N₁ D₁ : ℂ[X]} {z : ℂ}
    (hD₀ : D₀.eval z ≠ 0) (hD₁ : D₁.eval z ≠ 0)
    (htrans₀ : (unitDiskTransformDenominator a N₀ D₀).eval z ≠ 0)
    (htrans₁ : (unitDiskTransformDenominator a N₁ D₁).eval z ≠ 0) :
    unitDiskAutomorphism a (N₀.eval z / D₀.eval z) -
        unitDiskAutomorphism a (N₁.eval z / D₁.eval z) =
      (commonUnitDiskTransformDifferenceNumerator a N₀ D₀ N₁ D₁).eval z /
        (commonUnitDiskTransformDifferenceDenominator a N₀ D₀ N₁ D₁).eval z := by
  rw [unitDiskAutomorphism_div_eq_transform_eval hD₀ htrans₀,
    unitDiskAutomorphism_div_eq_transform_eval hD₁ htrans₁]
  unfold commonUnitDiskTransformDifferenceNumerator
    commonUnitDiskTransformDifferenceDenominator
  simp only [eval_sub, eval_mul]
  field_simp [htrans₀, htrans₁]

/-- The transformed denominator stays nonzero whenever the original rational
denominator is nonzero, the automorphism center is interior, and the rational
value lies in the closed disk. -/
theorem unitDiskTransformDenominator_eval_ne_zero
    {a : ℂ} {N D : ℂ[X]} {z : ℂ}
    (ha : ‖a‖ < 1) (hD : D.eval z ≠ 0)
    (hvalue : ‖N.eval z / D.eval z‖ ≤ 1) :
    (unitDiskTransformDenominator a N D).eval z ≠ 0 := by
  have hauto := unitDiskAutomorphism_denominator_ne_zero ha hvalue
  intro hzero
  apply hauto
  unfold unitDiskTransformDenominator at hzero
  simp only [eval_sub, eval_mul, eval_C] at hzero
  field_simp [hD]
  simpa using hzero

/-- Equal original rational values force a zero of the common-transform
difference numerator.  No analytic or nonvanishing assertion about the
transformed denominators is hidden in this algebraic statement. -/
theorem commonUnitDiskTransformDifferenceNumerator_eval_eq_zero_of_div_eq
    {a : ℂ} {N₀ D₀ N₁ D₁ : ℂ[X]} {z : ℂ}
    (hD₀ : D₀.eval z ≠ 0) (hD₁ : D₁.eval z ≠ 0)
    (heq : N₀.eval z / D₀.eval z = N₁.eval z / D₁.eval z) :
    (commonUnitDiskTransformDifferenceNumerator a N₀ D₀ N₁ D₁).eval z =
      0 := by
  have hcross : N₀.eval z * D₁.eval z = N₁.eval z * D₀.eval z :=
    (div_eq_div_iff hD₀ hD₁).mp heq
  unfold commonUnitDiskTransformDifferenceNumerator
    unitDiskTransformNumerator unitDiskTransformDenominator
  simp only [eval_sub, eval_mul, eval_C]
  linear_combination (1 - a * starRingEnd ℂ a) * hcross

/-- A complete distinct multiset of common interpolation nodes divides the
common-transform difference numerator.  This is the exact algebraic
cancellation behind the forthcoming multipoint maximum-modulus estimate. -/
theorem multisetRootPolynomial_dvd_commonUnitDiskTransformDifferenceNumerator
    (a : ℂ) (N₀ D₀ N₁ D₁ : ℂ[X]) (nodes : Multiset ℂ)
    (hnodes : nodes.Nodup)
    (hD₀ : ∀ z ∈ nodes, D₀.eval z ≠ 0)
    (hD₁ : ∀ z ∈ nodes, D₁.eval z ≠ 0)
    (heq : ∀ z ∈ nodes, N₀.eval z / D₀.eval z =
      N₁.eval z / D₁.eval z) :
    (nodes.map fun z => X - C z).prod ∣
      commonUnitDiskTransformDifferenceNumerator a N₀ D₀ N₁ D₁ := by
  let P := commonUnitDiskTransformDifferenceNumerator a N₀ D₀ N₁ D₁
  by_cases hP : P = 0
  · simp [P, hP]
  apply (Multiset.prod_X_sub_C_dvd_iff_le_roots hP nodes).2
  apply (Multiset.le_iff_subset hnodes).2
  intro z hz
  apply (Polynomial.mem_roots hP).2
  exact commonUnitDiskTransformDifferenceNumerator_eval_eq_zero_of_div_eq
    (hD₀ z hz) (hD₁ z hz) (heq z hz)

/-- The named upper residual multiset, and hence every filtered influence
core, has no repetitions because it lies in the roots of a separable base
polynomial. -/
theorem insideInfluenceDiskRoots_nodup_of_root_decomposition
    {A : ℝ[X]} (hA : A.Separable) {z : ℂ}
    {realResidual upperResidual : Multiset ℂ}
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual) :
    (insideInfluenceDiskRoots z upperResidual).Nodup := by
  have hupperLe : upperResidual ≤ (A.map Complex.ofRealHom).roots := by
    calc
      upperResidual ≤ conjugatePairRootMultiset upperResidual := by
        unfold conjugatePairRootMultiset
        exact Multiset.le_add_right _ _
      _ ≤ realResidual + conjugatePairRootMultiset upperResidual :=
        Multiset.le_add_left _ _
      _ = (A.map Complex.ofRealHom).roots := hroots.symm
  exact (Multiset.nodup_of_le hupperLe (nodup_roots hA.map)).filter _

/-! ## Finite Hardy specialization -/

/-- Numerator of the negative residual inner function `-S`. -/
def negativeLowerRootInnerNumerator (p : ℂ[X]) : ℂ[X] :=
  -conjugatePolynomial (lowerRootFactor p)

/-- Denominator of the negative residual inner function `-S`. -/
def negativeLowerRootInnerDenominator (p : ℂ[X]) : ℂ[X] :=
  lowerRootFactor p

/-- The common-transform difference numerator for `-S` and `B` in the
finite polynomial model. -/
def finiteCommonUnitDiskTransformDifferenceNumerator
    (A : ℝ[X]) (tau : ℝ) (a : ℂ) : ℂ[X] :=
  let p := finiteEPolynomial A tau
  commonUnitDiskTransformDifferenceNumerator a
    (negativeLowerRootInnerNumerator p)
    (negativeLowerRootInnerDenominator p)
    (upperRootFactor p)
    (conjugatePolynomial (upperRootFactor p))

/-- Denominator paired with the finite common-transform difference
numerator. -/
def finiteCommonUnitDiskTransformDifferenceDenominator
    (A : ℝ[X]) (tau : ℝ) (a : ℂ) : ℂ[X] :=
  let p := finiteEPolynomial A tau
  commonUnitDiskTransformDifferenceDenominator a
    (negativeLowerRootInnerNumerator p)
    (negativeLowerRootInnerDenominator p)
    (upperRootFactor p)
    (conjugatePolynomial (upperRootFactor p))

theorem negativeLowerRootInnerValue_eq_div
    (p : ℂ[X]) (z : ℂ) :
    (negativeLowerRootInnerNumerator p).eval z /
        (negativeLowerRootInnerDenominator p).eval z =
      -lowerRootInnerValue p z := by
  simp [negativeLowerRootInnerNumerator,
    negativeLowerRootInnerDenominator, lowerRootInnerValue, neg_div]

/-- On the open upper half-plane, the polynomial quotient is exactly the
difference between the two commonly transformed finite inner functions. -/
theorem finiteCommonUnitDiskTransformDifference_eq_div_eval
    (A : ℝ[X]) (tau : ℝ) {a w : ℂ}
    (ha : ‖a‖ < 1) (hw : 0 < w.im) :
    unitDiskAutomorphism a
          (-lowerRootInnerValue (finiteEPolynomial A tau) w) -
        unitDiskAutomorphism a
          (upperRootBlaschkeValue (finiteEPolynomial A tau) w) =
      (finiteCommonUnitDiskTransformDifferenceNumerator A tau a).eval w /
        (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval w := by
  let p := finiteEPolynomial A tau
  have hD₀ : (negativeLowerRootInnerDenominator p).eval w ≠ 0 :=
    lowerRootFactor_eval_ne_zero_of_im_pos p hw
  have hD₁ : (conjugatePolynomial (upperRootFactor p)).eval w ≠ 0 :=
    conjugate_upperRootFactor_eval_ne_zero_of_im_pos p hw
  have htrans₀ :
      (unitDiskTransformDenominator a
        (negativeLowerRootInnerNumerator p)
        (negativeLowerRootInnerDenominator p)).eval w ≠ 0 := by
    apply unitDiskTransformDenominator_eval_ne_zero ha hD₀
    rw [negativeLowerRootInnerValue_eq_div, norm_neg]
    exact norm_lowerRootInnerValue_le_one p hw
  have htrans₁ :
      (unitDiskTransformDenominator a (upperRootFactor p)
        (conjugatePolynomial (upperRootFactor p))).eval w ≠ 0 := by
    apply unitDiskTransformDenominator_eval_ne_zero ha hD₁
    exact norm_upperRootBlaschkeValue_le_one p hw
  have hidentity := commonUnitDiskTransformDifference_eq_div_eval
    hD₀ hD₁ htrans₀ htrans₁
  simpa [p, negativeLowerRootInnerValue_eq_div,
    upperRootBlaschkeValue, finiteCommonUnitDiskTransformDifferenceNumerator,
    finiteCommonUnitDiskTransformDifferenceDenominator] using hidentity

/-- Every inside-core interpolation occurrence is a literal polynomial
factor of the common-transform difference numerator. -/
theorem insideInfluenceDiskRootPolynomial_dvd_finiteCommonTransformDifference
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z : ℂ} {realResidual upperResidual : Multiset ℂ}
    (hroots : (A.map Complex.ofRealHom).roots =
      realResidual + conjugatePairRootMultiset upperResidual)
    (halpha : ∀ alpha ∈ upperResidual, 0 < alpha.im)
    (a : ℂ) :
    ((insideInfluenceDiskRoots z upperResidual).map fun alpha =>
        X - C alpha).prod ∣
      finiteCommonUnitDiskTransformDifferenceNumerator A tau a := by
  let core := insideInfluenceDiskRoots z upperResidual
  let p := finiteEPolynomial A tau
  apply multisetRootPolynomial_dvd_commonUnitDiskTransformDifferenceNumerator
    a (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p)
      (upperRootFactor p) (conjugatePolynomial (upperRootFactor p)) core
  · exact insideInfluenceDiskRoots_nodup_of_root_decomposition hA hroots
  · intro alpha halphaCore
    exact lowerRootFactor_eval_ne_zero_of_im_pos p
      (halpha alpha (Multiset.mem_of_mem_filter halphaCore))
  · intro alpha halphaCore
    exact conjugate_upperRootFactor_eval_ne_zero_of_im_pos p
      (halpha alpha (Multiset.mem_of_mem_filter halphaCore))
  · intro alpha halphaCore
    rw [negativeLowerRootInnerValue_eq_div]
    change -finiteInnerValue A tau alpha = finiteBlaschkeValue A tau alpha
    rw [finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root hA htau
      (base_eval_eq_zero_of_mem_upperResidual hA hroots
        (Multiset.mem_of_mem_filter halphaCore))]
    simp

end

end RiemannGaussian
