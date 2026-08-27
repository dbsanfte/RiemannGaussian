import RiemannGaussian.FiniteHardyRationalMaximum

/-!
# Denominator control for the finite multipoint Hardy argument

This file proves that the explicit common disk-transform denominator for
`-S` and `B` has no zeros on the closed upper half-plane.  It also computes
its degree, bounds the numerator degree, and applies the rational maximum
principle to obtain the unfactored global norm bound.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

private theorem star_ne_one_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    starRingEnd ℂ a ≠ 1 := by
  intro h
  have hnorm := congrArg norm h
  simp at hnorm
  linarith

private theorem neg_star_ne_one_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    -starRingEnd ℂ a ≠ 1 := by
  intro h
  have hnorm := congrArg norm h
  simp at hnorm
  linarith

/-- The disk-transform denominator for `-S` retains the degree of the lower
root factor when the automorphism center is strictly inside the disk. -/
theorem negativeLowerRootInnerTransformDenominator_natDegree
    (p : ℂ[X]) {a : ℂ} (ha : ‖a‖ < 1) :
    (unitDiskTransformDenominator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p)).natDegree =
        (lowerRootFactor p).natDegree := by
  have hdegree := natDegree_sub_C_mul_eq_of_monic_sameDegree
    (conjugatePolynomial_monic_of_monic (lowerRootFactor_monic p))
    (lowerRootFactor_monic p)
    (conjugatePolynomial_natDegree (lowerRootFactor p))
    (neg_star_ne_one_of_norm_lt_one ha)
  simpa [negativeLowerRootInnerNumerator,
    negativeLowerRootInnerDenominator, unitDiskTransformDenominator] using hdegree

/-- The disk-transform denominator for `B` retains the degree of the upper
root factor when the automorphism center is strictly inside the disk. -/
theorem upperRootBlaschkeTransformDenominator_natDegree
    (p : ℂ[X]) {a : ℂ} (ha : ‖a‖ < 1) :
    (unitDiskTransformDenominator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p))).natDegree =
        (upperRootFactor p).natDegree := by
  simpa [unitDiskTransformDenominator] using
    natDegree_sub_C_mul_eq_of_monic_sameDegree
    (upperRootFactor_monic p)
    (conjugatePolynomial_monic_of_monic (upperRootFactor_monic p))
    (conjugatePolynomial_natDegree (upperRootFactor p)).symm
    (star_ne_one_of_norm_lt_one ha)

/-- The transformed `-S` denominator has no zero in the closed upper
half-plane.  The proof separately checks the unimodular real boundary and
the contractive open half-plane. -/
theorem negativeLowerRootInnerTransformDenominator_eval_ne_zero
    (p : ℂ[X]) {a w : ℂ} (ha : ‖a‖ < 1) (hw : 0 ≤ w.im) :
    (unitDiskTransformDenominator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p)).eval w ≠ 0 := by
  by_cases hreal : w.im = 0
  · have hwEq : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [hreal]
    rw [hwEq]
    apply unitDiskTransformDenominator_eval_ne_zero ha
      (lowerRootFactor_eval_real_ne_zero p w.re)
    rw [show
      (negativeLowerRootInnerNumerator p).eval (w.re : ℂ) /
          (lowerRootFactor p).eval (w.re : ℂ) =
        -lowerRootInnerValue p (w.re : ℂ) by
          simpa [negativeLowerRootInnerDenominator] using
            negativeLowerRootInnerValue_eq_div p (w.re : ℂ),
      norm_neg, norm_lowerRootInnerValue_real]
  · have him : 0 < w.im := lt_of_le_of_ne hw (Ne.symm hreal)
    apply unitDiskTransformDenominator_eval_ne_zero ha
      (lowerRootFactor_eval_ne_zero_of_im_pos p him)
    rw [show
      (negativeLowerRootInnerNumerator p).eval w /
          (lowerRootFactor p).eval w = -lowerRootInnerValue p w by
          simpa [negativeLowerRootInnerDenominator] using
            negativeLowerRootInnerValue_eq_div p w,
      norm_neg]
    exact norm_lowerRootInnerValue_le_one p him

/-- The transformed `B` denominator has no zero in the closed upper
half-plane. -/
theorem upperRootBlaschkeTransformDenominator_eval_ne_zero
    (p : ℂ[X]) {a w : ℂ} (ha : ‖a‖ < 1) (hw : 0 ≤ w.im) :
    (unitDiskTransformDenominator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p))).eval w ≠ 0 := by
  by_cases hreal : w.im = 0
  · have hwEq : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [hreal]
    rw [hwEq]
    apply unitDiskTransformDenominator_eval_ne_zero ha
      (conjugate_upperRootFactor_eval_real_ne_zero p w.re)
    exact (norm_upperRootBlaschkeValue_real p w.re).le
  · have him : 0 < w.im := lt_of_le_of_ne hw (Ne.symm hreal)
    apply unitDiskTransformDenominator_eval_ne_zero ha
      (conjugate_upperRootFactor_eval_ne_zero_of_im_pos p him)
    exact norm_upperRootBlaschkeValue_le_one p him

/-- The complete common-transform denominator has no zero anywhere on the
closed upper half-plane. -/
theorem finiteCommonUnitDiskTransformDifferenceDenominator_eval_ne_zero
    (A : ℝ[X]) (tau : ℝ) {a w : ℂ}
    (ha : ‖a‖ < 1) (hw : 0 ≤ w.im) :
    (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval w ≠ 0 := by
  let p := finiteEPolynomial A tau
  unfold finiteCommonUnitDiskTransformDifferenceDenominator
    commonUnitDiskTransformDifferenceDenominator
  rw [eval_mul]
  exact mul_ne_zero
    (negativeLowerRootInnerTransformDenominator_eval_ne_zero p ha hw)
    (upperRootBlaschkeTransformDenominator_eval_ne_zero p ha hw)

/-- The common-transform denominator has exactly the sum of the lower- and
upper-root-factor degrees. -/
theorem finiteCommonUnitDiskTransformDifferenceDenominator_natDegree
    (A : ℝ[X]) (tau : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).natDegree =
      (lowerRootFactor (finiteEPolynomial A tau)).natDegree +
        (upperRootFactor (finiteEPolynomial A tau)).natDegree := by
  let p := finiteEPolynomial A tau
  have hneg : unitDiskTransformDenominator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p) ≠ 0 := by
    intro hzero
    have heval := negativeLowerRootInnerTransformDenominator_eval_ne_zero
      p ha (show 0 ≤ (Complex.I : ℂ).im by simp)
    rw [hzero, eval_zero] at heval
    exact heval rfl
  have hupp : unitDiskTransformDenominator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p)) ≠ 0 := by
    intro hzero
    have heval := upperRootBlaschkeTransformDenominator_eval_ne_zero
      p ha (show 0 ≤ (Complex.I : ℂ).im by simp)
    rw [hzero, eval_zero] at heval
    exact heval rfl
  unfold finiteCommonUnitDiskTransformDifferenceDenominator
    commonUnitDiskTransformDifferenceDenominator
  rw [natDegree_mul hneg hupp,
    negativeLowerRootInnerTransformDenominator_natDegree p ha,
    upperRootBlaschkeTransformDenominator_natDegree p ha]

private theorem unitDiskTransformNumerator_natDegree_le
    {N D : ℂ[X]} {n : ℕ}
    (hN : N.natDegree ≤ n) (hD : D.natDegree ≤ n) (a : ℂ) :
    (unitDiskTransformNumerator a N D).natDegree ≤ n := by
  unfold unitDiskTransformNumerator
  exact (natDegree_sub_le _ _).trans <|
    max_le hN (natDegree_C_mul_le a D |>.trans hD)

/-- The common-transform numerator has natural degree no larger than its
explicit denominator. -/
theorem finiteCommonUnitDiskTransformDifferenceNumerator_natDegree_le
    (A : ℝ[X]) (tau : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    (finiteCommonUnitDiskTransformDifferenceNumerator A tau a).natDegree ≤
      (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).natDegree := by
  let p := finiteEPolynomial A tau
  let l := (lowerRootFactor p).natDegree
  let u := (upperRootFactor p).natDegree
  have hnegNum : (unitDiskTransformNumerator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p)).natDegree ≤ l := by
    apply unitDiskTransformNumerator_natDegree_le
    · simp [negativeLowerRootInnerNumerator, l]
    · simp [negativeLowerRootInnerDenominator, l]
  have huppNum : (unitDiskTransformNumerator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p))).natDegree ≤ u := by
    apply unitDiskTransformNumerator_natDegree_le <;> simp [u]
  have hnegDen : (unitDiskTransformDenominator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p)).natDegree ≤ l := by
    rw [negativeLowerRootInnerTransformDenominator_natDegree p ha]
  have huppDen : (unitDiskTransformDenominator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p))).natDegree ≤ u := by
    rw [upperRootBlaschkeTransformDenominator_natDegree p ha]
  have hfirst : (unitDiskTransformNumerator a
      (negativeLowerRootInnerNumerator p)
      (negativeLowerRootInnerDenominator p) *
        unitDiskTransformDenominator a (upperRootFactor p)
          (conjugatePolynomial (upperRootFactor p))).natDegree ≤ l + u :=
    natDegree_mul_le.trans (add_le_add hnegNum huppDen)
  have hsecond : (unitDiskTransformNumerator a (upperRootFactor p)
      (conjugatePolynomial (upperRootFactor p)) *
        unitDiskTransformDenominator a
          (negativeLowerRootInnerNumerator p)
          (negativeLowerRootInnerDenominator p)).natDegree ≤ l + u := by
    calc
      _ ≤ u + l := natDegree_mul_le.trans (add_le_add huppNum hnegDen)
      _ = l + u := add_comm _ _
  rw [finiteCommonUnitDiskTransformDifferenceDenominator_natDegree A tau ha]
  unfold finiteCommonUnitDiskTransformDifferenceNumerator
    commonUnitDiskTransformDifferenceNumerator
  exact (natDegree_sub_le _ _).trans <|
    max_le (by simpa [p, l, u] using hfirst) (by simpa [p, l, u] using hsecond)

/-- The common-transform numerator degree is no larger than the denominator
degree, in the `WithBot` form consumed by the rational maximum principle. -/
theorem finiteCommonUnitDiskTransformDifferenceNumerator_degree_le
    (A : ℝ[X]) (tau : ℝ) {a : ℂ} (ha : ‖a‖ < 1) :
    (finiteCommonUnitDiskTransformDifferenceNumerator A tau a).degree ≤
      (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).degree := by
  have hD : finiteCommonUnitDiskTransformDifferenceDenominator A tau a ≠ 0 := by
    intro hzero
    have heval := finiteCommonUnitDiskTransformDifferenceDenominator_eval_ne_zero
      A tau ha (show 0 ≤ (Complex.I : ℂ).im by simp)
    rw [hzero, eval_zero] at heval
    exact heval rfl
  rw [degree_eq_natDegree hD]
  exact degree_le_of_natDegree_le
    (finiteCommonUnitDiskTransformDifferenceNumerator_natDegree_le A tau ha)

/-- On the real boundary, the explicit common-transform rational difference
has norm at most two because both transformed inner values lie in the disk. -/
theorem finiteCommonUnitDiskTransformDifference_norm_le_two_real
    (A : ℝ[X]) (tau : ℝ) {a : ℂ} (ha : ‖a‖ < 1) (x : ℝ) :
    ‖(finiteCommonUnitDiskTransformDifferenceNumerator A tau a).eval (x : ℂ) /
        (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval
          (x : ℂ)‖ ≤ 2 := by
  let p := finiteEPolynomial A tau
  let N₀ := negativeLowerRootInnerNumerator p
  let D₀ := negativeLowerRootInnerDenominator p
  let N₁ := upperRootFactor p
  let D₁ := conjugatePolynomial (upperRootFactor p)
  have hD₀ : D₀.eval (x : ℂ) ≠ 0 := lowerRootFactor_eval_real_ne_zero p x
  have hD₁ : D₁.eval (x : ℂ) ≠ 0 :=
    conjugate_upperRootFactor_eval_real_ne_zero p x
  have hvalue₀ : ‖N₀.eval (x : ℂ) / D₀.eval (x : ℂ)‖ ≤ 1 := by
    rw [show N₀.eval (x : ℂ) / D₀.eval (x : ℂ) =
        -lowerRootInnerValue p (x : ℂ) by
      simpa [N₀, D₀] using negativeLowerRootInnerValue_eq_div p (x : ℂ),
      norm_neg, norm_lowerRootInnerValue_real]
  have hvalue₁ : ‖N₁.eval (x : ℂ) / D₁.eval (x : ℂ)‖ ≤ 1 := by
    simpa [N₁, D₁, upperRootBlaschkeValue] using
      (norm_upperRootBlaschkeValue_real p x).le
  have htrans₀ : (unitDiskTransformDenominator a N₀ D₀).eval (x : ℂ) ≠ 0 :=
    unitDiskTransformDenominator_eval_ne_zero ha hD₀ hvalue₀
  have htrans₁ : (unitDiskTransformDenominator a N₁ D₁).eval (x : ℂ) ≠ 0 :=
    unitDiskTransformDenominator_eval_ne_zero ha hD₁ hvalue₁
  have hidentity := commonUnitDiskTransformDifference_eq_div_eval
    hD₀ hD₁ htrans₀ htrans₁
  rw [show
    (finiteCommonUnitDiskTransformDifferenceNumerator A tau a).eval (x : ℂ) /
        (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval (x : ℂ) =
      unitDiskAutomorphism a (N₀.eval (x : ℂ) / D₀.eval (x : ℂ)) -
        unitDiskAutomorphism a (N₁.eval (x : ℂ) / D₁.eval (x : ℂ)) by
          simpa [p, N₀, D₀, N₁, D₁,
            finiteCommonUnitDiskTransformDifferenceNumerator,
            finiteCommonUnitDiskTransformDifferenceDenominator] using hidentity.symm]
  calc
    _ ≤ ‖unitDiskAutomorphism a (N₀.eval (x : ℂ) / D₀.eval (x : ℂ))‖ +
        ‖unitDiskAutomorphism a (N₁.eval (x : ℂ) / D₁.eval (x : ℂ))‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_unitDiskAutomorphism_le_one ha hvalue₀)
      (norm_unitDiskAutomorphism_le_one ha hvalue₁)
    _ = 2 := by norm_num

/-- The explicit common-transform rational difference has norm at most two
throughout the closed upper half-plane. -/
theorem finiteCommonUnitDiskTransformDifference_norm_le_two
    (A : ℝ[X]) (tau : ℝ) {a w : ℂ}
    (ha : ‖a‖ < 1) (hw : 0 ≤ w.im) :
    ‖(finiteCommonUnitDiskTransformDifferenceNumerator A tau a).eval w /
        (finiteCommonUnitDiskTransformDifferenceDenominator A tau a).eval w‖ ≤ 2 := by
  exact polynomial_div_norm_le_of_upperHalfPlane_boundary
    (finiteCommonUnitDiskTransformDifferenceNumerator A tau a)
    (finiteCommonUnitDiskTransformDifferenceDenominator A tau a)
    (finiteCommonUnitDiskTransformDifferenceNumerator_degree_le A tau ha)
    (fun z hz =>
      finiteCommonUnitDiskTransformDifferenceDenominator_eval_ne_zero A tau ha hz)
    (finiteCommonUnitDiskTransformDifference_norm_le_two_real A tau ha) hw

end

end RiemannGaussian
