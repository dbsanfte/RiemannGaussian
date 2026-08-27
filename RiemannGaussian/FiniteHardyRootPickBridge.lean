import RiemannGaussian.FiniteHardySchwarzPick
import RiemannGaussian.FiniteHardyConfluentDeterminant
import RiemannGaussian.WeightedHyperbolicEnergy

/-!
# Root-level Pick bridge for the finite Hardy determinant

This file connects three previously separate finite objects:

* the residual-inner Schwarz--Pick contraction;
* the upper-root Blaschke product and its interpolation relation with the
  residual inner function at roots of the real base polynomial;
* the unconditional confluent Hardy determinant.

For an upper root `z` of `E = A + i*tau*A'` and an upper-half-plane root
`alpha` of `A`, the resulting theorem bounds the complete square-root Hardy
determinant by the Cayley transform of the pseudo-hyperbolic distance from
`z` to `alpha`.  Every product estimate below retains root multiplicities.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

open scoped ComplexConjugate

/-- Norm-square quotient form of the residual-inner Schwarz--Pick
contraction.  The zero output-denominator case is handled explicitly. -/
theorem lowerRootInnerValue_schwarzPick_normSq
    (p : ℂ[X]) {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) :
    Complex.normSq
        ((lowerRootInnerValue p z - lowerRootInnerValue p a) /
          (1 - lowerRootInnerValue p z *
            starRingEnd ℂ (lowerRootInnerValue p a))) ≤
      Complex.normSq ((z - a) / (z - starRingEnd ℂ a)) := by
  have hcross := lowerRootInnerValue_schwarzPick_cross p hz ha
  let A := Complex.normSq (z - starRingEnd ℂ a)
  let B := Complex.normSq (z - a)
  let C := Complex.normSq
    (1 - lowerRootInnerValue p z *
      starRingEnd ℂ (lowerRootInnerValue p a))
  let D := Complex.normSq
    (lowerRootInnerValue p z - lowerRootInnerValue p a)
  have hA : 0 < A := Complex.normSq_pos.mpr
    (sub_conj_ne_zero_of_im_pos hz ha)
  rw [Complex.normSq_div, Complex.normSq_div]
  change D / C ≤ B / A
  by_cases hCzero : C = 0
  · rw [hCzero, div_zero]
    exact div_nonneg (Complex.normSq_nonneg _) hA.le
  · have hC : 0 < C := lt_of_le_of_ne
      (Complex.normSq_nonneg _) (Ne.symm hCzero)
    exact (div_le_div_iff₀ hC hA).2 (by
      simpa [A, B, C, D, mul_comm] using hcross)

/-- Norm quotient form of the residual-inner Schwarz--Pick contraction. -/
theorem lowerRootInnerValue_schwarzPick_norm
    (p : ℂ[X]) {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) :
    ‖(lowerRootInnerValue p z - lowerRootInnerValue p a) /
          (1 - lowerRootInnerValue p z *
            starRingEnd ℂ (lowerRootInnerValue p a))‖ ≤
      upperHalfPlanePseudoHyperbolicDistance z a := by
  rw [upperHalfPlanePseudoHyperbolicDistance]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm]
  exact lowerRootInnerValue_schwarzPick_normSq p hz ha

/-- At an arbitrary upper-half-plane evaluation point, the complete
upper-root Blaschke product is bounded by the factor belonging to any chosen
upper root.  The selected occurrence is removed from the root multiset, so
the statement remains valid with repeated roots. -/
theorem norm_upperRootBlaschkeValue_le_pseudoHyperbolicDistance_of_root
    (p : ℂ[X]) {z a : ℂ}
    (hz : z ∈ (upperRootFactor p).roots) (ha : 0 < a.im) :
    ‖upperRootBlaschkeValue p a‖ ≤
      upperHalfPlanePseudoHyperbolicDistance a z := by
  obtain ⟨rest, hroots⟩ := Multiset.exists_cons_of_mem hz
  have hrest : ∀ w ∈ rest, 0 < w.im := by
    intro w hw
    have hwfull : w ∈ (upperRootFactor p).roots := by
      rw [hroots]
      simp [hw]
    rw [upperRootFactor_roots, Multiset.mem_filter] at hwfull
    exact hwfull.2
  have hnorm : ∀ s : Multiset ℂ,
      (∀ w ∈ s, 0 < w.im) →
        ‖(s.map fun w ↦ (a - w) / (a - starRingEnd ℂ w)).prod‖ ≤ 1 := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons w s ih =>
        have hw : 0 < w.im := hs w (by simp)
        have hsTail : ∀ y ∈ s, 0 < y.im := by
          intro y hy
          exact hs y (by simp [hy])
        have hdist := norm_sub_lt_norm_sub_conj_of_im_pos ha hw
        simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
        apply mul_le_one₀
        · rw [norm_div]
          exact (div_le_one (norm_pos_iff.mpr
            (sub_conj_ne_zero_of_im_pos ha hw))).2 hdist.le
        · exact norm_nonneg _
        · exact ih hsTail
  have hrestNorm := hnorm rest hrest
  rw [upperRootBlaschkeValue_eq_prod, ← upperRootFactor_roots,
    hroots, Multiset.map_cons, Multiset.prod_cons, norm_mul]
  change ‖(a - z) / (a - starRingEnd ℂ z)‖ *
      ‖(rest.map fun w ↦ (a - w) / (a - starRingEnd ℂ w)).prod‖ ≤
    upperHalfPlanePseudoHyperbolicDistance a z
  rw [upperHalfPlanePseudoHyperbolicDistance]
  exact mul_le_of_le_one_right (norm_nonneg _) hrestNorm

/-- Pseudo-hyperbolic distance in the upper half-plane is symmetric. -/
theorem upperHalfPlanePseudoHyperbolicDistance_comm (z a : ℂ) :
    upperHalfPlanePseudoHyperbolicDistance z a =
      upperHalfPlanePseudoHyperbolicDistance a z := by
  unfold upperHalfPlanePseudoHyperbolicDistance
  rw [norm_div, norm_div, norm_sub_rev z a]
  congr 1
  rw [show a - starRingEnd ℂ z =
      -starRingEnd ℂ (z - starRingEnd ℂ a) by
    simp only [map_sub, starRingEnd_apply, star_star]
    ring,
    norm_neg, Complex.norm_conj]

/-- Exact Pick-disk data at an upper root of `E` and an upper-half-plane root
of `A`: both the interpolated Blaschke value and the residual-inner
pseudo-hyperbolic displacement are bounded by the same input distance. -/
theorem finiteRoot_residualBlaschke_schwarzPick_data
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z alpha : ℂ}
    (hz : z ∈ (upperRootFactor (finiteEPolynomial A tau)).roots)
    (halphaIm : 0 < alpha.im)
    (halphaRoot : A.eval₂ Complex.ofRealHom alpha = 0) :
    ‖finiteBlaschkeValue A tau alpha‖ ≤
        upperHalfPlanePseudoHyperbolicDistance z alpha ∧
      ‖(finiteInnerValue A tau z + finiteBlaschkeValue A tau alpha) /
          (1 + finiteInnerValue A tau z *
            starRingEnd ℂ (finiteBlaschkeValue A tau alpha))‖ ≤
        upperHalfPlanePseudoHyperbolicDistance z alpha := by
  have hzIm : 0 < z.im := by
    have hz' := hz
    rw [upperRootFactor_roots, Multiset.mem_filter] at hz'
    exact hz'.2
  constructor
  · change ‖upperRootBlaschkeValue (finiteEPolynomial A tau) alpha‖ ≤ _
    calc
      ‖upperRootBlaschkeValue (finiteEPolynomial A tau) alpha‖ ≤
          upperHalfPlanePseudoHyperbolicDistance alpha z :=
        norm_upperRootBlaschkeValue_le_pseudoHyperbolicDistance_of_root
          (finiteEPolynomial A tau) hz halphaIm
      _ = upperHalfPlanePseudoHyperbolicDistance z alpha :=
        upperHalfPlanePseudoHyperbolicDistance_comm alpha z
  · have hsp := lowerRootInnerValue_schwarzPick_norm
      (finiteEPolynomial A tau) hzIm halphaIm
    change
      ‖(finiteInnerValue A tau z - finiteInnerValue A tau alpha) /
          (1 - finiteInnerValue A tau z *
            starRingEnd ℂ (finiteInnerValue A tau alpha))‖ ≤
        upperHalfPlanePseudoHyperbolicDistance z alpha at hsp
    rw [finiteInnerValue_eq_neg_finiteBlaschkeValue_at_root
      hA htau halphaRoot] at hsp
    simpa only [sub_neg_eq_add, map_neg, mul_neg, sub_neg_eq_add] using hsp

/-- Scalar terminal theorem for a pseudo-hyperbolic value disk.  If both the
disk center and radius are bounded by `r < 1`, and the target value is in the
closed unit disk, then its norm is at most `2*r/(1+r^2)`. -/
theorem norm_le_two_mul_div_one_add_sq_of_pseudoHyperbolicDisk
    {s b : ℂ} {r : ℝ} (hr : 0 ≤ r) (hrone : r < 1)
    (hsone : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ r)
    (hdisk : ‖(s + b) / (1 + s * starRingEnd ℂ b)‖ ≤ r) :
    ‖s‖ ≤ 2 * r / (1 + r ^ 2) := by
  let x := ‖s‖
  let y := ‖b‖
  let t := (s * starRingEnd ℂ b).re
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hyr : y ≤ r := hb
  have hrle : r ≤ 1 := hrone.le
  have hprodlt : ‖s * starRingEnd ℂ b‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      x * y ≤ 1 * r := mul_le_mul hsone hyr hy (by norm_num)
      _ = r := one_mul r
      _ < 1 := hrone
  have hden : 1 + s * starRingEnd ℂ b ≠ 0 := by
    intro hzero
    have hvalue : s * starRingEnd ℂ b = -1 := by
      linear_combination hzero
    rw [hvalue, norm_neg, norm_one] at hprodlt
    exact lt_irrefl 1 hprodlt
  rw [norm_div] at hdisk
  have hdenNorm : 0 < ‖1 + s * starRingEnd ℂ b‖ :=
    norm_pos_iff.mpr hden
  have hnum : ‖s + b‖ ≤ r * ‖1 + s * starRingEnd ℂ b‖ :=
    (div_le_iff₀ hdenNorm).mp hdisk
  have hright : 0 ≤ r * ‖1 + s * starRingEnd ℂ b‖ :=
    mul_nonneg hr (norm_nonneg _)
  have hsq : ‖s + b‖ ^ 2 ≤
      (r * ‖1 + s * starRingEnd ℂ b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hright).2 hnum
  rw [Complex.sq_norm, mul_pow, Complex.sq_norm,
    Complex.normSq_add, Complex.normSq_add, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_conj] at hsq
  simp only [one_mul, map_mul, starRingEnd_apply, star_star] at hsq
  simp only [Complex.normSq_eq_norm_sq] at hsq
  have htstar : (star s * b).re = t := by
    dsimp only [t]
    simp [Complex.mul_re]
  rw [htstar] at hsq
  have htleft : (s * star b).re = t := by rfl
  rw [htleft] at hsq
  change x ^ 2 + y ^ 2 + 2 * t ≤
    r ^ 2 * (1 + x ^ 2 * y ^ 2 + 2 * t) at hsq
  have ht : -x * y ≤ t := by
    have habs := Complex.abs_re_le_norm (s * starRingEnd ℂ b)
    rw [norm_mul, Complex.norm_conj] at habs
    change |t| ≤ x * y at habs
    simpa only [neg_mul] using (abs_le.mp habs).1
  have hcoeff : 0 ≤ 1 - r ^ 2 := by nlinarith
  have htadd : 0 ≤ t + x * y := by linarith
  have hnonneg := mul_nonneg hcoeff htadd
  have hkey : (x - y) ^ 2 ≤ r ^ 2 * (1 - x * y) ^ 2 := by
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 1 + r ^ 2)).2
  change x * (1 + r ^ 2) ≤ 2 * r
  by_cases hxy : x ≤ y
  · have hcoef : 1 + r ^ 2 ≤ 2 := by nlinarith
    calc
      x * (1 + r ^ 2) = (1 + r ^ 2) * x := by ring
      _ ≤ 2 * x :=
        mul_le_mul_of_nonneg_right hcoef hx
      _ ≤ 2 * r := by linarith
  · have hyx : y < x := lt_of_not_ge hxy
    have hleft : 0 ≤ x - y := sub_nonneg.mpr hyx.le
    have hxyOne : x * y ≤ 1 := by
      calc
        x * y ≤ 1 * r := mul_le_mul hsone hyr hy (by norm_num)
        _ = r := one_mul r
        _ ≤ 1 := hrle
    have hright' : 0 ≤ r * (1 - x * y) :=
      mul_nonneg hr (sub_nonneg.mpr hxyOne)
    have hlinear : x - y ≤ r * (1 - x * y) := by
      apply (sq_le_sq₀ hleft hright').mp
      simpa [mul_pow] using hkey
    have hfirst : 0 ≤ r + y - x * (1 + r * y) := by
      nlinarith
    have hrx : r * x ≤ 1 := by
      calc
        r * x ≤ 1 * 1 := mul_le_mul hrle hsone hx (by norm_num)
        _ = 1 := one_mul 1
    have hsecond : 0 ≤ (r - y) * (1 - r * x) :=
      mul_nonneg (sub_nonneg.mpr hyr) (sub_nonneg.mpr hrx)
    nlinarith

/-- A single upper-half-plane base root controls the residual-inner value at
any chosen upper root of `E` by the sharp one-disk Cayley bound. -/
theorem finiteInnerValue_at_upperRoot_le_singleBaseRootPickBound
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z alpha : ℂ}
    (hz : z ∈ (upperRootFactor (finiteEPolynomial A tau)).roots)
    (halphaIm : 0 < alpha.im)
    (halphaRoot : A.eval₂ Complex.ofRealHom alpha = 0) :
    ‖finiteInnerValue A tau z‖ ≤
      2 * upperHalfPlanePseudoHyperbolicDistance z alpha /
        (1 + upperHalfPlanePseudoHyperbolicDistance z alpha ^ 2) := by
  have hzIm : 0 < z.im := by
    have hz' := hz
    rw [upperRootFactor_roots, Multiset.mem_filter] at hz'
    exact hz'.2
  have hdata := finiteRoot_residualBlaschke_schwarzPick_data
    hA htau hz halphaIm halphaRoot
  apply norm_le_two_mul_div_one_add_sq_of_pseudoHyperbolicDisk
    (norm_nonneg _)
    (upperHalfPlanePseudoHyperbolicDistance_lt_one hzIm halphaIm)
  · exact norm_lowerRootInnerValue_le_one (finiteEPolynomial A tau) hzIm
  · exact hdata.1
  · exact hdata.2

/-- Root-level bridge to the complete finite Hardy determinant.  A chosen
upper root of `E` and any upper-half-plane root of `A` give an explicit
pseudo-hyperbolic upper bound for the actual complement Gram determinant. -/
theorem
    finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_singleBaseRootPickBound
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {z alpha : ℂ}
    (hz : z ∈ (upperRootFactor (finiteEPolynomial A tau)).roots)
    (halphaIm : 0 < alpha.im)
    (halphaRoot : A.eval₂ Complex.ofRealHom alpha = 0) :
    Real.sqrt
        (LinearMap.det
          (finiteHardyCrossAngleComplementGramOperator A tau).toLinearMap).re ≤
      2 * upperHalfPlanePseudoHyperbolicDistance z alpha /
        (1 + upperHalfPlanePseudoHyperbolicDistance z alpha ^ 2) := by
  exact
    (finiteHardyCrossAngleComplementGramOperator_sqrt_det_re_le_innerValue_of_mem
      A tau hz).trans
        (finiteInnerValue_at_upperRoot_le_singleBaseRootPickBound
          hA htau hz halphaIm halphaRoot)

end

end RiemannGaussian
