import RiemannGaussian.FiniteRootFactorization
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Direct finite Krein--Langer cancellation

For the finite polynomial model, this file defines the rational functions
`Theta = E^sharp / E`, the upper-root Blaschke factor `B`, and the residual
inner factor `S`.  It proves the exact identity `B * Theta = S` in
`RatFunc ℂ`, so both families of removable factors are cancelled in the
field of rational functions rather than through pointwise division.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The rational Blaschke factor made from the upper roots of `p`. -/
def upperRootBlaschkeRatFunc (p : ℂ[X]) : RatFunc ℂ :=
  RatFunc.mk (upperRootFactor p)
    (conjugatePolynomial (upperRootFactor p))

/-- The rational inner factor made from the lower roots of `p`. -/
def lowerRootInnerRatFunc (p : ℂ[X]) : RatFunc ℂ :=
  RatFunc.mk (conjugatePolynomial (lowerRootFactor p))
    (lowerRootFactor p)

/-- `Theta_tau = E_tau^sharp / E_tau` as a genuine rational function. -/
def finiteThetaRatFunc (A : ℝ[X]) (tau : ℝ) : RatFunc ℂ :=
  RatFunc.mk (finiteESharpPolynomial A tau) (finiteEPolynomial A tau)

/-- Pointwise representative of `Theta_tau`. -/
def finiteThetaValue (A : ℝ[X]) (tau : ℝ) (z : ℂ) : ℂ :=
  (finiteESharpPolynomial A tau).eval z /
    (finiteEPolynomial A tau).eval z

/-- `Theta_tau` is unimodular on the real axis whenever `tau` is nonzero. -/
@[simp] theorem norm_finiteThetaValue_real
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (x : ℝ) :
    ‖finiteThetaValue A tau (x : ℂ)‖ = 1 := by
  have hreflect :
      (finiteESharpPolynomial A tau).eval (x : ℂ) =
        conj ((finiteEPolynomial A tau).eval (x : ℂ)) := by
    simpa using finiteESharpPolynomial_eval_eq_conj A tau (x : ℂ)
  rw [finiteThetaValue, hreflect, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr
      (finiteEPolynomial_no_real_zero hA htau x))]

/-- At every complex zero of `A`, the two finite polynomials are negatives
of one another. -/
theorem finiteESharp_eval_eq_neg_finiteE_at_root
    (A : ℝ[X]) (tau : ℝ) {gamma : ℂ}
    (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (finiteESharpPolynomial A tau).eval gamma =
      -(finiteEPolynomial A tau).eval gamma := by
  rw [finiteESharpPolynomial_eval, finiteEPolynomial_eval, hgamma]
  ring

/-- A zero of separable `A` is not a zero of `E_tau` for nonzero `tau`. -/
theorem finiteE_eval_ne_zero_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    (finiteEPolynomial A tau).eval gamma ≠ 0 := by
  rw [finiteEPolynomial_eval, hgamma, zero_add]
  exact mul_ne_zero
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr htau))
    (hA.eval₂_derivative_ne_zero Complex.ofRealHom hgamma)

/-- Consequently `Theta_tau(gamma) = -1` at every zero `gamma` of `A`. -/
theorem finiteThetaValue_at_root
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {gamma : ℂ} (hgamma : A.eval₂ Complex.ofRealHom gamma = 0) :
    finiteThetaValue A tau gamma = -1 := by
  rw [finiteThetaValue,
    finiteESharp_eval_eq_neg_finiteE_at_root A tau hgamma,
    neg_div, div_self (finiteE_eval_ne_zero_at_root hA htau hgamma)]

/-- The elementary rational-function cancellation used in the direct
Krein--Langer factorization. -/
theorem ratFunc_cancel_two_factors
    {U D V L : ℂ[X]} {c : ℂ}
    (hU : U ≠ 0) (hD : D ≠ 0) (hL : L ≠ 0) (hc : c ≠ 0) :
    RatFunc.mk U D * RatFunc.mk (C c * D * V) (C c * U * L) =
      RatFunc.mk V L := by
  simp only [RatFunc.mk_eq_div, map_mul]
  field_simp [RatFunc.algebraMap_ne_zero hU,
    RatFunc.algebraMap_ne_zero hD,
    RatFunc.algebraMap_ne_zero hL,
    RatFunc.algebraMap_ne_zero (C_ne_zero.mpr hc)]

/-- Conjugating the exact root factorization of `E_tau` gives the matching
factorization of `E_tau^sharp`. -/
theorem finiteESharpPolynomial_eq_rootFactors
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    finiteESharpPolynomial A tau =
      C (finiteEPolynomial A tau).leadingCoeff *
        conjugatePolynomial (upperRootFactor (finiteEPolynomial A tau)) *
        conjugatePolynomial (lowerRootFactor (finiteEPolynomial A tau)) := by
  calc
    finiteESharpPolynomial A tau =
        conjugatePolynomial (finiteEPolynomial A tau) :=
      (finiteEPolynomial_map_conj A tau).symm
    _ = conjugatePolynomial
        (C (finiteEPolynomial A tau).leadingCoeff *
          upperRootFactor (finiteEPolynomial A tau) *
          lowerRootFactor (finiteEPolynomial A tau)) := by
      rw [← finiteEPolynomial_eq_rootFactors hA htau]
    _ = _ := by
      simp [conjugatePolynomial,
        finiteEPolynomial_leadingCoeff hA.ne_zero tau]

/-- Exact direct Krein--Langer cancellation: multiplying `Theta` by its
upper-root Blaschke factor leaves precisely the lower-root inner factor. -/
theorem finiteKreinLanger_cancellation
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    upperRootBlaschkeRatFunc (finiteEPolynomial A tau) *
        finiteThetaRatFunc A tau =
      lowerRootInnerRatFunc (finiteEPolynomial A tau) := by
  let E := finiteEPolynomial A tau
  let Q := finiteESharpPolynomial A tau
  let U := upperRootFactor E
  let D := conjugatePolynomial U
  let L := lowerRootFactor E
  let V := conjugatePolynomial L
  let c := E.leadingCoeff
  have hE : E = C c * U * L := by
    simpa [E, U, L, c] using finiteEPolynomial_eq_rootFactors hA htau
  have hQ : Q = C c * D * V := by
    simpa [E, Q, U, D, L, V, c] using
      finiteESharpPolynomial_eq_rootFactors hA htau
  change RatFunc.mk U D * RatFunc.mk Q E = RatFunc.mk V L
  rw [hE, hQ]
  apply ratFunc_cancel_two_factors
  · exact upperRootFactor_ne_zero E
  · exact conjugatePolynomial_ne_zero (upperRootFactor_ne_zero E)
  · exact lowerRootFactor_ne_zero E
  · exact leadingCoeff_ne_zero.mpr
      (finiteEPolynomial_ne_zero hA.ne_zero tau)

theorem upperRootBlaschkeRatFunc_ne_zero (p : ℂ[X]) :
    upperRootBlaschkeRatFunc p ≠ 0 := by
  rw [upperRootBlaschkeRatFunc, RatFunc.mk_eq_div]
  exact div_ne_zero
    (RatFunc.algebraMap_ne_zero (upperRootFactor_ne_zero p))
    (RatFunc.algebraMap_ne_zero
      (conjugatePolynomial_ne_zero (upperRootFactor_ne_zero p)))

/-- Quotient form of the direct Krein--Langer factorization,
`Theta = S / B`. -/
theorem finiteThetaRatFunc_eq_inner_div_blaschke
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    finiteThetaRatFunc A tau =
      lowerRootInnerRatFunc (finiteEPolynomial A tau) /
        upperRootBlaschkeRatFunc (finiteEPolynomial A tau) := by
  apply (eq_div_iff (upperRootBlaschkeRatFunc_ne_zero
    (finiteEPolynomial A tau))).mpr
  simpa [mul_comm] using finiteKreinLanger_cancellation hA htau

/-- In the upper half-plane, a point is strictly closer to an upper point
than to its conjugate. -/
theorem norm_sub_lt_norm_sub_conj_of_im_pos
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖z - w‖ < ‖z - conj w‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
    Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply]
  nlinarith

/-- Product formula for the pointwise upper-root Blaschke quotient. -/
theorem upperRootBlaschkeValue_eq_prod (p : ℂ[X]) (z : ℂ) :
    upperRootBlaschkeValue p z =
      ((p.roots.filter fun w => 0 < w.im).map fun w =>
        (z - w) / (z - conj w)).prod := by
  rw [upperRootBlaschkeValue]
  rw [show (upperRootFactor p).eval z =
      ((p.roots.filter fun w => 0 < w.im).map fun w => z - w).prod by
    simp only [upperRootFactor, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]]
  rw [show (conjugatePolynomial (upperRootFactor p)).eval z =
      ((p.roots.filter fun w => 0 < w.im).map fun w => z - conj w).prod by
    simp only [conjugatePolynomial, upperRootFactor,
      Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_apply, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]]
  exact Multiset.prod_map_div.symm

/-- The upper-root Blaschke quotient maps the open upper half-plane into the
closed unit disk. -/
theorem norm_upperRootBlaschkeValue_le_one
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    ‖upperRootBlaschkeValue p z‖ ≤ 1 := by
  rw [upperRootBlaschkeValue_eq_prod]
  have hall : ∀ w ∈ p.roots.filter (fun w => 0 < w.im), 0 < w.im := by
    intro w hw
    exact (Multiset.mem_filter.mp hw).2
  generalize p.roots.filter (fun w => 0 < w.im) = s at hall ⊢
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
      have hw : 0 < w.im := hall w (by simp)
      have hs : ∀ v ∈ s, 0 < v.im := by
        intro v hv
        exact hall v (by simp [hv])
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      apply mul_le_one₀
      · rw [norm_div]
        apply (div_le_one (lt_of_le_of_lt (norm_nonneg _)
          (norm_sub_lt_norm_sub_conj_of_im_pos hz hw))).mpr
        exact (norm_sub_lt_norm_sub_conj_of_im_pos hz hw).le
      · exact norm_nonneg _
      · exact ih hs

/-- The pointwise upper-root Blaschke quotient is complex differentiable on
the open upper half-plane. -/
theorem upperRootBlaschkeValue_differentiableOn (p : ℂ[X]) :
    DifferentiableOn ℂ (upperRootBlaschkeValue p)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((upperRootFactor p).differentiableAt.div
    (conjugatePolynomial (upperRootFactor p)).differentiableAt
    (upperRootBlaschke_denominator_ne_zero p hz)).differentiableWithinAt

/-- The lower root factor has no zero in the open upper half-plane. -/
theorem lowerRootFactor_eval_ne_zero_of_im_pos
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    (lowerRootFactor p).eval z ≠ 0 := by
  intro hzero
  have hzmem : z ∈ (lowerRootFactor p).roots :=
    (mem_roots (lowerRootFactor_ne_zero p)).mpr hzero
  rw [lowerRootFactor_roots, Multiset.mem_filter] at hzmem
  linarith

/-- Pointwise representative of the residual rational inner factor. -/
def lowerRootInnerValue (p : ℂ[X]) (z : ℂ) : ℂ :=
  (conjugatePolynomial (lowerRootFactor p)).eval z /
    (lowerRootFactor p).eval z

theorem lowerRootInner_denominator_ne_zero
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    (lowerRootFactor p).eval z ≠ 0 :=
  lowerRootFactor_eval_ne_zero_of_im_pos p hz

/-- The residual inner quotient is unimodular on the real axis. -/
@[simp] theorem norm_lowerRootInnerValue_real (p : ℂ[X]) (x : ℝ) :
    ‖lowerRootInnerValue p (x : ℂ)‖ = 1 := by
  rw [lowerRootInnerValue, conjugatePolynomial_eval_real, norm_div,
    Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr ?_)]
  intro hzero
  have hxmem : (x : ℂ) ∈ (lowerRootFactor p).roots :=
    (mem_roots (lowerRootFactor_ne_zero p)).mpr hzero
  rw [lowerRootFactor_roots, Multiset.mem_filter] at hxmem
  simpa using hxmem.2

/-- Product formula for the residual lower-root inner quotient. -/
theorem lowerRootInnerValue_eq_prod (p : ℂ[X]) (z : ℂ) :
    lowerRootInnerValue p z =
      ((p.roots.filter fun w => w.im < 0).map fun w =>
        (z - conj w) / (z - w)).prod := by
  rw [lowerRootInnerValue]
  rw [show (conjugatePolynomial (lowerRootFactor p)).eval z =
      ((p.roots.filter fun w => w.im < 0).map fun w => z - conj w).prod by
    simp only [conjugatePolynomial, lowerRootFactor,
      Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_apply, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]]
  rw [show (lowerRootFactor p).eval z =
      ((p.roots.filter fun w => w.im < 0).map fun w => z - w).prod by
    simp only [lowerRootFactor, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]]
  exact Multiset.prod_map_div.symm

/-- The residual inner quotient also maps the upper half-plane into the
closed unit disk. -/
theorem norm_lowerRootInnerValue_le_one
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    ‖lowerRootInnerValue p z‖ ≤ 1 := by
  rw [lowerRootInnerValue_eq_prod]
  have hall : ∀ w ∈ p.roots.filter (fun w => w.im < 0), w.im < 0 := by
    intro w hw
    exact (Multiset.mem_filter.mp hw).2
  generalize p.roots.filter (fun w => w.im < 0) = s at hall ⊢
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons w s ih =>
      have hw : w.im < 0 := hall w (by simp)
      have hs : ∀ v ∈ s, v.im < 0 := by
        intro v hv
        exact hall v (by simp [hv])
      have hconj : 0 < (conj w).im := by
        rw [Complex.conj_im]
        linarith
      have hdist : ‖z - conj w‖ < ‖z - w‖ := by
        simpa using norm_sub_lt_norm_sub_conj_of_im_pos hz hconj
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      apply mul_le_one₀
      · rw [norm_div]
        apply (div_le_one (lt_of_le_of_lt (norm_nonneg _) hdist)).mpr
        exact hdist.le
      · exact norm_nonneg _
      · exact ih hs

/-- The residual lower-root inner quotient is complex differentiable on the
open upper half-plane. -/
theorem lowerRootInnerValue_differentiableOn (p : ℂ[X]) :
    DifferentiableOn ℂ (lowerRootInnerValue p)
      {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((conjugatePolynomial (lowerRootFactor p)).differentiableAt.div
    (lowerRootFactor p).differentiableAt
    (lowerRootInner_denominator_ne_zero p hz)).differentiableWithinAt

/-- The degrees of the direct factors add up to the original degree. -/
theorem finiteKreinLanger_factor_degrees
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    (upperRootFactor (finiteEPolynomial A tau)).natDegree +
        (conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))).natDegree =
      A.natDegree := by
  simpa using finiteEPolynomial_upper_add_lower hA htau

/-- Once the upper-root count is identified as `kappa`, the two rational
inner degrees are exactly `kappa` and `deg A - kappa`.  Thus the analytic
root-count theorem is isolated as the sole input to the dimension count. -/
theorem finiteKreinLanger_factor_degrees_of_upper_count
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    {kappa : ℕ}
    (hcount : upperHalfPlaneRootCount (finiteEPolynomial A tau) = kappa) :
    (upperRootFactor (finiteEPolynomial A tau)).natDegree = kappa ∧
      (conjugatePolynomial
        (lowerRootFactor (finiteEPolynomial A tau))).natDegree =
          A.natDegree - kappa := by
  constructor
  · simpa using hcount
  · rw [conjugatePolynomial_natDegree, lowerRootFactor_natDegree]
    have hsum := finiteEPolynomial_upper_add_lower hA htau
    rw [hcount] at hsum
    exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsum)

end

end RiemannGaussian
