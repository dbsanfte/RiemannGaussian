import RiemannGaussian.FiniteOnePair
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic foundations for the finite `A + i tau A'` homotopy

This file starts the general finite-polynomial realization.  It defines the
complex polynomial

`E_tau = A + i tau A'`

for a real polynomial `A`, and proves the exact no-real-axis-crossing lemma
for every nonzero real `tau` when `A` is separable.  Over `ℝ`, separability is
the squarefree-root hypothesis needed by the analytic argument.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The complex polynomial `A + i tau A'` attached to a real polynomial. -/
def finiteEPolynomial (A : ℝ[X]) (tau : ℝ) : ℂ[X] :=
  A.map Complex.ofRealHom +
    (Complex.I * (tau : ℂ)) • A.derivative.map Complex.ofRealHom

/-- The reflected polynomial `A - i tau A'`. -/
def finiteESharpPolynomial (A : ℝ[X]) (tau : ℝ) : ℂ[X] :=
  A.map Complex.ofRealHom -
    (Complex.I * (tau : ℂ)) • A.derivative.map Complex.ofRealHom

@[simp] theorem finiteEPolynomial_eval_real (A : ℝ[X]) (tau x : ℝ) :
    (finiteEPolynomial A tau).eval (x : ℂ) =
      Complex.ofReal (A.eval x) +
        Complex.I * (tau : ℂ) *
          Complex.ofReal (A.derivative.eval x) := by
  rw [finiteEPolynomial, eval_add, eval_smul,
    Polynomial.eval_map, Polynomial.eval_map]
  change A.eval₂ Complex.ofRealHom (Complex.ofRealHom x) +
      (Complex.I * (tau : ℂ)) •
        A.derivative.eval₂ Complex.ofRealHom (Complex.ofRealHom x) = _
  rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
  simp only [Complex.ofRealHom_eq_coe, smul_eq_mul]

@[simp] theorem finiteESharpPolynomial_eval_real
    (A : ℝ[X]) (tau x : ℝ) :
    (finiteESharpPolynomial A tau).eval (x : ℂ) =
      Complex.ofReal (A.eval x) -
        Complex.I * (tau : ℂ) *
          Complex.ofReal (A.derivative.eval x) := by
  rw [finiteESharpPolynomial, eval_sub, eval_smul,
    Polynomial.eval_map, Polynomial.eval_map]
  change A.eval₂ Complex.ofRealHom (Complex.ofRealHom x) -
      (Complex.I * (tau : ℂ)) •
        A.derivative.eval₂ Complex.ofRealHom (Complex.ofRealHom x) = _
  rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
  simp only [Complex.ofRealHom_eq_coe, smul_eq_mul]

@[simp] theorem finiteEPolynomial_eval (A : ℝ[X]) (tau : ℝ) (z : ℂ) :
    (finiteEPolynomial A tau).eval z =
      A.eval₂ Complex.ofRealHom z +
        Complex.I * (tau : ℂ) *
          A.derivative.eval₂ Complex.ofRealHom z := by
  simp [finiteEPolynomial, Polynomial.eval_map, smul_eq_mul,
    mul_assoc]

@[simp] theorem finiteESharpPolynomial_eval
    (A : ℝ[X]) (tau : ℝ) (z : ℂ) :
    (finiteESharpPolynomial A tau).eval z =
      A.eval₂ Complex.ofRealHom z -
        Complex.I * (tau : ℂ) *
          A.derivative.eval₂ Complex.ofRealHom z := by
  simp [finiteESharpPolynomial, Polynomial.eval_map, smul_eq_mul,
    mul_assoc]

/-- A separable polynomial and its derivative cannot vanish at the same real
point. -/
theorem separable_eval_derivative_ne_zero_real
    {A : ℝ[X]} (hA : A.Separable) {x : ℝ} (hx : A.eval x = 0) :
    A.derivative.eval x ≠ 0 := by
  apply hA.eval₂_derivative_ne_zero (RingHom.id ℝ)
  simpa using hx

/-- No member of the nonzero-parameter homotopy `A + i tau A'` has a real
zero.  This is the exact algebraic barrier preventing root crossings through
the real axis. -/
theorem finiteEPolynomial_no_real_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (x : ℝ) :
    (finiteEPolynomial A tau).eval (x : ℂ) ≠ 0 := by
  intro hzero
  rw [finiteEPolynomial_eval_real] at hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero,
    zero_add, Complex.zero_re, Complex.zero_im] at hre him
  have hroot : A.eval x = 0 := hre
  have hderiv : A.derivative.eval x ≠ 0 :=
    separable_eval_derivative_ne_zero_real hA hroot
  exact hderiv ((mul_eq_zero.mp him).resolve_left htau)

/-- The reflected member `A - i tau A'` also has no real zero. -/
theorem finiteESharpPolynomial_no_real_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (x : ℝ) :
    (finiteESharpPolynomial A tau).eval (x : ℂ) ≠ 0 := by
  intro hzero
  rw [finiteESharpPolynomial_eval_real] at hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero,
    zero_add, zero_sub, Complex.zero_re, Complex.zero_im] at hre him
  have hroot : A.eval x = 0 := hre
  have hderiv : A.derivative.eval x ≠ 0 :=
    separable_eval_derivative_ne_zero_real hA hroot
  apply hderiv
  exact (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left htau

/-- `E_tau` and its reflection have no common complex zero. -/
theorem finiteEPolynomial_not_both_roots
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (z : ℂ) :
    (finiteEPolynomial A tau).eval z ≠ 0 ∨
      (finiteESharpPolynomial A tau).eval z ≠ 0 := by
  by_contra hboth
  push Not at hboth
  rw [finiteEPolynomial_eval] at hboth
  rw [finiteESharpPolynomial_eval] at hboth
  let av : ℂ := A.eval₂ Complex.ofRealHom z
  let dv : ℂ := A.derivative.eval₂ Complex.ofRealHom z
  have hsum : (2 : ℂ) * av = 0 := by
    dsimp only [av, dv]
    linear_combination hboth.1 + hboth.2
  have hav : av = 0 := (mul_eq_zero.mp hsum).resolve_left (by norm_num)
  have hscaled : (Complex.I * (tau : ℂ)) * dv = 0 := by
    have hfirst := hboth.1
    change av + (Complex.I * (tau : ℂ)) * dv = 0 at hfirst
    rw [hav, zero_add] at hfirst
    exact hfirst
  have hcoeff : Complex.I * (tau : ℂ) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr htau)
  have hdv : dv = 0 := (mul_eq_zero.mp hscaled).resolve_left hcoeff
  exact (hA.eval₂_derivative_ne_zero Complex.ofRealHom hav) hdv

/-- The direct finite Krein--Langer numerator and denominator are coprime for
every nonzero homotopy parameter. -/
theorem finiteEPolynomial_isCoprime_sharp
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    IsCoprime (finiteEPolynomial A tau)
      (finiteESharpPolynomial A tau) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    ℂ ℂ (finiteEPolynomial A tau) (finiteESharpPolynomial A tau)).2
  intro z
  simpa [aeval_def] using finiteEPolynomial_not_both_roots hA htau z

theorem finiteE_derivativeTerm_degree_lt
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    ((Complex.I * (tau : ℂ)) •
        A.derivative.map Complex.ofRealHom).degree <
      (A.map Complex.ofRealHom).degree := by
  calc
    ((Complex.I * (tau : ℂ)) •
        A.derivative.map Complex.ofRealHom).degree ≤
        (A.derivative.map Complex.ofRealHom).degree :=
      degree_smul_le _ _
    _ = A.derivative.degree :=
      degree_map_eq_of_injective Complex.ofRealHom.injective _
    _ < A.degree := degree_derivative_lt hA
    _ = (A.map Complex.ofRealHom).degree :=
      (degree_map_eq_of_injective Complex.ofRealHom.injective _).symm

/-- The homotopy has exactly the same degree as `A`; its derivative term is
strictly lower degree. -/
theorem finiteEPolynomial_degree
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEPolynomial A tau).degree = A.degree := by
  rw [finiteEPolynomial,
    degree_add_eq_left_of_degree_lt
      (finiteE_derivativeTerm_degree_lt hA tau),
    degree_map_eq_of_injective Complex.ofRealHom.injective]

theorem finiteESharpPolynomial_degree
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteESharpPolynomial A tau).degree = A.degree := by
  rw [finiteESharpPolynomial,
    degree_sub_eq_left_of_degree_lt
      (finiteE_derivativeTerm_degree_lt hA tau),
    degree_map_eq_of_injective Complex.ofRealHom.injective]

/-- The leading coefficient is independent of `tau`. -/
theorem finiteEPolynomial_leadingCoeff
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEPolynomial A tau).leadingCoeff =
      Complex.ofRealHom A.leadingCoeff := by
  rw [finiteEPolynomial,
    leadingCoeff_add_of_degree_lt'
      (finiteE_derivativeTerm_degree_lt hA tau),
    leadingCoeff_map]

theorem finiteESharpPolynomial_leadingCoeff
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteESharpPolynomial A tau).leadingCoeff =
      Complex.ofRealHom A.leadingCoeff := by
  rw [finiteESharpPolynomial,
    leadingCoeff_sub_of_degree_lt
      (finiteE_derivativeTerm_degree_lt hA tau),
    leadingCoeff_map]

/-- Evaluation of the reflected polynomial is conjugate evaluation of
`E_tau` at the conjugate point. -/
theorem finiteESharpPolynomial_eval_eq_conj
    (A : ℝ[X]) (tau : ℝ) (z : ℂ) :
    (finiteESharpPolynomial A tau).eval z =
      conj ((finiteEPolynomial A tau).eval (conj z)) := by
  rw [finiteESharpPolynomial_eval, finiteEPolynomial_eval]
  change aeval z A - Complex.I * (tau : ℂ) * aeval z A.derivative =
    conj (aeval (conj z) A +
      Complex.I * (tau : ℂ) * aeval (conj z) A.derivative)
  rw [Polynomial.aeval_conj, Polynomial.aeval_conj]
  simp [sub_eq_add_neg]

/-- Coefficientwise complex conjugation sends `E_tau` to its reflection. -/
theorem finiteEPolynomial_map_conj
    (A : ℝ[X]) (tau : ℝ) :
    (finiteEPolynomial A tau).map (starRingEnd ℂ) =
      finiteESharpPolynomial A tau := by
  ext n
  simp [finiteEPolynomial, finiteESharpPolynomial, sub_eq_add_neg]

/-- The homotopy polynomial is nonzero whenever `A` is. -/
theorem finiteEPolynomial_ne_zero
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    finiteEPolynomial A tau ≠ 0 := by
  intro hzero
  have hdegree := finiteEPolynomial_degree hA tau
  rw [hzero, degree_zero] at hdegree
  exact (degree_ne_bot.mpr hA) hdegree.symm

theorem finiteESharpPolynomial_ne_zero
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    finiteESharpPolynomial A tau ≠ 0 := by
  intro hzero
  have hdegree := finiteESharpPolynomial_degree hA tau
  rw [hzero, degree_zero] at hdegree
  exact (degree_ne_bot.mpr hA) hdegree.symm

theorem finiteEPolynomial_natDegree
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteEPolynomial A tau).natDegree = A.natDegree :=
  natDegree_eq_of_degree_eq (finiteEPolynomial_degree hA tau)

theorem finiteESharpPolynomial_natDegree
    {A : ℝ[X]} (hA : A ≠ 0) (tau : ℝ) :
    (finiteESharpPolynomial A tau).natDegree = A.natDegree :=
  natDegree_eq_of_degree_eq (finiteESharpPolynomial_degree hA tau)

/-- Over `ℂ`, the roots of the reflected polynomial are exactly the
conjugates of the roots of `E_tau`, with multiplicity. -/
theorem finiteESharpPolynomial_roots
    (A : ℝ[X]) (tau : ℝ) :
    (finiteESharpPolynomial A tau).roots =
      (finiteEPolynomial A tau).roots.map conj := by
  rw [← finiteEPolynomial_map_conj]
  exact (IsAlgClosed.splits (finiteEPolynomial A tau)).roots_map_of_injective
    (starRingEnd ℂ).injective

/-- Number of roots in the open upper half-plane, counted with
multiplicity. -/
def upperHalfPlaneRootCount (p : ℂ[X]) : ℕ :=
  (p.roots.filter fun z => 0 < z.im).card

/-- Number of roots in the open lower half-plane, counted with
multiplicity. -/
def lowerHalfPlaneRootCount (p : ℂ[X]) : ℕ :=
  (p.roots.filter fun z => z.im < 0).card

/-- Reflection interchanges upper and lower roots, including
multiplicities. -/
theorem upperHalfPlaneRootCount_finiteESharp
    (A : ℝ[X]) (tau : ℝ) :
    upperHalfPlaneRootCount (finiteESharpPolynomial A tau) =
      lowerHalfPlaneRootCount (finiteEPolynomial A tau) := by
  rw [upperHalfPlaneRootCount, lowerHalfPlaneRootCount,
    finiteESharpPolynomial_roots, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_apply, Complex.conj_im, neg_pos]

theorem lowerHalfPlaneRootCount_finiteESharp
    (A : ℝ[X]) (tau : ℝ) :
    lowerHalfPlaneRootCount (finiteESharpPolynomial A tau) =
      upperHalfPlaneRootCount (finiteEPolynomial A tau) := by
  rw [lowerHalfPlaneRootCount, upperHalfPlaneRootCount,
    finiteESharpPolynomial_roots, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_apply, Complex.conj_im, neg_lt_zero]

/-- If a nonzero complex polynomial has no real zero, every root lies in
exactly one open half-plane. -/
theorem upper_add_lower_eq_roots_card_of_no_real_zero
    {p : ℂ[X]} (hp : p ≠ 0)
    (hreal : ∀ x : ℝ, p.eval (x : ℂ) ≠ 0) :
    upperHalfPlaneRootCount p + lowerHalfPlaneRootCount p =
      p.roots.card := by
  have him_ne_zero : ∀ z ∈ p.roots, z.im ≠ 0 := by
    intro z hz him
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hzroot : p.eval z = 0 := (mem_roots hp).mp hz
    apply hreal z.re
    rw [← hzreal]
    exact hzroot
  have hfilter :
      p.roots.filter (fun z => ¬ 0 < z.im) =
        p.roots.filter (fun z => z.im < 0) := by
    apply Multiset.filter_congr
    intro z hz
    constructor
    · intro hnpos
      exact lt_of_le_of_ne (le_of_not_gt hnpos) (him_ne_zero z hz)
    · intro hneg
      exact not_lt_of_ge hneg.le
  rw [upperHalfPlaneRootCount, lowerHalfPlaneRootCount,
    ← Multiset.card_add, ← hfilter, Multiset.filter_add_not]

/-- For nonzero `tau`, the upper and lower roots of `E_tau`, counted with
multiplicity, add up to the degree of `A`. -/
theorem finiteEPolynomial_upper_add_lower
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) +
        lowerHalfPlaneRootCount (finiteEPolynomial A tau) =
      A.natDegree := by
  calc
    _ = (finiteEPolynomial A tau).roots.card :=
      upper_add_lower_eq_roots_card_of_no_real_zero
        (finiteEPolynomial_ne_zero hA.ne_zero tau)
        (finiteEPolynomial_no_real_zero hA htau)
    _ = (finiteEPolynomial A tau).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    _ = A.natDegree := finiteEPolynomial_natDegree hA.ne_zero tau

theorem finiteESharpPolynomial_upper_add_lower
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    upperHalfPlaneRootCount (finiteESharpPolynomial A tau) +
        lowerHalfPlaneRootCount (finiteESharpPolynomial A tau) =
      A.natDegree := by
  calc
    _ = (finiteESharpPolynomial A tau).roots.card :=
      upper_add_lower_eq_roots_card_of_no_real_zero
        (finiteESharpPolynomial_ne_zero hA.ne_zero tau)
        (finiteESharpPolynomial_no_real_zero hA htau)
    _ = (finiteESharpPolynomial A tau).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    _ = A.natDegree := finiteESharpPolynomial_natDegree hA.ne_zero tau

end

end RiemannGaussian
