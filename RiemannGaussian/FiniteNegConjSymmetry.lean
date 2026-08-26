import RiemannGaussian.FiniteKreinLanger

/-!
# Negative-conjugation symmetry of the finite residual inner factor

This file isolates the reflection `z ↦ -conj z`.  It proves that invariance
of a polynomial's root multiset under this reflection forces the same
conjugation law for its lower-root residual inner quotient.  For the finite
homotopy polynomial `A + I eta A'`, the required multiset invariance follows
algebraically when the real base polynomial is even.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Reflection in the imaginary axis. -/
def negConj (z : ℂ) : ℂ := -starRingEnd ℂ z

@[simp] theorem negConj_im (z : ℂ) : (negConj z).im = z.im := by
  simp [negConj]

@[simp] theorem negConj_involutive (z : ℂ) : negConj (negConj z) = z := by
  simp [negConj]

/-- Negative conjugation preserves the lower-root submultiset whenever it
preserves the full root multiset. -/
theorem lowerRoots_map_negConj_eq
    {p : ℂ[X]}
    (hroots : p.roots.map negConj = p.roots) :
    (p.roots.filter fun w => w.im < 0).map negConj =
      p.roots.filter fun w => w.im < 0 := by
  have hfiltered :=
    congrArg (Multiset.filter fun w : ℂ => w.im < 0) hroots
  rw [Multiset.filter_map] at hfiltered
  simpa only [Function.comp_apply, negConj_im] using hfiltered

/-- Each elementary lower-root inner factor obeys negative-conjugation
symmetry when both its root and evaluation point are reflected. -/
theorem lowerRootInnerElementaryFactor_negConj (w z : ℂ) :
    (negConj z - starRingEnd ℂ (negConj w)) /
        (negConj z - negConj w) =
      starRingEnd ℂ
        ((z - starRingEnd ℂ w) / (z - w)) := by
  simp only [negConj, map_neg, map_div₀, map_sub, starRingEnd_apply,
    star_star]
  rw [show -star z - -w = -(star z - w) by ring,
    show -star z - -star w = -(star z - star w) by ring,
    neg_div_neg_eq]

/-- Root-multiset symmetry gives the exact reflected-value identity for the
residual lower-root inner function, including multiplicities. -/
theorem lowerRootInnerValue_negConj_eq_conj
    {p : ℂ[X]}
    (hroots : p.roots.map negConj = p.roots) (z : ℂ) :
    lowerRootInnerValue p (negConj z) =
      starRingEnd ℂ (lowerRootInnerValue p z) := by
  rw [lowerRootInnerValue_eq_prod, lowerRootInnerValue_eq_prod]
  let s := p.roots.filter fun w => w.im < 0
  change
    (s.map fun w =>
      (negConj z - starRingEnd ℂ w) / (negConj z - w)).prod =
        starRingEnd ℂ
          (s.map fun w => (z - starRingEnd ℂ w) / (z - w)).prod
  have hs : s.map negConj = s := lowerRoots_map_negConj_eq hroots
  conv_lhs => rw [← hs]
  rw [Multiset.map_map]
  simp only [Function.comp_apply, lowerRootInnerElementaryFactor_negConj]
  simpa only [Multiset.map_map, Function.comp_apply] using
    (map_multiset_prod (starRingEnd ℂ)
      (s.map fun w => (z - starRingEnd ℂ w) / (z - w))).symm

/-- The derivative of an even polynomial is odd, stated as an exact
polynomial composition identity. -/
theorem derivative_comp_neg_X_eq_neg
    {A : ℝ[X]} (hEven : A.comp (-X) = A) :
    A.derivative.comp (-X) = -A.derivative := by
  have hderiv := congrArg derivative hEven
  rw [derivative_comp] at hderiv
  simp only [derivative_neg, derivative_X, neg_mul, one_mul] at hderiv
  calc
    A.derivative.comp (-X) = -(-A.derivative.comp (-X)) := by simp
    _ = -A.derivative := congrArg (fun q : ℝ[X] => -q) hderiv

/-- Evaluation of an even real polynomial at the negative conjugate is the
conjugate of its value. -/
theorem realPolynomial_eval₂_negConj_eq_conj_of_even
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (z : ℂ) :
    A.eval₂ Complex.ofRealHom (negConj z) =
      starRingEnd ℂ (A.eval₂ Complex.ofRealHom z) := by
  calc
    A.eval₂ Complex.ofRealHom (negConj z) =
        (A.comp (-X)).eval₂ Complex.ofRealHom (starRingEnd ℂ z) := by
      rw [eval₂_comp]
      simp [negConj]
    _ = A.eval₂ Complex.ofRealHom (starRingEnd ℂ z) := by rw [hEven]
    _ = starRingEnd ℂ (A.eval₂ Complex.ofRealHom z) := by
      change aeval (starRingEnd ℂ z) A =
        starRingEnd ℂ (aeval z A)
      rw [Polynomial.aeval_conj]

/-- Evaluation of the derivative of an even real polynomial is
anti-equivariant under negative conjugation. -/
theorem realPolynomial_derivative_eval₂_negConj_eq_neg_conj_of_even
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (z : ℂ) :
    A.derivative.eval₂ Complex.ofRealHom (negConj z) =
      -starRingEnd ℂ
        (A.derivative.eval₂ Complex.ofRealHom z) := by
  calc
    A.derivative.eval₂ Complex.ofRealHom (negConj z) =
        (A.derivative.comp (-X)).eval₂ Complex.ofRealHom
          (starRingEnd ℂ z) := by
      rw [eval₂_comp]
      simp [negConj]
    _ = (-A.derivative).eval₂ Complex.ofRealHom
        (starRingEnd ℂ z) := by rw [derivative_comp_neg_X_eq_neg hEven]
    _ = -A.derivative.eval₂ Complex.ofRealHom
        (starRingEnd ℂ z) := by simp
    _ = -starRingEnd ℂ
        (A.derivative.eval₂ Complex.ofRealHom z) := by
      change -aeval (starRingEnd ℂ z) A.derivative =
        -starRingEnd ℂ (aeval z A.derivative)
      rw [Polynomial.aeval_conj]

/-- For an even real base polynomial, composing `A + I eta A'` with
negation gives its coefficientwise-conjugate sharp polynomial. -/
theorem finiteEPolynomial_comp_neg_X_eq_sharp
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (η : ℝ) :
    (finiteEPolynomial A η).comp (-X) =
      finiteESharpPolynomial A η := by
  have hAmap :
      (A.map Complex.ofRealHom).comp (-X) = A.map Complex.ofRealHom := by
    calc
      (A.map Complex.ofRealHom).comp (-X) =
          (A.comp (-X)).map Complex.ofRealHom := by
        symm
        simpa using Polynomial.map_comp Complex.ofRealHom A (-X)
      _ = A.map Complex.ofRealHom := by rw [hEven]
  have hderivMap :
      (A.derivative.map Complex.ofRealHom).comp (-X) =
        -A.derivative.map Complex.ofRealHom := by
    calc
      (A.derivative.map Complex.ofRealHom).comp (-X) =
          (A.derivative.comp (-X)).map Complex.ofRealHom := by
        symm
        simpa using
          Polynomial.map_comp Complex.ofRealHom A.derivative (-X)
      _ = (-A.derivative).map Complex.ofRealHom := by
        rw [derivative_comp_neg_X_eq_neg hEven]
      _ = -A.derivative.map Complex.ofRealHom := by simp
  rw [finiteEPolynomial, finiteESharpPolynomial, add_comp, smul_comp,
    hAmap, hderivMap]
  simp
  rw [sub_eq_add_neg]

/-- The roots of `A + I eta A'` are invariant with multiplicity under
negative conjugation when `A` is even. -/
theorem finiteEPolynomial_roots_map_negConj_eq
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (η : ℝ) :
    (finiteEPolynomial A η).roots.map negConj =
      (finiteEPolynomial A η).roots := by
  have hcompRoots := congrArg Polynomial.roots
    (finiteEPolynomial_comp_neg_X_eq_sharp hEven η)
  rw [roots_comp_neg_X, finiteESharpPolynomial_roots] at hcompRoots
  have hmap := congrArg (Multiset.map fun z : ℂ => -z) hcompRoots
  simp only [Multiset.map_map, Function.comp_apply, neg_neg] at hmap
  rw [Multiset.map_id'] at hmap
  change (finiteEPolynomial A η).roots =
    (finiteEPolynomial A η).roots.map negConj at hmap
  exact hmap.symm

/-- Evenness of `A` discharges the residual-inner reflected-value identity
for its finite homotopy polynomial. -/
theorem finiteE_lowerRootInnerValue_negConj_eq_conj
    {A : ℝ[X]} (hEven : A.comp (-X) = A) (η : ℝ) (z : ℂ) :
    lowerRootInnerValue (finiteEPolynomial A η) (negConj z) =
      starRingEnd ℂ (lowerRootInnerValue (finiteEPolynomial A η) z) :=
  lowerRootInnerValue_negConj_eq_conj
    (finiteEPolynomial_roots_map_negConj_eq hEven η) z

end

end RiemannGaussian
