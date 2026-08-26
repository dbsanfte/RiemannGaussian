import RiemannGaussian.FiniteEAux

/-!
# Root factors for the finite `A + i tau A'` model

This file turns the half-plane root multisets from `FiniteEAux` into literal
monic polynomials.  It proves an exact upper/lower factorization for every
complex polynomial with no real roots and all of its roots present, then
specializes it to the finite `E_tau` homotopy.  It also defines the associated
finite Blaschke quotient and proves its unit boundary norm directly.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The monic polynomial whose roots are the upper-half-plane roots of `p`,
with multiplicity. -/
def upperRootFactor (p : ℂ[X]) : ℂ[X] :=
  ((p.roots.filter fun z => 0 < z.im).map fun z => X - C z).prod

/-- The monic polynomial whose roots are the lower-half-plane roots of `p`,
with multiplicity. -/
def lowerRootFactor (p : ℂ[X]) : ℂ[X] :=
  ((p.roots.filter fun z => z.im < 0).map fun z => X - C z).prod

theorem upperRootFactor_monic (p : ℂ[X]) :
    (upperRootFactor p).Monic :=
  monic_multisetProd_X_sub_C _

theorem lowerRootFactor_monic (p : ℂ[X]) :
    (lowerRootFactor p).Monic :=
  monic_multisetProd_X_sub_C _

theorem upperRootFactor_ne_zero (p : ℂ[X]) :
    upperRootFactor p ≠ 0 :=
  (upperRootFactor_monic p).ne_zero

theorem lowerRootFactor_ne_zero (p : ℂ[X]) :
    lowerRootFactor p ≠ 0 :=
  (lowerRootFactor_monic p).ne_zero

@[simp] theorem upperRootFactor_roots (p : ℂ[X]) :
    (upperRootFactor p).roots =
      p.roots.filter fun z => 0 < z.im := by
  simp [upperRootFactor]

@[simp] theorem lowerRootFactor_roots (p : ℂ[X]) :
    (lowerRootFactor p).roots =
      p.roots.filter fun z => z.im < 0 := by
  simp [lowerRootFactor]

@[simp] theorem upperRootFactor_natDegree (p : ℂ[X]) :
    (upperRootFactor p).natDegree = upperHalfPlaneRootCount p := by
  simp [upperRootFactor, upperHalfPlaneRootCount]

@[simp] theorem lowerRootFactor_natDegree (p : ℂ[X]) :
    (lowerRootFactor p).natDegree = lowerHalfPlaneRootCount p := by
  simp [lowerRootFactor, lowerHalfPlaneRootCount]

/-- A root of a polynomial with no real zero cannot lie on the real axis. -/
theorem root_im_ne_zero_of_no_real_zero
    {p : ℂ[X]} (hp : p ≠ 0)
    (hreal : ∀ x : ℝ, p.eval (x : ℂ) ≠ 0)
    {z : ℂ} (hz : z ∈ p.roots) : z.im ≠ 0 := by
  intro him
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hzroot : p.eval z = 0 := (mem_roots hp).mp hz
  apply hreal z.re
  rw [← hzreal]
  exact hzroot

/-- If no root is real, the upper and lower filtered root multisets form an
exact partition, retaining multiplicity. -/
theorem upperRoots_add_lowerRoots
    {p : ℂ[X]} (him : ∀ z ∈ p.roots, z.im ≠ 0) :
    p.roots.filter (fun z => 0 < z.im) +
        p.roots.filter (fun z => z.im < 0) =
      p.roots := by
  have hfilter :
      p.roots.filter (fun z => ¬ 0 < z.im) =
        p.roots.filter (fun z => z.im < 0) := by
    apply Multiset.filter_congr
    intro z hz
    constructor
    · intro hnpos
      exact lt_of_le_of_ne (le_of_not_gt hnpos) (him z hz)
    · intro hneg
      exact not_lt_of_ge hneg.le
  rw [← hfilter, Multiset.filter_add_not]

/-- Exact factorization into the leading coefficient and the two open
half-plane root factors. -/
theorem eq_C_leadingCoeff_mul_upperRootFactor_mul_lowerRootFactor
    {p : ℂ[X]} (hroots : p.roots.card = p.natDegree)
    (him : ∀ z ∈ p.roots, z.im ≠ 0) :
    p = C p.leadingCoeff * upperRootFactor p * lowerRootFactor p := by
  have hpartition := upperRoots_add_lowerRoots him
  calc
    p = C p.leadingCoeff *
        (p.roots.map fun z => X - C z).prod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C hroots).symm
    _ = C p.leadingCoeff *
        (upperRootFactor p * lowerRootFactor p) := by
      rw [← hpartition, Multiset.map_add, Multiset.prod_add]
      rfl
    _ = C p.leadingCoeff * upperRootFactor p * lowerRootFactor p :=
      (mul_assoc _ _ _).symm

/-- The finite homotopy has the exact upper/lower root factorization for
every nonzero real parameter. -/
theorem finiteEPolynomial_eq_rootFactors
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0) :
    finiteEPolynomial A tau =
      C (finiteEPolynomial A tau).leadingCoeff *
        upperRootFactor (finiteEPolynomial A tau) *
        lowerRootFactor (finiteEPolynomial A tau) := by
  apply eq_C_leadingCoeff_mul_upperRootFactor_mul_lowerRootFactor
  · exact IsAlgClosed.card_roots_eq_natDegree
  · exact fun z hz => root_im_ne_zero_of_no_real_zero
      (finiteEPolynomial_ne_zero hA.ne_zero tau)
      (finiteEPolynomial_no_real_zero hA htau) hz

/-- Coefficientwise conjugation of a complex polynomial. -/
def conjugatePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.map (starRingEnd ℂ)

theorem conjugatePolynomial_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    conjugatePolynomial p ≠ 0 :=
  (Polynomial.map_ne_zero_iff (starRingEnd ℂ).injective).mpr hp

@[simp] theorem conjugatePolynomial_natDegree (p : ℂ[X]) :
    (conjugatePolynomial p).natDegree = p.natDegree := by
  exact natDegree_map_eq_of_injective (starRingEnd ℂ).injective p

@[simp] theorem conjugatePolynomial_roots (p : ℂ[X]) :
    (conjugatePolynomial p).roots = p.roots.map conj := by
  exact (IsAlgClosed.splits p).roots_map_of_injective
    (starRingEnd ℂ).injective

/-- Evaluation at an arbitrary point conjugates both the coefficients and
the argument. -/
@[simp] theorem conjugatePolynomial_eval (p : ℂ[X]) (z : ℂ) :
    (conjugatePolynomial p).eval z = conj (p.eval (conj z)) := by
  simpa [conjugatePolynomial] using
    (Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ)
      (x := conj z))

/-- On the real axis, a coefficientwise-conjugated polynomial evaluates to
the conjugate value. -/
@[simp] theorem conjugatePolynomial_eval_real (p : ℂ[X]) (x : ℝ) :
    (conjugatePolynomial p).eval (x : ℂ) =
      conj (p.eval (x : ℂ)) := by
  simpa [conjugatePolynomial] using
    (Polynomial.eval_map_apply (p := p) (f := starRingEnd ℂ) (x := (x : ℂ)))

/-- No real point is a zero of the upper root factor. -/
theorem upperRootFactor_eval_real_ne_zero (p : ℂ[X]) (x : ℝ) :
    (upperRootFactor p).eval (x : ℂ) ≠ 0 := by
  intro hzero
  have hxmem : (x : ℂ) ∈ (upperRootFactor p).roots :=
    (mem_roots (upperRootFactor_ne_zero p)).mpr hzero
  rw [upperRootFactor_roots, Multiset.mem_filter] at hxmem
  simpa using hxmem.2

/-- The quotient of an upper root factor by its reflected polynomial has
unit norm at every real point. -/
theorem norm_upperRootFactor_div_conjugate_real
    (p : ℂ[X]) (x : ℝ) :
    ‖(upperRootFactor p).eval (x : ℂ) /
        (conjugatePolynomial (upperRootFactor p)).eval (x : ℂ)‖ = 1 := by
  rw [conjugatePolynomial_eval_real, norm_div, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr (upperRootFactor_eval_real_ne_zero p x))]

/-- The reflected upper-root factor has no zero in the open upper
half-plane. -/
theorem conjugate_upperRootFactor_eval_ne_zero_of_im_pos
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    (conjugatePolynomial (upperRootFactor p)).eval z ≠ 0 := by
  intro hzero
  have hzmem : z ∈ (conjugatePolynomial (upperRootFactor p)).roots :=
    (mem_roots (conjugatePolynomial_ne_zero
      (upperRootFactor_ne_zero p))).mpr hzero
  rw [conjugatePolynomial_roots, Multiset.mem_map] at hzmem
  obtain ⟨w, hw, rfl⟩ := hzmem
  rw [upperRootFactor_roots, Multiset.mem_filter] at hw
  rw [Complex.conj_im] at hz
  linarith

/-- The literal finite Blaschke quotient built from the upper roots of `p`. -/
def upperRootBlaschkeValue (p : ℂ[X]) (z : ℂ) : ℂ :=
  (upperRootFactor p).eval z /
    (conjugatePolynomial (upperRootFactor p)).eval z

theorem upperRootBlaschke_denominator_ne_zero
    (p : ℂ[X]) {z : ℂ} (hz : 0 < z.im) :
    (conjugatePolynomial (upperRootFactor p)).eval z ≠ 0 :=
  conjugate_upperRootFactor_eval_ne_zero_of_im_pos p hz

/-- The finite Blaschke quotient is unimodular on the real axis. -/
@[simp] theorem norm_upperRootBlaschkeValue_real
    (p : ℂ[X]) (x : ℝ) :
    ‖upperRootBlaschkeValue p (x : ℂ)‖ = 1 := by
  exact norm_upperRootFactor_div_conjugate_real p x

@[simp] theorem upperRootBlaschke_numerator_natDegree (p : ℂ[X]) :
    (upperRootFactor p).natDegree = upperHalfPlaneRootCount p :=
  upperRootFactor_natDegree p

@[simp] theorem upperRootBlaschke_denominator_natDegree (p : ℂ[X]) :
    (conjugatePolynomial (upperRootFactor p)).natDegree =
      upperHalfPlaneRootCount p := by
  simp

end

end RiemannGaussian
