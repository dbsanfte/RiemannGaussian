import RiemannGaussian.SymmetricQuartetFiniteRoots

/-!
# Canonical root decomposition for real polynomials

The finite Hardy estimates consume an exact multiset decomposition of a real
base polynomial into real-axis roots and conjugate pairs represented by their
upper-half-plane member.  This file constructs those multisets canonically
from the complete complex root multiset.

Conjugation symmetry is proved coefficientwise and then transported through
`Polynomial.roots`, so every statement retains algebraic multiplicity.  The
resulting decomposition is unconditional; separability is needed only for the
additional no-repetition conclusion.
-/

open Polynomial
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-aware submultiset of real-axis roots of a real
polynomial after mapping its coefficients to `ℂ`. -/
def realPolynomialRealRootMultiset (A : ℝ[X]) : Multiset ℂ :=
  (A.map Complex.ofRealHom).roots.filter fun z => z.im = 0

/-- The multiplicity-aware submultiset of open upper-half-plane roots of a
real polynomial after mapping its coefficients to `ℂ`. -/
def realPolynomialUpperRootMultiset (A : ℝ[X]) : Multiset ℂ :=
  (A.map Complex.ofRealHom).roots.filter fun z => 0 < z.im

/-- Coefficientwise conjugation fixes a polynomial obtained from real
coefficients. -/
@[simp] theorem conjugatePolynomial_real_map (A : ℝ[X]) :
    conjugatePolynomial (A.map Complex.ofRealHom) =
      A.map Complex.ofRealHom := by
  ext n
  simp [conjugatePolynomial]

/-- The complete complex root multiset of a real polynomial is invariant
under conjugation, including every root occurrence. -/
theorem realPolynomial_roots_map_conj (A : ℝ[X]) :
    (A.map Complex.ofRealHom).roots.map (starRingEnd ℂ) =
      (A.map Complex.ofRealHom).roots := by
  have h := congrArg Polynomial.roots (conjugatePolynomial_real_map A)
  simpa only [conjugatePolynomial_roots] using h

/-- Conjugation maps the upper root submultiset exactly onto the lower root
submultiset, preserving multiplicity. -/
theorem realPolynomial_upperRoots_map_conj_eq_lowerRoots (A : ℝ[X]) :
    ((A.map Complex.ofRealHom).roots.filter fun z => 0 < z.im).map
        (starRingEnd ℂ) =
      (A.map Complex.ofRealHom).roots.filter fun z => z.im < 0 := by
  have hfiltered := congrArg
    (Multiset.filter fun z : ℂ => z.im < 0)
    (realPolynomial_roots_map_conj A)
  rw [Multiset.filter_map] at hfiltered
  simpa only [Function.comp_apply, Complex.conj_im, neg_lt_zero] using hfiltered

/-- Every complex multiset partitions exactly into its real-axis, upper, and
lower submultisets. -/
theorem complexMultiset_real_upper_lower_partition (s : Multiset ℂ) :
    s.filter (fun z => z.im = 0) +
        s.filter (fun z => 0 < z.im) +
        s.filter (fun z => z.im < 0) = s := by
  ext z
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hnpos : ¬0 < z.im := not_lt_of_ge hneg.le
    simp [hneg, hneg.ne, hnpos]
  · simp [hzero]
  · have hnneg : ¬z.im < 0 := not_lt_of_ge hpos.le
    simp [hpos, hpos.ne', hnneg]

/-- Canonical exact decomposition of the complete complex root multiset of a
real polynomial into real roots and conjugate pairs represented by their
upper member. -/
theorem realPolynomial_roots_eq_real_add_conjugatePairs (A : ℝ[X]) :
    (A.map Complex.ofRealHom).roots =
      realPolynomialRealRootMultiset A +
        conjugatePairRootMultiset (realPolynomialUpperRootMultiset A) := by
  symm
  calc
    realPolynomialRealRootMultiset A +
          conjugatePairRootMultiset (realPolynomialUpperRootMultiset A) =
        (A.map Complex.ofRealHom).roots.filter (fun z => z.im = 0) +
          (A.map Complex.ofRealHom).roots.filter (fun z => 0 < z.im) +
          ((A.map Complex.ofRealHom).roots.filter fun z => 0 < z.im).map
            (starRingEnd ℂ) := by
      simp [realPolynomialRealRootMultiset,
        realPolynomialUpperRootMultiset, conjugatePairRootMultiset,
        add_assoc]
    _ = (A.map Complex.ofRealHom).roots.filter (fun z => z.im = 0) +
          (A.map Complex.ofRealHom).roots.filter (fun z => 0 < z.im) +
          (A.map Complex.ofRealHom).roots.filter (fun z => z.im < 0) := by
      rw [realPolynomial_upperRoots_map_conj_eq_lowerRoots]
    _ = (A.map Complex.ofRealHom).roots :=
      complexMultiset_real_upper_lower_partition _

/-- Every member of the canonical real-root multiset lies on the real
axis. -/
theorem realPolynomialRealRootMultiset_im_eq_zero (A : ℝ[X]) :
    ∀ z ∈ realPolynomialRealRootMultiset A, z.im = 0 := by
  intro z hz
  exact (Multiset.mem_filter.mp hz).2

/-- Every member of the canonical upper-root multiset lies in the open upper
half-plane. -/
theorem realPolynomialUpperRootMultiset_im_pos (A : ℝ[X]) :
    ∀ z ∈ realPolynomialUpperRootMultiset A, 0 < z.im := by
  intro z hz
  exact (Multiset.mem_filter.mp hz).2

/-- The canonical upper-root multiset has no repetitions when the base
polynomial is separable. -/
theorem realPolynomialUpperRootMultiset_nodup
    {A : ℝ[X]} (hA : A.Separable) :
    (realPolynomialUpperRootMultiset A).Nodup := by
  exact (Polynomial.nodup_roots hA.map).filter _

/-- Exact multiplicity count for the canonical decomposition: real roots
plus twice the upper roots account for the full degree. -/
theorem realPolynomial_realRoot_card_add_two_mul_upperRoot_card
    (A : ℝ[X]) :
    (realPolynomialRealRootMultiset A).card +
        2 * (realPolynomialUpperRootMultiset A).card = A.natDegree := by
  have hcard := congrArg Multiset.card
    (realPolynomial_roots_eq_real_add_conjugatePairs A)
  rw [IsAlgClosed.card_roots_eq_natDegree,
    Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
    at hcard
  simp only [Multiset.card_add, Multiset.card_map,
    conjugatePairRootMultiset] at hcard
  omega

end

end RiemannGaussian
