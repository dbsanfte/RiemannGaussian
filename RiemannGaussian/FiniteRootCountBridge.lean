import RiemannGaussian.FiniteAlgebraicHilbert

/-!
# Root-count bridge for the finite algebraic Hilbert model

This file isolates the one remaining homotopy statement needed to remove the
raw degree hypothesis from the finite Gram--Weil realization.  For a real
polynomial, the upper and lower roots at `tau = 0` are paired by conjugation.
Consequently, invariance of the upper count from `0` to a nonzero parameter
implies the degree inequality required by cross-angle injectivity.

The homotopy-invariance equality itself is not assumed globally or hidden in
a definition here; it remains an explicit hypothesis of the final bridge
theorems.
-/

open Polynomial

namespace RiemannGaussian

noncomputable section

/-- Upper- and lower-half-plane roots, counted with multiplicity, account for
at most all roots.  Real-axis roots are the possible remainder. -/
theorem upper_add_lower_le_roots_card (p : ℂ[X]) :
    upperHalfPlaneRootCount p + lowerHalfPlaneRootCount p ≤
      p.roots.card := by
  rw [upperHalfPlaneRootCount, lowerHalfPlaneRootCount]
  have hfilter :
      p.roots.filter (fun z => z.im < 0) ≤
        p.roots.filter (fun z => ¬ 0 < z.im) :=
    Multiset.monotone_filter_right p.roots fun _ hz =>
      not_lt_of_ge hz.le
  calc
    (p.roots.filter fun z => 0 < z.im).card +
          (p.roots.filter fun z => z.im < 0).card ≤
        (p.roots.filter fun z => 0 < z.im).card +
          (p.roots.filter fun z => ¬ 0 < z.im).card :=
      Nat.add_le_add_left (Multiset.card_le_card hfilter) _
    _ = (p.roots.filter (fun z => 0 < z.im) +
          p.roots.filter (fun z => ¬ 0 < z.im)).card := by simp
    _ = p.roots.card := by rw [Multiset.filter_add_not]

/-- At the zero homotopy parameter, the mapped real polynomial has equally
many upper and lower roots, including multiplicity. -/
theorem finiteEPolynomial_zero_upper_eq_lower (A : ℝ[X]) :
    upperHalfPlaneRootCount (finiteEPolynomial A 0) =
      lowerHalfPlaneRootCount (finiteEPolynomial A 0) := by
  simpa [finiteEPolynomial, finiteESharpPolynomial] using
    upperHalfPlaneRootCount_finiteESharp A 0

/-- Twice the upper count at `tau = 0` is bounded by the degree of the real
polynomial.  Equality occurs exactly when there are no real-axis roots, but
only the inequality is needed downstream. -/
theorem twice_finiteEPolynomial_zero_upper_le_natDegree
    {A : ℝ[X]} (hA : A ≠ 0) :
    2 * upperHalfPlaneRootCount (finiteEPolynomial A 0) ≤
      A.natDegree := by
  have hle := upper_add_lower_le_roots_card
    (finiteEPolynomial A 0)
  rw [← finiteEPolynomial_zero_upper_eq_lower A] at hle
  calc
    2 * upperHalfPlaneRootCount (finiteEPolynomial A 0) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0) +
          upperHalfPlaneRootCount (finiteEPolynomial A 0) := by omega
    _ ≤ (finiteEPolynomial A 0).roots.card := hle
    _ = (finiteEPolynomial A 0).natDegree :=
      IsAlgClosed.card_roots_eq_natDegree
    _ = A.natDegree := finiteEPolynomial_natDegree hA 0

/-- The exact homotopy input implies that the upper count at a nonzero
parameter is no larger than the lower count. -/
theorem finiteEPolynomial_upper_le_lower_of_upper_count_eq_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hcount :
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0)) :
    upperHalfPlaneRootCount (finiteEPolynomial A tau) ≤
      lowerHalfPlaneRootCount (finiteEPolynomial A tau) := by
  have htwice := twice_finiteEPolynomial_zero_upper_le_natDegree hA.ne_zero
  have hsum := finiteEPolynomial_upper_add_lower hA htau
  rw [← hcount] at htwice
  omega

/-- Root-count invariance supplies exactly the root-factor degree inequality
used by finite cross-angle injectivity. -/
theorem finiteEPolynomial_rootFactor_degree_le_of_upper_count_eq_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hcount :
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0)) :
    (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree ≤
      (lowerRootFactor (finiteEPolynomial A tau)).natDegree := by
  simpa using
    finiteEPolynomial_upper_le_lower_of_upper_count_eq_zero
      hA htau hcount

/-- Cross-angle injectivity with the true homotopy root-count statement as
its sole extra input. -/
theorem finiteAlgebraicCrossAngle_injective_of_upper_count_eq_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hcount :
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0)) :
    Function.Injective (finiteAlgebraicCrossAngle A tau) :=
  finiteAlgebraicCrossAngle_injective hA htau
    (finiteEPolynomial_rootFactor_degree_le_of_upper_count_eq_zero
      hA htau hcount)

/-- Exact algebraic Gram--Weil inertia with root-count invariance, rather
than a separately supplied degree inequality, as the remaining hypothesis. -/
theorem finiteAlgebraicGramWeilBlockDefect_hasQuadraticInertia_of_upper_count_eq_zero
    {A : ℝ[X]} (hA : A.Separable) {tau : ℝ} (htau : tau ≠ 0)
    (hcount :
      upperHalfPlaneRootCount (finiteEPolynomial A tau) =
        upperHalfPlaneRootCount (finiteEPolynomial A 0)) :
    HasQuadraticInertia
      (gramWeilBlockDefectOperator
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (gramWeilBlockDefectQuadratic
        (𝕜 := ℂ)
        (P := finiteResidualCoefficientHilbert A tau)
        (N := finiteAlgebraicNegativeSpace A tau)
        (finiteAlgebraicCrossAngle A tau))
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree
      ((conjugatePolynomial
          (lowerRootFactor (finiteEPolynomial A tau))).natDegree -
        (conjugatePolynomial
          (upperRootFactor (finiteEPolynomial A tau))).natDegree)
      (conjugatePolynomial
        (upperRootFactor (finiteEPolynomial A tau))).natDegree :=
  finiteAlgebraicGramWeilBlockDefect_hasQuadraticInertia hA htau
    (finiteEPolynomial_rootFactor_degree_le_of_upper_count_eq_zero
      hA htau hcount)

end

end RiemannGaussian
