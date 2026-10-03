/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeStagedSeed

/-!
# Geometric row cancellation and the literal row step

Adjacent geometric targets have a degree-one cleared telescoping
identity, valid even at zero factors. Our literal row targets step by
alpha^N. When that step moves the whole root interval to a disjoint
interval, every nonzero polynomial denominator in a first-order
functional recurrence has degree at least the original interval length.
The saved long-period control realizes this disjoint case. This is a
restriction on a specific recurrence, not a lower bound on all residual
algorithms or on interpolation at a finite list of rows.
-/

namespace RiemannGaussian.SemiprimeGeometricRows

open scoped BigOperators
open Polynomial SemiprimeIntervalJet

/-- Retain the degree-L original target polynomial. -/
noncomputable def rowPolynomial {R : Type*} [CommRing R] (alpha : R) (L : ℕ) : R[X] :=
  SemiprimeCartesianCompletion.rootPolynomial (Finset.range L) (fun u => alpha^u)

theorem rowPolynomial_eval {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    (rowPolynomial alpha L).eval x=intervalProduct alpha x L := by
  simp only [rowPolynomial, SemiprimeCartesianCompletion.rootPolynomial,
    eval_prod, eval_sub, eval_X, eval_C, intervalProduct]

/-- Extending the original interval adds its next factor exactly. -/
theorem intervalProduct_succ {R : Type*} [CommRing R] (alpha x : R) (L : ℕ) :
    intervalProduct alpha x (L+1)=intervalProduct alpha x L*(x-alpha^L) :=
  Finset.prod_range_succ _ _

/-- Adjacent powers have an exact endpoint cancellation. Clearing both
endpoint factors preserves zeros and requires no inverse or unit test. -/
theorem adjacent_target_telescoping {R : Type*} [CommRing R]
    (alpha x : R) (L : ℕ) :
    intervalProduct alpha (alpha*x) L*(alpha*x-alpha^L)=
      alpha^L*(alpha*x-1)*intervalProduct alpha x L := by
  induction L with
  | zero => simp [intervalProduct]
  | succ L ih =>
    rw [intervalProduct_succ, intervalProduct_succ]
    calc
      _ = (intervalProduct alpha (alpha*x) L*(alpha*x-alpha^L))*
          (alpha*x-alpha^(L+1)) := by ring
      _ = (alpha^L*(alpha*x-1)*intervalProduct alpha x L)*
          (alpha*x-alpha^(L+1)) := by rw [ih]
      _ = _ := by rw [pow_succ]; ring

/-- The adjacent-target identity holds at the original polynomial
source, before evaluation or cancellation of any potentially zero factor. -/
theorem adjacent_polynomial_telescoping {R : Type*} [CommRing R]
    (alpha : R) (L : ℕ) :
    (rowPolynomial alpha L).comp (C alpha*X)*(C alpha*X-C (alpha^L))=
      C (alpha^L)*(C alpha*X-1)*rowPolynomial alpha L := by
  have h := adjacent_target_telescoping (C alpha) (X : R[X]) L
  simpa only [intervalProduct, map_pow, rowPolynomial,
    SemiprimeCartesianCompletion.rootPolynomial, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.C_comp] using h

/-- A disjoint shifted interval keeps every original root away from
the shifted polynomial. All exponent ranges remain explicit. -/
theorem shifted_interval_nonzero {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L d : ℕ} (hLd : L≤d) (hdL : d+L≤orderOf alpha) :
    ∀ u<L, intervalProduct alpha (alpha^d*alpha^u) L≠0 := by
  intro u hu hz
  obtain ⟨v, hv, he⟩ := (intervalProduct_zero_iff _ _ _).mp hz
  rw [← pow_add] at he
  have hdu : d+u<orderOf alpha := by omega
  have hvOrder : v<orderOf alpha := by omega
  have hev := pow_injOn_Iio_orderOf hdu hvOrder he
  omega

/-- If a polynomial recurrence clears a denominator after shifting to
an interval disjoint from the original roots, that denominator must
vanish at every original root. Its degree cannot be made small. -/
theorem functional_step_denominator_degree {R : Type*} [CommRing R] [IsDomain R]
    (alpha beta : R) {L : ℕ} (hL : L≤orderOf alpha) (A D : R[X]) (hD : D≠0)
    (hshift : ∀ u<L, intervalProduct alpha (beta*alpha^u) L≠0)
    (hrec : A*rowPolynomial alpha L=
      D*(rowPolynomial alpha L).comp (C beta*X)) : L≤D.natDegree := by
  apply interval_annihilator_degree alpha hL D hD
  intro u hu
  have he := congrArg (fun P : R[X] => P.eval (alpha^u)) hrec
  have hz : intervalProduct alpha (alpha^u) L=0 :=
    (intervalProduct_zero_iff _ _ _).mpr ⟨u, hu, rfl⟩
  simp only [eval_mul, eval_comp, eval_X, eval_C, rowPolynomial_eval, hz,
    mul_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (hshift u hu)

/-- A step by alpha^d with no overlap forces a degree-L denominator.
This excludes this particular short rational recurrence, not other
representations of the original residuals. -/
theorem disjoint_step_denominator_degree {R : Type*} [CommRing R] [IsDomain R]
    (alpha : R) {L d : ℕ} (hLd : L≤d) (hdL : d+L≤orderOf alpha)
    (A D : R[X]) (hD : D≠0)
    (hrec : A*rowPolynomial alpha L=
      D*(rowPolynomial alpha L).comp (C (alpha^d)*X)) : L≤D.natDegree := by
  apply functional_step_denominator_degree alpha (alpha^d) (by omega) A D hD
    (shifted_interval_nonzero alpha hLd hdL) hrec

/-- The saved public row step is a large shift inside the retained
smaller-field period, rather than a step to the adjacent power. -/
theorem control_row_step :
    (1823692905 : ZMod 44963)^2803308161=
      (1823692905 : ZMod 44963)^17385 ∧
    (4333 : ℕ)≤17385 ∧ 17385+4333≤22481 := by
  have horder := SemiprimeCentreFreeCover.control_long_local_orders.1
  constructor
  · have he := pow_mod_orderOf (1823692905 : ZMod 44963) 2803308161
    rw [horder] at he
    exact he.symm
  · norm_num

/-- On the original saved long-period input, a first-order polynomial
recurrence for adjacent row labels needs denominator degree at least
4333. Interpolation only at the 38 selected targets is outside its scope. -/
theorem control_row_denominator_degree (A D : (ZMod 44963)[X]) (hD : D≠0)
    (hrec : A*rowPolynomial (1823692905 : ZMod 44963) 4333=
      D*(rowPolynomial (1823692905 : ZMod 44963) 4333).comp
        (C ((1823692905 : ZMod 44963)^2803308161)*X)) : 4333≤D.natDegree := by
  have hp : Nat.Prime 44963 := by norm_num
  let : Fact (Nat.Prime 44963) := ⟨hp⟩
  rw [control_row_step.1] at hrec
  apply disjoint_step_denominator_degree (d:=17385) _ (by norm_num) _ A D hD hrec
  rw [SemiprimeCentreFreeCover.control_long_local_orders.1]
  norm_num

/-- The degree-one adjacent-power shortcut cannot implement the
literal row step in this control. -/
theorem control_no_degree_one_step (A D : (ZMod 44963)[X]) (hD : D≠0)
    (hsmall : D.natDegree≤1) :
    A*rowPolynomial (1823692905 : ZMod 44963) 4333≠
      D*(rowPolynomial (1823692905 : ZMod 44963) 4333).comp
        (C ((1823692905 : ZMod 44963)^2803308161)*X) := by
  intro he
  have hh := control_row_denominator_degree A D hD he
  omega

end RiemannGaussian.SemiprimeGeometricRows
