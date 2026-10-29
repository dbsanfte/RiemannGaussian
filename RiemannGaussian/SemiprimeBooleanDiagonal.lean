/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Boolean Möbius diagonal extraction

Finite Boolean substitutions and forced-coordinate sums, with the true support
cutoff. This is algebraic counting correctness, independent of machine bounds.
-/
namespace RiemannGaussian.SemiprimeBooleanDiagonal
open scoped BigOperators
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Boolean Möbius coefficient, with the paper's exact sign. -/
def mobius (E : Finset ι) (f : Finset ι → R) : R :=
  ∑ U ∈ E.powerset, (-1 : R)^(E.card-U.card) * f U

omit [DecidableEq ι] in
theorem mobius_sub (E : Finset ι) (f g : Finset ι → R) :
    mobius E (fun U => f U-g U) = mobius E f-mobius E g := by
  simp [mobius, mul_sub, Finset.sum_sub_distrib]

theorem mobius_insert (E : Finset ι) (i : ι) (hi : i ∉ E) (f : Finset ι → R) :
    mobius (insert i E) f = mobius E (fun U => f (insert i U)-f U) := by
  unfold mobius
  rw [Finset.sum_powerset_insert hi]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hsub := Finset.mem_powerset.mp hU
  have hiU : i ∉ U := fun h => hi (hsub h)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hiU]
  have hn : E.card+1-U.card = (E.card-U.card)+1 := by omega
  rw [hn, pow_succ]
  simp only [Nat.add_sub_add_right]
  ring

/-- Full Boolean inversion for an arbitrary table; no polynomial hypothesis. -/
theorem sum_mobius (S : Finset ι) (f : Finset ι → R) :
    ∑ E ∈ S.powerset, mobius E f = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp [mobius]
  | @insert i S hi ih =>
    rw [Finset.sum_powerset_insert hi]
    have hs : (∑ E ∈ S.powerset, mobius (insert i E) f) =
        ∑ E ∈ S.powerset, mobius E (fun U => f (insert i U)-f U) := by
      apply Finset.sum_congr rfl
      intro E hE
      exact mobius_insert E i (fun h => hi ((Finset.mem_powerset.mp hE) h)) f
    rw [hs, ih, ih]
    ring

/-- A variable on which the Boolean table does not depend kills its Möbius coefficient. -/
theorem mobius_eq_zero_of_independent (E : Finset ι) (i : ι) (hi : i ∈ E)
    (f : Finset ι → R) (hf : ∀ U ⊆ E.erase i, f (insert i U) = f U) :
    mobius E f = 0 := by
  rw [← Finset.insert_erase hi, mobius_insert _ i (Finset.notMem_erase i E)]
  unfold mobius
  apply Finset.sum_eq_zero
  intro U hU
  change (-1 : R)^((E.erase i).card-U.card) * (f (insert i U)-f U) = 0
  rw [hf U (Finset.mem_powerset.mp hU), sub_self, mul_zero]

/-- Indicator-vector substitution into the original polynomial. -/
def indicator (U : Finset ι) (i : ι) : R := if i ∈ U then 1 else 0

omit [DecidableEq ι] in
theorem mobius_sum {A : Type*} (s : Finset A) (E : Finset ι)
    (f : A → Finset ι → R) :
    mobius E (fun U => ∑ a ∈ s, f a U) = ∑ a ∈ s, mobius E (f a) := by
  simp only [mobius, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A monomial cannot have a nonzero Boolean Möbius coefficient outside its support. -/
theorem mobius_monomial_eq_zero (E : Finset ι) (d : ι →₀ ℕ) (c : R)
    (h : ¬ E ⊆ d.support) :
    mobius E (fun U => MvPolynomial.eval (indicator U) (MvPolynomial.monomial d c)) = 0 := by
  obtain ⟨i, hi, hdi⟩ := Finset.not_subset.mp h
  apply mobius_eq_zero_of_independent E i hi
  intro U hU
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by intro heq; subst j; exact hdi hj
  simp [indicator, Finset.mem_insert, hji]

/-- The genuine polynomial degree implies the Boolean support cutoff. -/
theorem mobius_eval_eq_zero_of_totalDegree_lt (p : MvPolynomial ι R) (E : Finset ι)
    (h : p.totalDegree < E.card) :
    mobius E (fun U => MvPolynomial.eval (indicator U) p) = 0 := by
  have heval (U : Finset ι) : MvPolynomial.eval (indicator U) p =
      ∑ d ∈ p.support, MvPolynomial.eval (indicator U) (MvPolynomial.monomial d (p.coeff d)) := by
    conv_lhs => rw [p.as_sum]
    rw [MvPolynomial.eval_sum]
  simp_rw [heval]
  rw [mobius_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply mobius_monomial_eq_zero
  intro hsub
  have hcard : d.support.card ≤ d.sum (fun _ v => v) := by
    change d.support.card ≤ ∑ i ∈ d.support, d i
    calc
      _ = ∑ _i ∈ d.support, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have := Finsupp.mem_support_iff.mp hi
        omega
  have := MvPolynomial.le_totalDegree hd
  have := Finset.card_le_card hsub
  omega

/-- Pointwise Boolean reconstruction with the degree cutoff, before summing rows. -/
theorem eval_indicator_eq_sum_mobius (p : MvPolynomial ι R) (S : Finset ι)
    (q : ℕ) (hq : p.totalDegree ≤ q) :
    MvPolynomial.eval (indicator S) p =
      ∑ E ∈ S.powerset.filter (fun E => E.card ≤ q),
        mobius E (fun U => MvPolynomial.eval (indicator U) p) := by
  rw [← sum_mobius S (fun U => MvPolynomial.eval (indicator U) p)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro E hE hn
  have heq : ¬ E.card ≤ q := by
    intro hc
    exact hn (Finset.mem_filter.mpr ⟨hE, hc⟩)
  exact mobius_eval_eq_zero_of_totalDegree_lt p E (by omega)

/-- Ambient-set form exposes precisely the forced Boolean coordinates. -/
theorem eval_indicator_eq_sum_ambient (p : MvPolynomial ι R) (S x : Finset ι)
    (hx : x ⊆ S) (q : ℕ) (hq : p.totalDegree ≤ q) :
    MvPolynomial.eval (indicator x) p =
      ∑ E ∈ S.powerset.filter (fun E => E.card ≤ q),
        if E ⊆ x then mobius E (fun U => MvPolynomial.eval (indicator U) p) else 0 := by
  rw [← Finset.sum_filter]
  have hf : (S.powerset.filter (fun E => E.card ≤ q)).filter (fun E => E ⊆ x) =
      x.powerset.filter (fun E => E.card ≤ q) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro h
      exact ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨h.1.trans hx, h.2⟩, h.1⟩
  rw [hf]
  exact eval_indicator_eq_sum_mobius p x q hq

/-- Paper Lemma 3.3: arbitrary row-dependent polynomials, degree cutoff,
original signs, and assignments forced to one on E. Assignments are represented
by their subsets of one coordinates. -/
theorem boolean_diagonal (S : Finset ι) (q : ℕ)
    (p : Finset ι → MvPolynomial ι R)
    (hp : ∀ x ∈ S.powerset, (p x).totalDegree ≤ q) :
    (∑ x ∈ S.powerset, MvPolynomial.eval (indicator x) (p x)) =
      ∑ E ∈ S.powerset.filter (fun E => E.card ≤ q),
        ∑ U ∈ E.powerset, (-1 : R)^(E.card-U.card) *
          ∑ x ∈ S.powerset.filter (fun x => E ⊆ x),
            MvPolynomial.eval (indicator U) (p x) := by
  calc
    _ = ∑ x ∈ S.powerset, ∑ E ∈ S.powerset.filter (fun E => E.card ≤ q),
          if E ⊆ x then mobius E (fun U => MvPolynomial.eval (indicator U) (p x)) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact eval_indicator_eq_sum_ambient (p x) S x (Finset.mem_powerset.mp hx) q (hp x hx)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E hE
      rw [← Finset.sum_filter]
      simp only [mobius]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U hU
      rw [Finset.mul_sum]

/-- All retained Taylor coefficients use the same E,U menu. The hypothesis is
only the degree filtration (paper (3.9)), not a supplied diagonal identity. -/
theorem retained_taylor_diagonal (S : Finset ι) (J : ℕ)
    (G : Finset ι → Polynomial (MvPolynomial ι R))
    (hG : ∀ x ∈ S.powerset, ∀ j < J, ((G x).coeff j).totalDegree ≤ j)
    (j : ℕ) (hj : j < J) :
    (∑ x ∈ S.powerset, MvPolynomial.eval (indicator x) ((G x).coeff j)) =
      ∑ E ∈ S.powerset.filter (fun E => E.card ≤ J-1),
        ∑ U ∈ E.powerset, (-1 : R)^(E.card-U.card) *
          ∑ x ∈ S.powerset.filter (fun x => E ⊆ x),
            MvPolynomial.eval (indicator U) ((G x).coeff j) := by
  apply boolean_diagonal
  intro x hx
  exact (hG x hx j hj).trans (by omega)

#print axioms retained_taylor_diagonal
#print axioms boolean_diagonal
#print axioms mobius_eval_eq_zero_of_totalDegree_lt
#print axioms eval_indicator_eq_sum_mobius
#print axioms sum_mobius
#print axioms mobius_eq_zero_of_independent
end RiemannGaussian.SemiprimeBooleanDiagonal
