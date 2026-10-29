/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeStreamingTensor
import RiemannGaussian.SemiprimeBooleanDiagonal

/-!
# Taylor degree filtration of the actual corrected tensor product

Each nonconstant correction carries a positive power of z and is linear in the
independent Boolean indeterminates. The streamed tensor evaluator preserves this
filtration, yielding the concrete frontend for Boolean diagonal extraction.
-/
namespace RiemannGaussian.SemiprimeCounterFiltration
open scoped BigOperators
open RiemannGaussian.SemiprimeStreamingTensor
open RiemannGaussian.SemiprimeBooleanDiagonal
variable {V : Type*}

/-- Paper (3.9), expressed coefficientwise. -/
def Filtered (p : Polynomial (MvPolynomial V ℚ)) : Prop :=
  ∀ j, (p.coeff j).totalDegree ≤ j

theorem filtered_scalar (c : ℚ) : Filtered (Polynomial.C (MvPolynomial.C c : MvPolynomial V ℚ)) := by
  intro j
  simp only [Polynomial.coeff_C]
  split_ifs <;> simp [MvPolynomial.totalDegree_C]

theorem filtered_add {p q : Polynomial (MvPolynomial V ℚ)} (hp : Filtered p) (hq : Filtered q) :
    Filtered (p+q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hp j) (hq j))

theorem filtered_mul {p q : Polynomial (MvPolynomial V ℚ)} (hp : Filtered p) (hq : Filtered q) :
    Filtered (p*q) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [hsum] using Nat.add_le_add (hp ij.1) (hq ij.2))

theorem filtered_sub {p q : Polynomial (MvPolynomial V ℚ)} (hp : Filtered p) (hq : Filtered q) :
    Filtered (p-q) := by
  have h := filtered_add hp (filtered_mul (filtered_scalar (-1)) hq)
  have heq : p + Polynomial.C (MvPolynomial.C (-1 : ℚ)) * q = p-q := by
    simp only [map_neg, map_one]
    ring
  rw [heq] at h
  exact h

theorem filtered_sum {A : Type*} (s : Finset A) (p : A → Polynomial (MvPolynomial V ℚ))
    (hp : ∀ a ∈ s, Filtered (p a)) : Filtered (∑ a ∈ s, p a) := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact MvPolynomial.totalDegree_finsetSum_le (fun a ha => hp a ha j)

theorem filtered_prod {A : Type*} (s : Finset A) (p : A → Polynomial (MvPolynomial V ℚ))
    (hp : ∀ a ∈ s, Filtered (p a)) : Filtered (∏ a ∈ s, p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using filtered_scalar (V := V) 1
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact filtered_mul (hp a (Finset.mem_insert_self a s))
      (ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)))

/-- Actual linear correction with independently supplied rational row entries. -/
noncomputable def linearForm [Fintype V] (row : V → ℚ) : MvPolynomial V ℚ :=
  ∑ v, MvPolynomial.C (row v) * MvPolynomial.X v

theorem linearForm_degree [Fintype V] (row : V → ℚ) : (linearForm row).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro v hv
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C])

theorem filtered_positive_monomial [Fintype V] (d : ℕ) (row : V → ℚ) :
    Filtered (Polynomial.monomial (d+1) (linearForm row)) := by
  intro j
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · have := linearForm_degree row
    omega
  · simp

/-- Independent scalar base and finitely many positive-degree linear corrections. -/
noncomputable def inputPort [Fintype V] (base : ℚ) (D : ℕ) (rows : ℕ → V → ℚ) :
    Polynomial (MvPolynomial V ℚ) :=
  Polynomial.C (MvPolynomial.C base) +
    ∑ d ∈ Finset.range D, Polynomial.monomial (d+1) (linearForm (rows d))

theorem filtered_inputPort [Fintype V] (base : ℚ) (D : ℕ) (rows : ℕ → V → ℚ) :
    Filtered (inputPort base D rows) :=
  filtered_add (filtered_scalar base)
    (filtered_sum _ _ (fun d _ => filtered_positive_monomial d (rows d)))

theorem filtered_evaluate (w : ℕ) (T : (Fin w → Bool) → ℚ)
    (ports : Fin w → Polynomial (MvPolynomial V ℚ)) (hp : ∀ i, Filtered (ports i)) :
    Filtered (evaluate w (fun a => Polynomial.C (MvPolynomial.C (T a))) ports) := by
  induction w with
  | zero => exact filtered_scalar _
  | succ w ih =>
    exact filtered_add
      (filtered_mul (filtered_sub (by simpa using filtered_scalar (V := V) 1) (hp 0))
        (ih _ _ (fun i => hp i.succ)))
      (filtered_mul (hp 0) (ih _ _ (fun i => hp i.succ)))

/-- Concrete G_x: streamed multilinear local tensors on scalar bases plus
positive-z-degree linear corrections, multiplied over all factors. -/
noncomputable def correctedProduct [Fintype V] {E : Type*} [Fintype E]
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (base : (e : E) → Fin (arity e) → ℚ) (D : ℕ)
    (rows : (e : E) → Fin (arity e) → ℕ → V → ℚ) :
    Polynomial (MvPolynomial V ℚ) :=
  ∏ e, evaluate (arity e) (fun a => Polynomial.C (MvPolynomial.C (T e a)))
    (fun i => inputPort (base e i) D (rows e i))

theorem filtered_correctedProduct [Fintype V] {E : Type*} [Fintype E]
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (base : (e : E) → Fin (arity e) → ℚ) (D : ℕ)
    (rows : (e : E) → Fin (arity e) → ℕ → V → ℚ) :
    Filtered (correctedProduct arity T base D rows) := by
  apply filtered_prod
  intro e he
  apply filtered_evaluate
  intro i
  exact filtered_inputPort _ _ _

/-- Counter frontend for all retained Taylor coefficients: no degree-filtration
hypothesis is supplied; it is proved from the actual input and tensor recursion. -/
theorem correctedProduct_taylor_diagonal [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] (S : Finset V) (J : ℕ)
    (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (base : Finset V → (e : E) → Fin (arity e) → ℚ) (D : ℕ)
    (rows : (e : E) → Fin (arity e) → ℕ → V → ℚ)
    (j : ℕ) (hj : j < J) :
    (∑ x ∈ S.powerset, MvPolynomial.eval (indicator x)
      ((correctedProduct arity T (base x) D rows).coeff j)) =
      ∑ A ∈ S.powerset.filter (fun A => A.card ≤ J-1),
        ∑ U ∈ A.powerset, (-1 : ℚ)^(A.card-U.card) *
          ∑ x ∈ S.powerset.filter (fun x => A ⊆ x),
            MvPolynomial.eval (indicator U)
              ((correctedProduct arity T (base x) D rows).coeff j) := by
  apply retained_taylor_diagonal S J (fun x => correctedProduct arity T (base x) D rows)
    (fun x _ k _ => filtered_correctedProduct arity T (base x) D rows k) j hj

#print axioms filtered_correctedProduct
#print axioms correctedProduct_taylor_diagonal
#print axioms filtered_evaluate
#print axioms filtered_inputPort
end RiemannGaussian.SemiprimeCounterFiltration
