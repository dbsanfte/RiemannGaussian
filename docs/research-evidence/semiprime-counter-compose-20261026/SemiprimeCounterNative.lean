/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterFiltration

/-!
# Native replacement rows and the corrected counting polynomial

The global polynomial, its zero value and total-incidence degree are constructed
from replacement rows. Taylor naturality connects it to the actual corrected
streaming product rather than assuming the desired counter identity.
-/
namespace RiemannGaussian.SemiprimeCounterNative
open scoped BigOperators
open Polynomial
open RiemannGaussian.SemiprimeStreamingTensor
open RiemannGaussian.SemiprimeBooleanDiagonal
open RiemannGaussian.SemiprimeCounterFiltration

/-- Ring homomorphisms commute with the exact streamed tensor recursion. -/
theorem evaluate_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (w : ℕ) (T : (Fin w → Bool) → A) (ports : Fin w → A) :
    f (evaluate w T ports) = evaluate w (fun a => f (T a)) (fun i => f (ports i)) := by
  induction w with
  | zero => rfl
  | succ w ih => simp [evaluate, ih]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

/-- A replacement-row linear form evaluated on an actual Boolean assignment. -/
noncomputable def rowPort (rows : V → Polynomial ℚ) (x : Finset V) : Polynomial ℚ :=
  ∑ v, rows v * C (indicator x v)

/-- Actual product of streamed local tensor extensions on replacement ports. -/
noncomputable def rowProduct (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (x : Finset V) : Polynomial ℚ :=
  ∏ e, evaluate (arity e) (fun a => C (T e a)) (fun i => rowPort (rows e i) x)

/-- Global counting polynomial, summing each Boolean assignment once. -/
noncomputable def globalPolynomial (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) : Polynomial ℚ :=
  ∑ x : Finset V, rowProduct arity T rows x

/-- Original Boolean tensor contraction with supplied physical port coordinates. -/
noncomputable def originalContraction (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (coordinate : (e : E) → Fin (arity e) → V) : ℚ :=
  ∑ x : Finset V, ∏ e, T e (fun i => decide (coordinate e i ∈ x))

theorem globalPolynomial_at_zero (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ)
    (coordinate : (e : E) → Fin (arity e) → V)
    (hrestore : ∀ e i v, (rows e i v).eval 0 = if v=coordinate e i then 1 else 0) :
    (globalPolynomial arity T rows).eval 0 = originalContraction arity T coordinate := by
  classical
  simp only [globalPolynomial, originalContraction, rowProduct, eval_finsetSum, eval_prod]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro e he
  change (Polynomial.evalRingHom 0) (evaluate (arity e) (fun a => C (T e a))
    (fun i => rowPort (rows e i) x)) = _
  rw [RiemannGaussian.SemiprimeCounterNative.evaluate_map (A := Polynomial ℚ) (B := ℚ)
    (Polynomial.evalRingHom 0) (arity e) (fun a => C (T e a)) (fun i => rowPort (rows e i) x)]
  have hp : (fun i => (rowPort (rows e i) x).eval 0) =
      (fun i => bit (decide (coordinate e i ∈ x)) : Fin (arity e) → ℚ) := by
    funext i
    simp only [rowPort, eval_finsetSum, eval_mul, eval_C, hrestore]
    simp [indicator, bit]
  simp only [Polynomial.coe_evalRingHom, eval_C]
  change evaluate (arity e) (fun a => T e a) (fun i => (rowPort (rows e i) x).eval 0) = _
  rw [hp, boolean_recovery]

theorem rowPort_degree (rows : V → Polynomial ℚ) (x : Finset V) (R : ℕ)
    (hrows : ∀ v, (rows v).natDegree ≤ R) : (rowPort rows x).natDegree ≤ R := by
  apply natDegree_sum_le_of_forall_le
  intro v hv
  exact (natDegree_mul_C_le _ _).trans (hrows v)

theorem globalPolynomial_degree (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (R : ℕ)
    (hrows : ∀ e i v, (rows e i v).natDegree ≤ R) :
    (globalPolynomial arity T rows).natDegree ≤ (∑ e, arity e)*R := by
  exact natDegree_sum_product_evaluate_le arity T (fun x e i => rowPort (rows e i) x) R
    (fun x e i => rowPort_degree (rows e i) x R (hrows e i))

/-- Map a corrected input at a fixed independent Boolean substitution. -/
theorem inputPort_map (U : Finset V) (base : ℚ) (D : ℕ) (rows : ℕ → V → ℚ) :
    (inputPort base D rows).map (MvPolynomial.eval (indicator U)) =
      C base + ∑ d ∈ Finset.range D, monomial (d+1) (∑ v, rows d v * indicator U v) := by
  simp [inputPort, linearForm, Polynomial.map_add, Polynomial.map_sum,
    Polynomial.map_monomial ]

/-- Actual fixed-U product frontend for the shared-summary contraction. -/
theorem correctedProduct_map (U : Finset V) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (base : (e : E) → Fin (arity e) → ℚ) (D : ℕ)
    (rows : (e : E) → Fin (arity e) → ℕ → V → ℚ) :
    (correctedProduct arity T base D rows).map (MvPolynomial.eval (indicator U)) =
      ∏ e, evaluate (arity e) (fun a => C (T e a))
        (fun i => (inputPort (base e i) D (rows e i)).map (MvPolynomial.eval (indicator U))) := by
  simp only [correctedProduct, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro e he
  have h := RiemannGaussian.SemiprimeCounterNative.evaluate_map
    (A := Polynomial (MvPolynomial V ℚ)) (B := Polynomial ℚ)
    (Polynomial.mapRingHom (MvPolynomial.eval (indicator U : V → ℚ)))
    (arity e) (fun a => Polynomial.C (MvPolynomial.C (T e a)))
    (fun i => inputPort (base e i) D (rows e i))
  simpa using h


/-- Exact finite positive-degree expansion of a shifted replacement row. -/
theorem taylor_row_expansion (p : Polynomial ℚ) (t : ℚ) (R : ℕ) (hp : p.natDegree ≤ R) :
    taylor t p = C (p.eval t) +
      ∑ d ∈ Finset.range R, monomial (d+1) ((taylor t p).coeff (d+1)) := by
  conv_lhs => rw [(taylor t p).as_sum_range' (R+1) (by rw [natDegree_taylor]; omega)]
  rw [Finset.sum_range_succ']
  simp only [monomial_zero_left, taylor_coeff_zero]
  rw [add_comm]

/-- The concrete corrected port, specialized back to its assignment, is exactly
the shifted original row port. -/
theorem shifted_inputPort (rows : V → Polynomial ℚ) (x : Finset V) (t : ℚ) (R : ℕ)
    (hp : ∀ v, (rows v).natDegree ≤ R) :
    (inputPort (∑ v, (rows v).eval t * indicator x v) R
      (fun d v => (taylor t (rows v)).coeff (d+1))).map (MvPolynomial.eval (indicator x)) =
      taylor t (rowPort rows x) := by
  rw [inputPort_map]
  simp only [rowPort, map_sum, taylor_mul, taylor_C]
  have hexpand : (∑ v, taylor t (rows v) * C (indicator x v)) =
      ∑ v, (C ((rows v).eval t) + ∑ d ∈ Finset.range R,
        monomial (d+1) ((taylor t (rows v)).coeff (d+1))) * C (indicator x v) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact congrArg (fun p : Polynomial ℚ => p*C (indicator x v))
      (taylor_row_expansion (rows v) t R (hp v))
  rw [hexpand]
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, monomial_mul_C]
  rw [Finset.sum_comm]
  congr 1
  · simp only [← C_mul, ← map_sum]

theorem taylor_evaluate (t : ℚ) (w : ℕ) (T : (Fin w → Bool) → ℚ)
    (ports : Fin w → Polynomial ℚ) :
    taylor t (evaluate w (fun a => C (T a)) ports) =
      evaluate w (fun a => C (T a)) (fun i => taylor t (ports i)) := by
  induction w with
  | zero => simp [evaluate]
  | succ w ih => simp [evaluate, taylor_mul, ih]

/-- Native scalar bases of the shifted counter. -/
noncomputable def shiftedBase (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (x : Finset V) :
    (e : E) → Fin (arity e) → ℚ :=
  fun e i => ∑ v, (rows e i v).eval t * indicator x v

/-- Native positive-degree coefficients of the shifted rows. -/
noncomputable def shiftedRows (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) :
    (e : E) → Fin (arity e) → ℕ → V → ℚ :=
  fun e i d v => (taylor t (rows e i v)).coeff (d+1)

/-- Exact (3.7)--(3.8) specialization: X=x recovers the shifted original row product. -/
theorem correctedProduct_shift (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R) (x : Finset V) :
    (correctedProduct arity T (shiftedBase arity rows t x) R (shiftedRows arity rows t)).map
      (MvPolynomial.eval (indicator x)) = taylor t (rowProduct arity T rows x) := by
  rw [correctedProduct_map]
  simp only [rowProduct]
  have hprod (f : E → Polynomial ℚ) : taylor t (∏ e, f e) = ∏ e, taylor t (f e) := by
    exact map_prod (taylorAlgHom t) f Finset.univ
  rw [hprod]
  apply Finset.prod_congr rfl
  intro e he
  rw [taylor_evaluate]
  congr 1
  funext i
  exact shifted_inputPort (rows e i) x t R (hp e i)

/-- Exact retained-coefficient handoff to the actual Boolean diagonal theorem. -/
theorem globalPolynomial_taylor_coeff (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R : ℕ)
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R) (j : ℕ) :
    (taylor t (globalPolynomial arity T rows)).coeff j =
      ∑ x : Finset V, MvPolynomial.eval (indicator x)
        ((correctedProduct arity T (shiftedBase arity rows t x) R
          (shiftedRows arity rows t)).coeff j) := by
  simp only [globalPolynomial, map_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← correctedProduct_shift arity T rows t R hp x]
  rw [coeff_map]

/-- The all-subset assignment sum agrees exactly with the diagonal's ambient cube. -/
theorem globalPolynomial_eq_powerset (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) :
    globalPolynomial arity T rows =
      ∑ x ∈ (Finset.univ : Finset V).powerset, rowProduct arity T rows x := by
  simp [globalPolynomial]

/-- Fully native Taylor/Möbius identity, ready for actual shared-summary grouping. -/
theorem native_taylor_diagonal (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → V → Polynomial ℚ) (t : ℚ) (R J : ℕ)
    (hp : ∀ e i v, (rows e i v).natDegree ≤ R) (j : ℕ) (hj : j < J) :
    (taylor t (globalPolynomial arity T rows)).coeff j =
      ∑ A ∈ (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ J-1),
        ∑ U ∈ A.powerset, (-1 : ℚ)^(A.card-U.card) *
          ∑ x ∈ (Finset.univ : Finset V).powerset.filter (fun x => A ⊆ x),
            MvPolynomial.eval (indicator U)
              ((correctedProduct arity T (shiftedBase arity rows t x) R
                (shiftedRows arity rows t)).coeff j) := by
  rw [globalPolynomial_taylor_coeff arity T rows t R hp]
  have h := correctedProduct_taylor_diagonal (Finset.univ : Finset V) J arity T
    (shiftedBase arity rows t) R (shiftedRows arity rows t) j hj
  simpa using h

/-- Fixed-U coefficient handoff, with the input ports literally mapped. -/
theorem correctedProduct_coeff_eval (U : Finset V) (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (base : (e : E) → Fin (arity e) → ℚ) (D : ℕ)
    (rows : (e : E) → Fin (arity e) → ℕ → V → ℚ) (j : ℕ) :
    MvPolynomial.eval (indicator U) ((correctedProduct arity T base D rows).coeff j) =
      (∏ e, evaluate (arity e) (fun a => C (T e a))
        (fun i => (inputPort (base e i) D (rows e i)).map
          (MvPolynomial.eval (indicator U)))).coeff j := by
  rw [← correctedProduct_map U arity T base D rows, coeff_map]

#print axioms native_taylor_diagonal
#print axioms correctedProduct_coeff_eval
#print axioms correctedProduct_shift
#print axioms globalPolynomial_taylor_coeff
#print axioms correctedProduct_map
#print axioms globalPolynomial_at_zero
#print axioms globalPolynomial_degree
end RiemannGaussian.SemiprimeCounterNative
