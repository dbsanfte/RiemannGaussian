/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootOwnerSemantics

/-! # Original Boolean assignment count as a finite scalar contraction
The Boolean-function/Finset equivalence is explicit. Prefix records remain the
original records; no satisfying assignment/count or coverage is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1RootBooleanCount
open scoped BigOperators
open SemiprimeCounterSearch SemiprimeCountRecovery SemiprimeD1RootOwnerSemantics
open SemiprimeD1RootOwnerTables
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Complete original finite assignments, with literal characteristic-bit decode. -/
def assignmentEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n→Bool) where
  toFun := assignmentBit
  invFun bits := Finset.univ.filter (fun v => bits v)
  left_inv x := by ext v; simp only [Finset.mem_filter,Finset.mem_univ,true_and,assignmentBit,decide_eq_true_eq]
  right_inv bits := by
    funext v
    cases h : bits v <;> simp [assignmentBit,h]

/-- Products of actual Boolean checker indicators are their conjunction. -/
theorem prod_bool {E R : Type*} [Fintype E] [CommSemiring R] (test : E→Bool) :
    (∏e,if test e then (1:R) else 0)=if ∀e,test e=true then 1 else 0 := by
  classical
  by_cases h : ∀e,test e=true
  · conv_rhs => rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro e _
    exact ite_eq_left (h e)
  · conv_rhs => rw [ite_eq_right h]
    obtain ⟨e,he⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right he)

/-- Exact original-prefix acceptance count in any scalar semiring. This is a
finite algebra lemma; the actual root producer is instantiated separately. -/
theorem boolean_count {E : Type} {R : Type*} [Fintype E] [CommSemiring R] (n : ℕ)
    (arity : E→ℕ) (table : (e : E)→(Fin (arity e)→Bool)→Bool)
    (coordinate : (e : E)→Fin (arity e)→Fin n) (fixed : List (Fin n×Bool)) :
    (∑bits : Fin n→Bool,if ∀v,allowed fixed v (bits v)=true then
      (∏e,if table e (fun j => bits (coordinate e j)) then (1:R) else 0) else 0)=
      (acceptedCount (restricted assignmentBit (originalPredicate arity table coordinate) fixed):R) := by
  classical
  rw [←(assignmentEquiv n).sum_comp]
  unfold acceptedCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (if ∀v,allowed fixed v (assignmentBit x v)=true then
      (∏e,if table e (fun j => assignmentBit x (coordinate e j)) then (1:R) else 0) else 0)=_
  rw [prod_bool]
  have hp := prefix_allowed_iff fixed (assignmentBit x)
  by_cases hf : fixed.all (fun p => assignmentBit x p.1 == p.2)=true
  · have ha := hp.mpr hf
    by_cases ht : ∀e,table e (fun j => assignmentBit x (coordinate e j))=true
    · simp [ha,ht,restricted,originalPredicate,hf]
    · simp [ha,ht,restricted,originalPredicate]
  · have ha := hp.not.mpr hf
    have hfalse : fixed.all (fun p => assignmentBit x p.1 == p.2)=false := Bool.eq_false_iff.mpr hf
    simp [ha,restricted,hfalse]

end
end RiemannGaussian.SemiprimeD1RootBooleanCount
