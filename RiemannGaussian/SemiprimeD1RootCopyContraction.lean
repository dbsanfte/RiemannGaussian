/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootNetworkOrder
import RiemannGaussian.SemiprimeD1SemiprimePrefix

/-! # Exact finite contraction of the acquired root copy tensors
The finite algebra preserves isolated-variable multiplicity: each owner sums
its two prefix-compatible values, even when its incidence fibre is empty.
The concrete root endpoint must still identify its actual literal table entries
and port orders with this finite algebra.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeD1RootCopyContraction
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite products of literal zero/one tests are one exactly when all tests hold. -/
theorem prod_indicator {V R : Type*} [Fintype V] [CommSemiring R] (P : V→Prop) :
    (∏v,if P v then (1:R) else 0)=if ∀v,P v then 1 else 0 := by
  classical
  by_cases h : ∀v,P v
  · simp [h]
  · simp only [h,ite_false]
    obtain ⟨v,hv⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [hv,ite_false])

/-- Semantic value of one literal root copy tensor, with prefix compatibility. -/
def copyWeight {I V R : Type*} [CommSemiring R]
    (owner : I→V) (allowed : V→Bool→Prop) (a : I→Bool) (v : V) : R :=
  ∑b : Bool,@ite R (allowed v b ∧ ∀i,owner i=v → a i=b) (Classical.propDecidable _) 1 0

/-- Copy-tensor consistency is exactly one pullback of the original owner bits. -/
theorem consistency_iff {I V : Type*} (owner : I→V) (allowed : V→Bool→Prop)
    (a : I→Bool) (bits : V→Bool) :
    (∀v,allowed v (bits v) ∧ ∀i,owner i=v → a i=bits v) ↔
      (∀v,allowed v (bits v)) ∧ a=(fun i => bits (owner i)) := by
  constructor
  · intro h
    exact ⟨fun v => (h v).1,funext (fun i => (h (owner i)).2 i rfl)⟩
  · rintro ⟨ha,rfl⟩ v
    exact ⟨ha v,fun i hi => by change bits (owner i)=bits v; rw [hi]⟩

/-- Exact copy contraction, including empty incidence fibres and arbitrary
repeated/conflicting prefix tests. No count or incidence-surjectivity advice. -/
theorem contraction {I V R : Type*} [Fintype I] [Fintype V]
    [DecidableEq I] [DecidableEq V] [CommSemiring R]
    (owner : I→V) (allowed : V→Bool→Prop) (factor : (I→Bool)→R) :
    (∑a : I→Bool,factor a*∏v,copyWeight owner allowed a v)=
      ∑bits : V→Bool,if ∀v,allowed v (bits v) then factor (fun i => bits (owner i)) else 0 := by
  classical
  unfold copyWeight
  simp_rw [Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  by_cases ha : ∀v,allowed v (bits v)
  · conv_rhs => rw [ite_eq_left ha]
    rw [Finset.sum_eq_single (fun i => bits (owner i))]
    · have hp : (∏v,@ite R (allowed v (bits v) ∧ ∀i,owner i=v → bits (owner i)=bits v) (Classical.propDecidable _) 1 0)=1 := by
        apply Finset.prod_eq_one
        intro v _
        exact ite_eq_left ⟨ha v,fun i hi => congrArg bits hi⟩
      rw [hp,mul_one]
    · intro a _ hn
      have he : ∃i,a i≠bits (owner i) := Function.ne_iff.mp hn
      obtain ⟨i,hi⟩ := he
      have hp : (∏v,@ite R (allowed v (bits v) ∧ ∀i,owner i=v → a i=bits v) (Classical.propDecidable _) 1 0)=0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (owner i))
        exact ite_eq_right (fun h => hi (h.2 i rfl))
      rw [hp,mul_zero]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  · conv_rhs => rw [ite_eq_right ha]
    obtain ⟨v,hv⟩ := not_forall.mp ha
    apply Finset.sum_eq_zero
    intro a _
    have hp : (∏v,@ite R (allowed v (bits v) ∧ ∀i,owner i=v → a i=bits v) (Classical.propDecidable _) 1 0)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      exact ite_eq_right (fun h => hv h.1)
    rw [hp,mul_zero]

end
end RiemannGaussian.SemiprimeD1RootCopyContraction
