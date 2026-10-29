/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecords

/-! # Linear sequential-merge reports
The record-count factor is linear. Key and full payload bytes are retained in
the independent per-record bound, rather than hidden in a random-access unit.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsBounds
open SemiprimeD1BoundaryRecords

/-- Exact-key comparison visits at most the two input key lengths. -/
theorem compare_clock (xs ys : List Bool) :
    (compareKey xs ys).clock≤3*(xs.length+ys.length+1) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compareKey]; omega
  | cons a as ih =>
    cases ys with
    | nil => simp [compareKey]; omega
    | cons b bs =>
      have ht:=ih bs
      cases a <;> cases b <;> simp [compareKey] <;> omega

/-- Paid copies are linear in record count and every actual record byte. -/
theorem copyEntries_clock (es : List Entry) (B : Nat)
    (h : ∀e∈es,size e≤B) :
    (copyEntries es).clock≤4*(B+1)*(es.length+1) := by
  have hs : (es.map (fun e => 3*size e+3)).sum≤(3*B+3)*es.length := by
    induction es with
    | nil => simp
    | cons e es ih =>
      have he:=h e List.mem_cons_self
      have ht:=ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  change (es.map (fun e => 3*size e+3)).sum+1≤_
  nlinarith

/-- The sequential merge report has no quadratic record-count factor. -/
theorem mergeFuel_clock : (fuel : Nat) → (xs ys : List Entry) → (B : Nat) →
    xs.length+ys.length≤fuel →
    (∀e∈xs++ys,size e≤B) →
    (mergeFuel fuel xs ys).clock≤20*(B+1)*(xs.length+ys.length+1)
  | 0,xs,ys,B,hfuel,h => by
    have hx : xs=[] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp [mergeFuel,copyEntries]; omega
  | _+1,[],ys,B,_,h => by
    have hc:=copyEntries_clock ys B (by simpa using h)
    simp only [mergeFuel,List.length_nil,Nat.zero_add]
    nlinarith
  | _+1,xs,[],B,_,h => by
    have hc:=copyEntries_clock xs B (by simpa using h)
    cases xs with
    | nil => simp [mergeFuel,copyEntries]; omega
    | cons x xs =>
      simp only [mergeFuel,List.length_nil,Nat.add_zero]
      nlinarith
  | fuel+1,x::xs,y::ys,B,hfuel,h => by
    have hx:=h x (by simp)
    have hy:=h y (by simp)
    have hkx : x.key.length≤B := by unfold size at hx; omega
    have hky : y.key.length≤B := by unfold size at hy; omega
    have hc:=compare_clock x.key y.key
    rw [mergeFuel]
    split
    · have ht:=mergeFuel_clock fuel (x::xs) ys B
        (by simp only [List.length_cons] at hfuel ⊢; omega)
        (by
          intro e he
          apply h
          rcases List.mem_append.mp he with he | he
          · exact List.mem_append_left _ he
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ he))
      simp only [List.length_cons] at *
      nlinarith
    · have ht:=mergeFuel_clock fuel xs (y::ys) B
        (by simp only [List.length_cons] at hfuel ⊢; omega)
        (by
          intro e he
          apply h
          rcases List.mem_append.mp he with he | he
          · exact List.mem_append_left _ (List.mem_cons_of_mem _ he)
          · exact List.mem_append_right _ he)
      simp only [List.length_cons] at *
      nlinarith

/-- Closed merge uses precisely its actual number of input records as fuel. -/
theorem merge_clock (xs ys : List Entry) (B : Nat)
    (h : ∀e∈xs++ys,size e≤B) :
    (merge xs ys).clock≤20*(B+1)*(xs.length+ys.length+1) :=
  mergeFuel_clock _ _ _ B (by rfl) h

/-- Only the current local address dimension is materialized. -/
theorem assignments_length (n : Nat) : (assignments n).value.length=2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [assignments,ih,pow_succ,Nat.mul_two]

/-- Actual address allocation is linear in catalogue size and address length. -/
theorem assignments_clock (n : Nat) :
    (assignments n).clock≤20*(n+1)*2^n := by
  induction n with
  | zero => simp [assignments]
  | succ n ih =>
    have hp : 1≤2^n := Nat.one_le_two_pow
    simp only [assignments,assignments_length,pow_succ]
    nlinarith

end RiemannGaussian.SemiprimeD1BoundaryRecordsBounds
