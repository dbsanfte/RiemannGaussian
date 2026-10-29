/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsBounds

/-! # Linear request-join work with explicit full-jet arithmetic budgets -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsLookupBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsBounds
open SemiprimeD1JetAxes (Context)

/-- One coefficient word cannot exceed the full payload byte count. -/
theorem member_word_le (ws : List (List Bool)) (w : List Bool) (hw : w∈ws) :
    w.length≤(ws.map List.length).sum := by
  induction ws with
  | nil => simp at hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · simp
    · have ht:=ih hw
      simp only [List.map_cons,List.sum_cons]
      omega

/-- A whole-record bound includes all scalar word bytes. -/
theorem word_bound (e : Entry) (B : Nat) (h : size e≤B) :
    ∀w∈e.words,w.length≤B := by
  intro w hw
  have hs:=member_word_le e.words w hw
  unfold size at h
  omega

/-- Packed requests hide no coefficient payload in the metadata head word. -/
theorem request_word_bound (e : Entry) (B : Nat) (h : size e≤B) :
    ∀w∈(Request.unpack e).words,w.length≤B := by
  intro w hw
  exact word_bound e B h w (List.mem_of_mem_tail hw)

/-- Actual full-jet multiplication cost, including every axis traversal. -/
def arithmeticBudget (ctx : Context) (B : Nat) : Nat :=
  SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank B ctx.precision

/-- A single request multiplication is bounded from its actual bytes and shape. -/
theorem product_clock (ctx : Context) (r t : Entry) (B : Nat)
    (hr : size r≤B) (ht : size t≤B)
    (hnr : (Request.unpack r).words.length≤ctx.rank) (hnt : t.words.length≤ctx.rank) :
    (SemiprimeD1JetRingBits.mul ctx (Request.unpack r).words t.words).clock≤arithmeticBudget ctx B :=
  SemiprimeD1JetRingBounds.mul_clock ctx _ _ B hnr hnt
    (request_word_bound r B hr) (word_bound t B ht)

/-- Missing-table multiplication uses the real empty zero vector. -/
theorem zero_clock (ctx : Context) (r : Entry) (B : Nat)
    (hr : size r≤B) (hnr : (Request.unpack r).words.length≤ctx.rank) :
    (SemiprimeD1JetRingBits.mul ctx (Request.unpack r).words []).clock≤arithmeticBudget ctx B :=
  SemiprimeD1JetRingBounds.mul_clock ctx _ _ B hnr (by simp)
    (request_word_bound r B hr) (by simp)

/-- Per-record join allowance contains independent context/arithmetic metadata. -/
def joinBudget (ctx : Context) (B : Nat) : Nat := arithmeticBudget ctx B+20*(B+1)

/-- A forward join is linear in request plus table record count. Context and
payload parameters occur only in the separate per-record allowance. -/
theorem lookupFuel_clock (ctx : Context) :
    (fuel : Nat) → (rs ts : List Entry) → (B : Nat) →
    rs.length+ts.length≤fuel →
    (∀e∈rs,size e≤B) → (∀e∈ts,size e≤B) →
    (∀e∈rs,(Request.unpack e).words.length≤ctx.rank) →
    (∀e∈ts,e.words.length≤ctx.rank) →
    (lookupFuel ctx fuel rs ts).clock≤joinBudget ctx B*(rs.length+ts.length+1)
  | 0,rs,ts,B,hfuel,_,_,_,_ => by
    have hr : rs=[] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : ts=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst rs; subst ts
    simp [lookupFuel,joinBudget]; omega
  | _+1,[],ts,B,_,_,_,_,_ => by
    simp only [lookupFuel,List.length_nil,Nat.zero_add]
    unfold joinBudget
    nlinarith
  | fuel+1,r::rs,[],B,hfuel,hr,ht,hnr,hnt => by
    have hzero:=zero_clock ctx r B (hr r List.mem_cons_self) (hnr r List.mem_cons_self)
    have tail:=lookupFuel_clock ctx fuel rs [] B
      (by simp only [List.length_cons,List.length_nil,Nat.add_zero] at hfuel ⊢;omega)
      (fun e he => hr e (List.mem_cons_of_mem _ he)) ht
      (fun e he => hnr e (List.mem_cons_of_mem _ he)) hnt
    have hsize:=hr r List.mem_cons_self
    simp only [List.length_nil,Nat.add_zero] at tail
    simp only [lookupFuel,List.length_cons,List.length_nil,Nat.add_zero]
    unfold joinBudget at tail ⊢
    nlinarith
  | fuel+1,r::rs,t::ts,B,hfuel,hr,ht,hnr,hnt => by
    have hsizeR:=hr r List.mem_cons_self
    have hsizeT:=ht t List.mem_cons_self
    have hkr : r.key.length≤B := by unfold size at hsizeR;omega
    have hkt : t.key.length≤B := by unfold size at hsizeT;omega
    have cmp:=compare_clock r.key t.key
    have headZero:=zero_clock ctx r B hsizeR (hnr r List.mem_cons_self)
    have headProduct:=product_clock ctx r t B hsizeR hsizeT
      (hnr r List.mem_cons_self) (hnt t List.mem_cons_self)
    have dropRequest:=lookupFuel_clock ctx fuel rs (t::ts) B
      (by simp only [List.length_cons] at hfuel ⊢;omega)
      (fun e he => hr e (List.mem_cons_of_mem _ he)) ht
      (fun e he => hnr e (List.mem_cons_of_mem _ he)) hnt
    have dropTable:=lookupFuel_clock ctx fuel (r::rs) ts B
      (by simp only [List.length_cons] at hfuel ⊢;omega)
      hr (fun e he => ht e (List.mem_cons_of_mem _ he))
      hnr (fun e he => hnt e (List.mem_cons_of_mem _ he))
    rw [lookupFuel]
    cases ho : (compareKey r.key t.key).value <;>
      simp only [List.length_cons] at dropRequest dropTable ⊢ <;>
      unfold joinBudget at dropRequest dropTable ⊢ <;> nlinarith

end RiemannGaussian.SemiprimeD1BoundaryRecordsLookupBounds
