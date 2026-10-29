/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsContractBounds
import RiemannGaussian.SemiprimeD1BoundaryRecordsLookupBounds

/-! # Executed two-sort boundary attachment -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsAttachBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsCanonical
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1BoundaryRecordsContractBounds
open SemiprimeD1BoundaryRecordsLookupBounds
open SemiprimeD1JetAxes (Context)

/-- Complete request bytes include both route and projected lookup address. -/
def requestBudget (ctx : Context) (K T : Nat) : Nat := recordBudget ctx K+T+1

theorem requests_properties (ctx : Context) (source target : List Nat) (K : Nat)
    (es : List Entry) (hg : GoodEntries ctx es) (hk : Keys K es) :
    ∀ e∈(requests source target es).value,
      size e≤requestBudget ctx K target.length ∧
      (Request.unpack e).words.length≤ctx.rank ∧ (Request.unpack e).route.length≤K := by
  induction es with
  | nil => simp [requests]
  | cons e es ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hs:=size_le ctx K e (hg e List.mem_cons_self) (hk e List.mem_cons_self)
      have hn:=(hg e List.mem_cons_self).1
      have hkey:=hk e List.mem_cons_self
      have hp:=project_length e.key source target
      simp only [Request.pack,Request.unpack,List.tail_cons,List.headD_cons]
      constructor
      · unfold size requestBudget recordBudget at *
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · exact ⟨hn.le,hkey⟩
    · exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))
        (fun x hx => hk x (List.mem_cons_of_mem _ hx)) x hx

theorem requests_clock (ctx : Context) (source target : List Nat) (K : Nat)
    (es : List Entry) (hg : GoodEntries ctx es) (hk : Keys K es) :
    (requests source target es).clock ≤
      (projectBudget source target K+3*recordBudget ctx K+8)*(es.length+1) := by
  induction es with
  | nil => simp only [requests,List.length_nil,Nat.zero_add,Nat.mul_one]; omega
  | cons e es ih =>
    have ht:=ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))
      (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    have hp:=project_clock e.key source target K (hk e List.mem_cons_self)
    have hs:=size_le ctx K e (hg e List.mem_cons_self) (hk e List.mem_cons_self)
    simp only [requests,List.length_cons]
    nlinarith

/-- Joined keys are the original request routes, including missing-table zero. -/
theorem lookupFuel_keys (ctx : Context) :
    (fuel : Nat) → (rs ts : List Entry) → (K : Nat) → rs.length+ts.length≤fuel →
    (∀e∈rs,(Request.unpack e).route.length≤K) → Keys K (lookupFuel ctx fuel rs ts).value
  | 0,rs,ts,K,h,_ => by
    have hr : rs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst rs
    simp [lookupFuel,Keys]
  | _+1,[],_,_,_,_ => by simp [lookupFuel,Keys]
  | fuel+1,r::rs,[],K,h,hk => by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hk r List.mem_cons_self
    · exact lookupFuel_keys ctx fuel rs [] K (by simp only [List.length_cons,List.length_nil,Nat.add_zero] at h ⊢;omega)
        (fun e he => hk e (List.mem_cons_of_mem _ he)) e he
  | fuel+1,r::rs,t::ts,K,h,hk => by
    rw [lookupFuel]
    cases ho : (compareKey r.key t.key).value
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hk r List.mem_cons_self
      · exact lookupFuel_keys ctx fuel rs (t::ts) K
          (by simp only [List.length_cons] at h ⊢;omega)
          (fun e he => hk e (List.mem_cons_of_mem _ he)) e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hk r List.mem_cons_self
      · exact lookupFuel_keys ctx fuel rs (t::ts) K
          (by simp only [List.length_cons] at h ⊢;omega)
          (fun e he => hk e (List.mem_cons_of_mem _ he)) e he
    · exact lookupFuel_keys ctx fuel (r::rs) ts K
        (by simp only [List.length_cons] at h ⊢;omega) hk

/-- Per-record allowance for both real sorts and full arithmetic join. -/
def attachBudget (ctx : Context) (source target : List Nat) (K B W : Nat) : Nat :=
  projectBudget source target K+3*recordBudget ctx K+8+
    200*(requestBudget ctx K target.length+1)*(W+3)+
    joinBudget ctx (requestBudget ctx K target.length+B)+
    200*(recordBudget ctx K+1)*(W+3)+7

/-- Attachment is linear in accumulator plus literal-table count; the separate
factor pays full jet arithmetic, identifier widths and the two logarithmic sorts. -/
theorem attach_clock_pow (ctx : Context) (source target : List Nat) (K B W : Nat)
    (acc table : List Entry) (hg : GoodEntries ctx acc) (hk : Keys K acc)
    (hb : ∀e∈table,size e≤B) (ht : ∀e∈table,e.words.length≤ctx.rank)
    (hn : acc.length≤2^W) :
    (attach ctx source target acc table).clock ≤
      attachBudget ctx source target K B W*(2^W+table.length+1) := by
  let rs:=(requests source target acc).value
  let ordered:=(sort rs).value
  let joined:=lookupFuel ctx (ordered.length+table.length+1) ordered table
  have hp:=requests_properties ctx source target K acc hg hk
  have ho : ∀e∈ordered,size e≤requestBudget ctx K target.length ∧
      (Request.unpack e).words.length≤ctx.rank ∧ (Request.unpack e).route.length≤K := by
    intro e he
    exact hp e ((SemiprimeD1BoundaryRecordsSort.sort_perm rs).mem_iff.mp he)
  have hrl : rs.length=acc.length := requests_length source target acc
  have hol : ordered.length=acc.length := (SemiprimeD1BoundaryRecordsSort.sort_length rs).trans hrl
  have hjl : joined.value.length=acc.length := (lookupFuel_length ctx _ _ _ (by omega)).trans hol
  have hreq:=requests_clock ctx source target K acc hg hk
  have hsort:=SemiprimeD1BoundaryRecordsSortBounds.sort_clock_pow rs
    (requestBudget ctx K target.length) W (fun e he => (hp e he).1) (by rw [hrl]; exact hn)
  have hjoin:=lookupFuel_clock ctx (ordered.length+table.length+1) ordered table
    (requestBudget ctx K target.length+B) (by omega)
    (fun e he => (ho e he).1.trans (Nat.le_add_right _ _))
    (fun e he => (hb e he).trans (Nat.le_add_left _ _))
    (fun e he => (ho e he).2.1) ht
  have hjg:=lookupFuel_good ctx (ordered.length+table.length+1) ordered table (by omega)
  have hjk:=lookupFuel_keys ctx (ordered.length+table.length+1) ordered table K (by omega)
    (fun e he => (ho e he).2.2)
  have hrestore:=SemiprimeD1BoundaryRecordsSortBounds.sort_clock_pow joined.value
    (recordBudget ctx K) W (fun e he => size_le ctx K e (hjg e he) (hjk e he))
    (by rw [hjl]; exact hn)
  have hreq':=hreq.trans (Nat.mul_le_mul_left _ (by omega : acc.length+1≤2^W+table.length+1))
  have hs' : (sort rs).clock ≤
      (200*(requestBudget ctx K target.length+1)*(W+3))*(2^W+table.length+1) := by
    apply hsort.trans
    calc
      _ = (200*(requestBudget ctx K target.length+1)*(W+3))*(2^W+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hj':=hjoin.trans (Nat.mul_le_mul_left _ (by omega : ordered.length+table.length+1≤2^W+table.length+1))
  have hr' : (sort joined.value).clock ≤
      (200*(recordBudget ctx K+1)*(W+3))*(2^W+table.length+1) := by
    apply hrestore.trans
    calc
      _ = (200*(recordBudget ctx K+1)*(W+3))*(2^W+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  change (requests source target acc).clock+(sort rs).clock+joined.clock+(sort joined.value).clock+7≤_
  unfold attachBudget
  nlinarith only [hreq',hs',hj',hr',Nat.zero_le (2^W),Nat.zero_le table.length]

end RiemannGaussian.SemiprimeD1BoundaryRecordsAttachBounds
