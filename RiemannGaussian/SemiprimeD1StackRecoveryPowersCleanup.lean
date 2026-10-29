/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationInput
/-! # Same-source complete35-role physical arithmetic cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersCleanup
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryGridInventory (rationalRole_not_template rationalRole_complete)
/-- Actual whole store cell mass, used solely for proof-side bounds. -/
def mass (data:Stack→List Bool) :Nat:=∑k,(data k).length
/-- Each literal word is charged to the actual existing physical store. -/
theorem word_le_mass (data:Stack→List Bool) (k:Stack) :(data k).length ≤ mass data:=
  Finset.single_le_sum (f:=fun k:Stack=>(data k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Fixed role inventory corresponding to a finite set of already compiled labels. -/
def roles {n:Nat} (slot:Fin n→Stack) :List Stack:=(List.finRange n).map slot
/-- Every finite literal inventory has exactly its compiled cardinality. -/
theorem roles_length {n:Nat} (slot:Fin n→Stack) :(roles slot).length=n:=by simp only [roles,List.length_map,List.length_finRange]
/-- Physical instruction slot and proof inventory position coincide. -/
theorem roles_get {n:Nat} (slot:Fin n→Stack) (i:Fin n) :(roles slot)[i.val]'(by rw [roles_length];exact i.isLt)=slot i:=by
  simp only [roles,List.getElem_map,List.getElem_finRange]
  exact congrArg slot (Fin.ext rfl)
/-- Exact proof-side store after a prefix of actual drain loops. -/
noncomputable def cleared {n:Nat} (slot:Fin n→Stack) (data:Stack→List Bool) (position:Nat) :Stack→List Bool:=by
  classical
  exact fun k=>if k∈(roles slot).take position then [] else data k
/-- Before the first actual drain, no source or cache word changes. -/
theorem cleared_zero {n:Nat} (slot:Fin n→Stack) (data:Stack→List Bool) :cleared slot data 0=data:=by
  funext k;simp [cleared]
/-- Every actual physical drain advances exactly one literal inventory position. -/
theorem cleared_succ {n:Nat} (slot:Fin n→Stack) (data:Stack→List Bool) (i:Fin n) :
    Function.update (cleared slot data i.val) (slot i) []=cleared slot data (i.val+1):=by
  classical
  have hn:i.val<(roles slot).length:=by rw [roles_length];exact i.isLt
  have ht:=List.take_succ_eq_append_getElem hn
  rw [roles_get] at ht
  funext k
  by_cases he:k=slot i
  · subst k
    simp only [Function.update_same,cleared,ht,List.mem_append,List.mem_singleton,or_true,ite_true]
  · rw [Function.update_of_ne he]
    change (if k∈(roles slot).take i.val then [] else data k)=(if k∈(roles slot).take (i.val+1) then [] else data k)
    rw [ht]
    simp only [List.mem_append,List.mem_singleton,he,or_false]
/-- Actual cleanup cannot increase any word's initial physical cell count. -/
theorem cleared_le {n:Nat} (slot:Fin n→Stack) (data:Stack→List Bool) (position:Nat) (k:Stack) :
    (cleared slot data position k).length ≤ mass data:=by
  simp only [cleared]
  split
  · exact Nat.zero_le _
  · exact word_le_mass data k
/-- Fixed compile-time successor of each real finite cleanup label. -/
def next {n:Nat} (pc:Fin n→Label) (stopped:Label) (i:Fin n) :Label:=
  if h:i.val<n-1 then pc ⟨i.val+1,by omega⟩ else stopped
/-- Every nonempty literal inventory is physically drained through its last real EOF branch.
The n/slot/pc arguments occur only in this trace theorem, never as source operands. -/
theorem sweep {n:Nat} (hn:0<n) (slot:Fin n→Stack) (pc:Fin n→Label) (stopped:Label)
    (hc:∀i,program (pc i)=.base (.pop (slot i) (next pc stopped i) (pc i) (pc i)))
    (remaining position:Nat) (hp:position+remaining=n-1) (data:Stack→List Bool) :
    ∃t ≤(remaining+1)*(mass data+1),Runs program t (pc ⟨position,by omega⟩)
      (cleared slot data position) stopped (cleared slot data n):=by
  induction remaining generalizing position with
  | zero=>
    have hpos:position=n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=stopped:=by simp only [next,i,hpos,Nat.lt_irrefl,dite_false]
    have h0:=PTrace.drain_loop (pc i) stopped (slot i) (by rw [hc,hnext])
      (cleared slot data position) ((cleared slot data position) (slot i)) rfl
    have hclear:=cleared_succ slot data i
    change Function.update (cleared slot data position) (slot i) []=cleared slot data (position+1) at hclear
    rw [hclear] at h0
    have he:position+1=n:=by omega
    rw [he] at h0
    refine ⟨_,?_,h0⟩
    have hw:=cleared_le slot data position (slot i)
    omega
  | succ remaining ih=>
    have hpos:position<n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=pc ⟨position+1,by omega⟩:=by simp only [next,i,dite_eq_left hpos]
    have h0:=PTrace.drain_loop (pc i) (pc ⟨position+1,by omega⟩) (slot i) (by rw [hc,hnext])
      (cleared slot data position) ((cleared slot data position) (slot i)) rfl
    have hclear:=cleared_succ slot data i
    change Function.update (cleared slot data position) (slot i) []=cleared slot data (position+1) at hclear
    rw [hclear] at h0
    obtain ⟨t,ht,h1⟩:=ih (position+1) (by omega)
    refine ⟨_,?_,PTrace.join h0 h1⟩
    have hw:=cleared_le slot data position (slot i)
    nlinarith
/-- Every literal role is fully cleared after the finite physical inventory ends. -/
theorem cleared_full {n:Nat} (slot:Fin n→Stack) (data:Stack→List Bool) (k:Stack) :
    cleared slot data n k=(@ite (List Bool) (k∈roles slot) (Classical.propDecidable _) [] (data k)):=by
  classical
  change (if k∈(roles slot).take n then [] else data k)=_
  rw [List.take_of_length_le (by rw [roles_length])]
/-- All35 private roles, including already empty shadows, execute their actual EOF drains. -/
theorem rational_cleanup (data:Stack→List Bool):
    ∃t≤35*(mass data+1),Runs program t (.local (.clearRational 0)) data (.local (.frame true))
      (cleared (fun i:Fin 35=>rational (rationalRole i)) data 35):=by
  have hc:∀i:Fin 35,program (.local (.clearRational i))=.base
      (.pop (rational (rationalRole i)) (next (fun j=>Label.local (.clearRational j)) (.local (.frame true)) i)
        (.local (.clearRational i)) (.local (.clearRational i))):=by intro i;rfl
  obtain ⟨t,ht,hr⟩:=sweep (by decide:0<35) (fun i:Fin 35=>rational (rationalRole i))
    (fun i=>Label.local (.clearRational i)) (.local (.frame true)) hc 34 0 rfl data
  refine ⟨t,by omega,?_⟩
  simpa only [cleared_zero,show (⟨0,by decide⟩:Fin 35)=0 from Fin.ext rfl] using hr
/-- The literal35-role image is exactly the real rational bank except the actual retained width tape. -/
theorem rational_mem_iff (k:R.Stack) :rational k∈roles (fun i:Fin 35=>rational (rationalRole i)) ↔
    k≠SemiprimeD1StackRationalOperation.aux .template:=by
  constructor
  · intro h hk
    obtain ⟨i,_,he⟩:=List.mem_map.mp h
    exact rationalRole_not_template i ((Sum.inl_injective he).trans hk)
  · intro hk
    obtain ⟨i,hi⟩:=rationalRole_complete k hk
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,congrArg rational hi⟩
/-- Whole35-role actual cleanup preserves W and every68 other physical word, including the full chronological slope tail. -/
theorem rational_cleared (w:Words) :
    cleared (fun i:Fin 35=>rational (rationalRole i)) (bank w) 35=
      bank {w with rational:=fun k=>if k=SemiprimeD1StackRationalOperation.aux .template then w.rational k else []}:=by
  classical
  funext k
  rw [cleared_full]
  rcases k with k|k
  · change (if rational k∈roles (fun i:Fin 35=>rational (rationalRole i)) then [] else w.rational k)=_
    rw [rational_mem_iff]
    by_cases he:k=SemiprimeD1StackRationalOperation.aux .template
    · simp only [he,ne_eq,not_true_eq_false,ite_false,bank,Sum.elim_inl,ite_true]
    · simp only [he,ne_eq,not_false_eq_true,ite_true,bank,Sum.elim_inl,ite_false]
  · have hn:(Sum.inr k:Stack)∉roles (fun i:Fin 35=>rational (rationalRole i)):=by
      intro h
      obtain ⟨i,_,he⟩:=List.mem_map.mp h
      cases he
    rw [ite_eq_right hn]
    rfl
end RiemannGaussian.SemiprimeD1StackRecoveryPowersCleanup
