/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsPrimitives
/-! # Complete physical cleanup protects source heap/counter and persistent root header -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanup
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackProcedureTrace
namespace Inv
export SemiprimeD1StackRootPhaseFreshRecordsInventory (clearRoles clearRoles_length clearRoles_mem)
end Inv
/-- Actual145 drain addresses:140 mapped logical words, three RAW alias-shadows,
currentrecord and newissuedreference. Sourceheap/counter/header are protected. -/
def roles :List Stack :=Inv.clearRoles.map cacheStack++
  [cachePrivate I.sourceHeap,cachePrivate I.sourceCounter,cachePrivate I.sourceReference,aux .record,aux .reference]
/-- Exactly145 physically executed EOF checks and complete byte drains. -/
theorem roles_length :roles.length=145 :=by
  simp only [roles,List.length_append,List.length_map,Inv.clearRoles_length]
  rfl
/-- Fixed literal code position selects exactly the declared physical cleanup address. -/
theorem roles_get (i:Fin 145) :roles[i.val]=clearStack i :=by
  by_cases h:i.val<140
  · change (Inv.clearRoles.map cacheStack++[cachePrivate I.sourceHeap,cachePrivate I.sourceCounter,cachePrivate I.sourceReference,aux .record,aux .reference])[i.val]=_
    rw [List.getElem_append_left (by simpa only [List.length_map,Inv.clearRoles_length] using h),List.getElem_map]
    simp only [clearStack,h,dite_eq_left]
    rfl
  · have hi:140 ≤ i.val:=by omega
    have hm:i.val=140 ∨ i.val=141 ∨ i.val=142 ∨ i.val=143 ∨ i.val=144:=by omega
    rcases hm with he|he|he|he|he
    all_goals
      rcases i with ⟨n,hn⟩
      dsimp only [Fin.val_mk] at he
      subst n
      rfl
/-- Non-aliased logical client words use their actual private physical addresses. -/
theorem cache_private (k:Q.Stack) (hh:k≠I.sourceHeap) (hc:k≠I.sourceCounter) (hr:k≠I.sourceReference) :
    cacheStack k=cachePrivate k :=by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> first | rfl | exact (hh rfl).elim | exact (hc rfl).elim | exact (hr rfl).elim
  · rfl
/-- None of the three RAW aliases is an actual included-client operand. -/
theorem no_raw_alias (k:Q.Stack) :
    cacheStack k≠cachePrivate I.sourceHeap ∧ cacheStack k≠cachePrivate I.sourceCounter ∧
      cacheStack k≠cachePrivate I.sourceReference :=by
  rcases k with k|k
  · rcases k with k|k
    · refine ⟨?_,?_,?_⟩
      all_goals intro he;cases he
    · cases k <;> decide
  · refine ⟨?_,?_,?_⟩
    all_goals intro he;cases he
/-- No actual client operand aliases the NEW record or NEW issued reference. -/
theorem no_new_local (k:Q.Stack) :cacheStack k≠aux .record ∧ cacheStack k≠aux .reference :=by
  rcases k with k|k
  · rcases k with k|k
    · constructor
      all_goals intro he;cases he
    · cases k <;> decide
  · constructor
    all_goals intro he;cases he
/-- Mapped logical cleanup touches EXACTLY the140 allowed client operands. -/
theorem mapped_mem (k:Q.Stack) :cacheStack k∈roles ↔ k∈Inv.clearRoles :=by
  have h0:=no_raw_alias k
  have h1:=no_new_local k
  simp only [roles,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · intro h
    rcases h with ⟨j,hj,he⟩|h
    · have heq:j=k:=cache_injective he
      simpa only [heq] using hj
    · rcases h with h|h|h|h|h
      · exact (h0.1 h).elim
      · exact (h0.2.1 h).elim
      · exact (h0.2.2 h).elim
      · exact (h1.1 h).elim
      · exact (h1.2 h).elim
  · intro h
    exact Or.inl ⟨k,h,rfl⟩
/-- Every raw private client word is cleared EXCEPT the persistent root old-axis header. -/
theorem private_mem (k:Q.Stack) :cachePrivate k∈roles ↔ k≠I.oldHeader :=by
  by_cases hh:k=I.sourceHeap
  · subst k
    constructor
    · intro _;decide
    · intro _
      exact List.mem_append_right _ (by simp only [List.mem_cons_self])
  · by_cases hc:k=I.sourceCounter
    · subst k
      constructor
      · intro _;decide
      · intro _
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · by_cases hr:k=I.sourceReference
      · subst k
        constructor
        · intro _;decide
        · intro _
          exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · rw [←cache_private k hh hc hr,mapped_mem,Inv.clearRoles_mem]
        exact ⟨fun h=>h.2.2,fun h=>⟨hh,hc,h⟩⟩
/-- No actual original188 source field is a cleanup target, including its immutable heap/counter. -/
theorem root_not_mem (k:R.Stack) :rootStack k∉roles :=by
  intro h
  rcases List.mem_append.mp h with h|h
  · obtain ⟨j,hj,he⟩:=List.mem_map.mp h
    have hp: j≠I.sourceHeap ∧ j≠I.sourceCounter ∧ j≠I.oldHeader:=Inv.clearRoles_mem j |>.mp hj
    rcases j with j|j
    · rcases j with j|j
      · cases he
      · cases j <;> first | exact (hp.1 rfl).elim | exact (hp.2.1 rfl).elim | cases he
    · cases he
  · simp [cachePrivate,aux,rootStack] at h
/-- Exactly pointer/currentrecord/newreference are cleared among caller's auxiliary words. -/
theorem aux_mem (k:Aux) :aux k∈roles ↔ k=.pointer ∨ k=.record ∨ k=.reference :=by
  have hlogical:(∃q,q∈Inv.clearRoles ∧ cacheStack q=aux k) ↔ k=.pointer:=by
    constructor
    · rintro ⟨q,_,he⟩
      rcases q with q|q
      · rcases q with q|q
        · cases he
        · cases q <;> first | exact (Sum.inr.inj (Sum.inr.inj he)).symm | cases he
      · cases he
    · intro he
      subst k
      exact ⟨I.sourceReference,(Inv.clearRoles_mem _).mpr (by decide),rfl⟩
  simp only [roles,List.mem_append,List.mem_map,hlogical,List.mem_cons,List.not_mem_nil,or_false]
  simp [aux,cachePrivate]
/-- Total actual345-word data mass, including all retained source heaps and shadows. -/
def mass (bank:Stack→List Bool) :Nat :=∑k,(bank k).length
/-- Every word is charged to the complete physical data inventory. -/
theorem word_le_mass (bank:Stack→List Bool) (k:Stack) :(bank k).length ≤ mass bank :=
  Finset.single_le_sum (f:=fun k:Stack=>(bank k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Mathematical prefix state of the ACTUAL finite complete-drain loop. -/
noncomputable def cleared (bank:Stack→List Bool) (n:Nat) :Stack→List Bool :=by
  classical
  exact fun k=>if k∈roles.take n then [] else bank k
/-- No physical word has changed before the first real drain. -/
theorem cleared_zero (bank:Stack→List Bool) :cleared bank 0=bank :=by funext k;simp [cleared]
/-- Each real drain advances exactly its finite literal address prefix. -/
theorem cleared_succ (bank:Stack→List Bool) (i:Fin 145) :
    Function.update (cleared bank i.val) (clearStack i) []=cleared bank (i.val+1) :=by
  classical
  have hn:i.val<roles.length:=by simpa only [roles_length] using i.isLt
  have ht:=List.take_succ_eq_append_getElem hn
  rw [roles_get] at ht
  funext k
  by_cases he:k=clearStack i
  · subst k
    simp only [Function.update_same,cleared,ht,List.mem_append,List.mem_singleton,or_true,ite_true]
  · rw [Function.update_of_ne he]
    change (if k∈roles.take i.val then [] else bank k)=(if k∈roles.take (i.val+1) then [] else bank k)
    rw [ht]
    simp only [List.mem_append,List.mem_singleton,he,or_false]
/-- Physical cleanup never increases any actual word. -/
theorem cleared_le (bank:Stack→List Bool) (n:Nat) (k:Stack) :((cleared bank n) k).length ≤ mass bank :=by
  simp only [cleared]
  split
  · exact Nat.zero_le _
  · exact word_le_mass bank k
/-- Every byte, every empty alias-shadow EOF and the final jump are paid by this SAME program. -/
theorem sweep (remaining position:Nat) (hp:position+remaining=145) (bank:Stack→List Bool) :
    ∃t ≤ remaining*(mass bank+1)+1,
      Runs program t (.clear ⟨position,by omega⟩) (cleared bank position) .header (cleared bank 145) :=by
  induction remaining generalizing position with
  | zero=>
    have he:position=145:=by omega
    subst position
    exact ⟨1,by omega,cleanup_end (cleared bank 145)⟩
  | succ remaining ih=>
    have hn:position<145:=by omega
    have h0:=clear_call ⟨position,by omega⟩ hn (cleared bank position)
    rw [cleared_succ bank ⟨position,hn⟩] at h0
    obtain ⟨t,ht,h1⟩:=ih (position+1) (by omega)
    refine ⟨((cleared bank position) (clearStack ⟨position,hn⟩)).length+1+t,?_,compose h0 h1⟩
    have hw:=cleared_le bank position (clearStack ⟨position,hn⟩)
    nlinarith
/-- Complete prepared cleanup trace; exact protected-field equations are given by membership lemmas above. -/
theorem cleanup_run (bank:Stack→List Bool) :
    ∃t ≤ 145*(mass bank+1)+1,Runs program t (.clear 0) bank .header (cleared bank 145) :=by
  have hz:(⟨0,by omega⟩:Fin 146)=0:=Fin.ext rfl
  simpa only [hz,cleared_zero] using sweep 145 0 rfl bank
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCleanup
