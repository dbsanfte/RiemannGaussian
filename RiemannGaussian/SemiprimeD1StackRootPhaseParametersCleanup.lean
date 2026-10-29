/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersPrimitives
/-! # Literal complete private-bank drains between chronological phase allocations -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersCleanup
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackProcedureTrace
/-- All actual phase roles plus the three restored row-local payloads. -/
def clearRoles : List Stack :=I.roles.map phaseStack++[aux .index,aux .record,aux .reference]
/-- Exactly fifty-one physical EOF-checked drain sites. -/
theorem clearRoles_length : clearRoles.length=51 :=by simp only [clearRoles,List.length_append,List.length_map,SemiprimeD1StackRootPhaseParametersInventory.roles_length];rfl
/-- The fixed cleanup instruction's role is exactly its inventory position. -/
theorem clearRoles_get (i:Fin 51) : clearRoles[i.val]=clearStack i :=by fin_cases i <;> rfl
/-- Full actual data-cell mass, including all retained root and heap words. -/
def mass (bank:Stack→List Bool) : Nat :=∑k,(bank k).length
/-- An actual private word is charged to the full physical data mass. -/
theorem word_le_mass (bank:Stack→List Bool) (k:Stack) : (bank k).length≤ mass bank :=
  Finset.single_le_sum (f:=fun k:Stack=>(bank k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Proof-side state after a literal finite prefix of actual private drain loops. -/
noncomputable def cleared (bank:Stack→List Bool) (n:Nat) : Stack→List Bool :=by
  classical
  exact fun k=>if k∈clearRoles.take n then [] else bank k
/-- Before the first actual drain, no payload has changed. -/
theorem cleared_zero (bank:Stack→List Bool) : cleared bank 0=bank :=by funext k;simp [cleared]
/-- Each physical EOF-checked drain advances precisely one fixed inventory position. -/
theorem cleared_succ (bank:Stack→List Bool) (i:Fin 51) :
    Function.update (cleared bank i.val) (clearStack i) []=cleared bank (i.val+1) :=by
  classical
  have hn:i.val<clearRoles.length:=by simpa only [clearRoles_length] using i.isLt
  have ht:=List.take_succ_eq_append_getElem hn
  rw [clearRoles_get] at ht
  funext k
  by_cases he:k=clearStack i
  · subst k
    simp only [Function.update_same,cleared,ht,List.mem_append,List.mem_singleton,or_true,ite_true]
  · rw [Function.update_of_ne he]
    change (if k∈clearRoles.take i.val then [] else bank k)=(if k∈clearRoles.take (i.val+1) then [] else bank k)
    rw [ht]
    simp only [List.mem_append,List.mem_singleton,he,or_false]
/-- Physical clearing cannot increase any retained or private word. -/
theorem cleared_le (bank:Stack→List Bool) (n:Nat) (k:Stack) : ((cleared bank n) k).length≤ mass bank :=by
  simp only [cleared]
  split
  · exact Nat.zero_le _
  · exact word_le_mass bank k
/-- After the fixed inventory length, membership is in the whole physical drain list. -/
theorem cleared_full (bank:Stack→List Bool) (k:Stack) :
    cleared bank 51 k=(@ite (List Bool) (k∈clearRoles) (Classical.propDecidable _) [] (bank k)) :=by
  classical
  change (if k∈clearRoles.take 51 then [] else bank k)=_
  rw [List.take_of_length_le (show clearRoles.length≤51 by rw [clearRoles_length])]
/-- Only the three named row-local auxiliary words are physically drained. -/
theorem aux_mem_iff (k:Aux) : aux k∈clearRoles ↔ k=.index ∨ k=.record ∨ k=.reference :=by
  simp [clearRoles,phaseStack,aux]
/-- Actual cleanup preserves all126 root cells, heap/counter/reference-history,
reader suffix and output while clearing every phase field and row-local payload. -/
theorem cleared_all (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output:List Bool) :
    cleared (view root phase reader index record heap counter reference history output) 51=
      view root (fun _=>[]) reader [] [] heap counter [] history output :=by
  classical
  funext k
  rw [cleared_full]
  rcases k with k|k
  · have hn:(Sum.inl k:Stack)∉clearRoles:=by
      intro h
      rcases List.mem_append.mp h with h|h
      · obtain ⟨p,_,he⟩:=List.mem_map.mp h
        cases he
      · simp [aux] at h
    rw [ite_eq_right hn]
    rfl
  · rcases k with k|k
    · have hm:(phaseStack k)∈clearRoles:=
        List.mem_append_left _ (List.mem_map.mpr ⟨k,SemiprimeD1StackRootPhaseParametersInventory.roles_complete k,rfl⟩)
      change (if phaseStack k∈clearRoles then [] else _)=[]
      rw [ite_eq_left hm]
    · change (if aux k∈clearRoles then [] else work reader index record heap counter reference history output k)=_
      simp only [aux_mem_iff]
      cases k <;> simp [view,data,work]
/-- Every actual word byte and every empty-field EOF is paid by this same program. -/
theorem sweep (remaining position:Nat) (hp:position+remaining=51) (bank:Stack→List Bool) :
    ∃t≤remaining*(mass bank+1)+1,Runs program t (.clear ⟨position,by omega⟩) (cleared bank position)
      .header (cleared bank 51) :=by
  induction remaining generalizing position with
  | zero=>
    have he:position=51:=by omega
    subst position
    refine ⟨1,by omega,?_⟩
    exact cleanup_end (cleared bank 51)
  | succ remaining ih=>
    have hlt:position<51:=by omega
    let i:Fin 52:=⟨position,by omega⟩
    have h0:=clear_call i hlt (cleared bank position)
    have hs:=cleared_succ bank ⟨position,hlt⟩
    rw [hs] at h0
    obtain ⟨t,ht,h1⟩:=ih (position+1) (by omega)
    refine ⟨((cleared bank position) (clearStack ⟨position,hlt⟩)).length+1+t,?_,compose h0 h1⟩
    have hw:=cleared_le bank position (clearStack ⟨position,hlt⟩)
    nlinarith
/-- Complete literal private cleanup preserves the exact source and accumulated heap/order. -/
theorem cleanup_run (root:G.Stack→List Bool) (phase:P.Stack→List Bool)
    (reader index record heap counter reference history output:List Bool) :
    ∃t≤51*(mass (view root phase reader index record heap counter reference history output)+1)+1,
      Runs program t (.clear 0) (view root phase reader index record heap counter reference history output)
        .header (view root (fun _=>[]) reader [] [] heap counter [] history output) :=by
  have hz:(⟨0,by omega⟩:Fin 52)=0:=Fin.ext rfl
  simpa only [cleared_zero,cleared_all,hz] using
    sweep 51 0 rfl (view root phase reader index record heap counter reference history output)
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersCleanup
