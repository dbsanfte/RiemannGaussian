/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankCleanup
/-! # Physical mismatch/EOF rejection and complete actual work cleanup
The real abort path drains every nonpersistent callee word and all six outer
work words. Original heap/counter/reference/child banks survive. Only afterward
is the now-empty actual scratch given singleton false status.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankAbort
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackCachePhaseBankClearEncoding
open SemiprimeD1StackProcedureTrace
/-- Real outer work port at each of six fixed abort labels. -/
def auxRole (i:Fin 6):Aux:=
  if i=0 then .referenceReader else if i=1 then .childReader else if i=2 then .valid
  else if i=3 then .history else if i=4 then .buffer else .output
/-- Exact partial view of physically drained outer work, with both original vectors retained. -/
def auxThrough (w:Aux→List Bool) (n:Nat):Aux→List Bool
  | .references=>w .references | .children=>w .children
  | .referenceReader=>if 0<n then [] else w .referenceReader
  | .childReader=>if 1<n then [] else w .childReader
  | .valid=>if 2<n then [] else w .valid
  | .history=>if 3<n then [] else w .history
  | .buffer=>if 4<n then [] else w .buffer
  | .output=>if 5<n then [] else w .output
/-- No actual outer word is changed before its sweep starts. -/
theorem aux_zero (w:Aux→List Bool):auxThrough w 0=w:=by funext k;cases k <;> rfl
/-- Every finite outer cleanup label refers to its real physical tape. -/
theorem aux_address (i:Fin 6):abortWord i=aux (auxRole i):=by fin_cases i <;> rfl
/-- Earlier abort drains do not silently modify a future physical work word. -/
theorem aux_current (w:Aux→List Bool) (i:Fin 6):auxThrough w i.val (auxRole i)=w (auxRole i):=by fin_cases i <;> rfl
/-- Exactly one physical drain advances each outer-work partial view. -/
theorem aux_step (w:Aux→List Bool) (i:Fin 6):
    Function.update (auxThrough w i.val) (auxRole i) []=auxThrough w (i.val+1):=by
  funext k;fin_cases i <;> cases k <;> rfl
/-- Actual physical one-port abort drain, including the final empty pop and genuine caller frames. -/
theorem part_run (bank:P.Stack→List Bool) (w:Aux→List Bool) (i:Fin 6):
    Runs program ((w (auxRole i)).length+1) (.local (.abortAux i)) (data bank (auxThrough w i.val))
      (nextAbort i) (data bank (auxThrough w (i.val+1))):=by
  have h0:=drain_loop (.abortAux i) (nextAbort i) (abortWord i) rfl
    (data bank (auxThrough w i.val)) (w (auxRole i)) (by rw [aux_address,data_aux,aux_current])
  rw [aux_address,←data_update_aux,aux_step] at h0
  exact h0
/-- Actual sum of the six physical outer work payloads. -/
def auxMass (w:Aux→List Bool):Nat:=
  (w .referenceReader).length+(w .childReader).length+(w .valid).length+
    (w .history).length+(w .buffer).length+(w .output).length
/-- Complete six-word outer cleanup, retaining both original vectors literally. -/
theorem aux_run (bank:P.Stack→List Bool) (w:Aux→List Bool):
    Runs program (auxMass w+6) (.local (.abortAux 0)) (data bank w) (.local .reject) (data bank (auxThrough w 6)):=by
  have h0:=part_run bank w 0
  simp only [Fin.val_zero,Nat.zero_add,aux_zero] at h0
  have h1:=part_run bank w 1
  have h2:=part_run bank w 2
  have h3:=part_run bank w 3
  have h4:=part_run bank w 4
  have h5:=part_run bank w 5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  have ht:auxMass w+6=(((w .referenceReader).length+1+((w .childReader).length+1)+
      ((w .valid).length+1))+((w .history).length+1))+((w .buffer).length+1)+((w .output).length+1):=by
    unfold auxMass
    omega
  rw [ht]
  exact h
/-- Exact rejected source bank after all actual work drains; original four operands are retained. -/
def rejectedData (bank:P.Stack→List Bool) (w:Aux→List Bool):Stack→List Bool:=
  Function.update (data (cleared bank) (auxThrough w 6)) status [false]
/-- Real rejection time through complete236+6 cleanup, final false push and physical halt. -/
def abortTime (bank:P.Stack→List Bool) (w:Aux→List Bool):Nat:=1+sweepTime bank 0+(auxMass w+6)+1+1
/-- Once a real parser/tag/EOF mismatch enters abort, actual cleanup guarantees false status and no partial output. -/
theorem abort_trace (bank:P.Stack→List Bool) (w:Aux→List Bool):
    Runs program (abortTime bank w-1) (.local .abort) (data bank w) (.local .done) (rejectedData bank w):=by
  have h0:=jump_run .abort (.local (.clear true 0)) (data bank w) rfl
  have h1:=SemiprimeD1StackCachePhaseBankCleanup.source_run true bank w
  have h2:=aux_run (cleared bank) w
  have h3:=push_run .reject (.local .done) status false (data (cleared bank) (auxThrough w 6)) rfl
  change Runs program 1 _ _ _ (Function.update (data (cleared bank) (auxThrough w 6)) status (false::cleared bank P.copyScratch)) at h3
  rw [cleared_scratch] at h3
  have h:=join (join (join h0 h1) h2) h3
  have ht:abortTime bank w-1=1+sweepTime bank 0+(auxMass w+6)+1:=by unfold abortTime;omega
  rw [ht]
  exact h
/-- Rejection emits no partial phase bank, only a real singleton false status word. -/
theorem rejected_output (bank:P.Stack→List Bool) (w:Aux→List Bool):
    rejectedData bank w output=[] ∧ rejectedData bank w status=[false]:=by
  constructor
  · rfl
  · simp only [rejectedData,Function.update_self]
/-- Actual rejected halt clears both transient flags and all real returns after the physical work sweep. -/
theorem abort_run (bank:P.Stack→List Bool) (w:Aux→List Bool):
    SemiprimeD1StackCalls.run program (abortTime bank w)
      (⟨some (.local .abort),none,none,data bank w,[]⟩:C.State Stack Label)=
        some (⟨none,none,none,rejectedData bank w,[]⟩:C.State Stack Label):=by
  let start:C.State Stack Label:=⟨some (.local .abort),none,none,data bank w,[]⟩
  obtain ⟨out,hr,ha⟩:=abort_trace bank w [] start ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (rejectedData bank w) [] out ha
  have ht:abortTime bank w=(abortTime bank w-1)+1:=by unfold abortTime;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackCachePhaseBankAbort
