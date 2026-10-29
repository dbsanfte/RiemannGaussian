/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseBankRestoreFields
/-! # Complete actual heap→forty-eight-word phase-bank restoration
Only the physical heap, allocation-count and issued-reference words are supplied.
Logical banks/index describe actual allocator bytes in proofs; no getter, bank
function, decoded answer, phase arithmetic or clock is present in runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseBankRestoreExecution
open SemiprimeD1StackPhaseBankRestore SemiprimeD1StackPhaseBankRestorePrimitives
open SemiprimeD1StackPhaseBankRestoreFields SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Logical allocation history names the actual forty-eight-frame record bytes. -/
def records (banks:List (P.Stack→List Bool)) :List (List Bool) :=banks.map record
/-- Same allocator-issued ordinal, with only a proof cast across the record encoding's length. -/
def index (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :Fin (records banks).length :=
  ⟨i.val,by simpa only [records,List.length_map] using i.isLt⟩
/-- Actual initial physical heap bytes. The bank itself is never an input tape. -/
def source (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :C.State Stack Label :=
  initial (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true) (List.replicate i.val true)
/-- Exact expected stop, preserving all original heap/counter/reference words. -/
def target (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :C.State Stack Label :=
  done banks[i.val] (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true) (List.replicate i.val true)
/-- Own actual complete clock: real heap call,48real field calls/flags,real EOF and halt. -/
def runBound (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :Nat :=
  SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+8*mass banks[i.val] 0+388
/-- Consumed reader output and validation flag leave every actual heap-read work role clear. -/
theorem view_done (bank:P.Stack→List Bool) (heap counter reference:List Bool) :
    view bank heap counter reference [] []=result bank heap counter reference :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Real heap dereference returns exactly the record encoded at the original issued ordinal. -/
theorem heap_run (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    Runs program (SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+1) (ctl .start)
      (source banks i).data (ctl .heapCheck)
      (view (fun _=>[]) (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true)
        (List.replicate i.val true) (record banks[i.val]) [true]) :=by
  have h:=heap_call (records banks) (index banks i)
  have he:(records banks)[(index banks i).val]=record banks[i.val]:=by simp only [records,index,List.getElem_map]
  rw [he] at h
  simpa only [source,records,List.length_map,index] using h
/-- Actual heap-valid true pop enters the first field parser, clearing the shared flag tape. -/
theorem heap_valid (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    Runs program 1 (ctl .heapCheck)
      (view (fun _=>[]) (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true)
        (List.replicate i.val true) (record banks[i.val]) [true]) (ctl (.field 0))
      (view (fun _=>[]) (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true)
        (List.replicate i.val true) (record banks[i.val]) []) :=by
  have h:=valid_run .heapCheck (ctl (.field 0))
    (view (fun _=>[]) (SemiprimeD1StackHeapAllocate.heapBytes (records banks)) (List.replicate banks.length true)
      (List.replicate i.val true) (record banks[i.val]) [true]) rfl rfl
  rw [view_valid] at h
  exact h
/-- Complete prepared restoration trace is real heap dereference→48real field calls→actual EOF. -/
theorem source_trace (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    Runs program (SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+8*mass banks[i.val] 0+387)
      (ctl .start) (source banks i).data (ctl .done) (target banks i).data :=by
  have h0:=heap_run banks i
  have h1:=heap_valid banks i
  have h2:=fields_run banks[i.val] (SemiprimeD1StackHeapAllocate.heapBytes (records banks))
    (List.replicate banks.length true) (List.replicate i.val true)
  rw [view_done] at h2
  have hh:=join (join h0 h1) h2
  have hc:(SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+1)+1+
      (8*mass banks[i.val] 0+385)=
      SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+8*mass banks[i.val] 0+387:=by omega
  rw [hc] at hh
  exact hh
/-- Exact actual whole halt restores the logical selected bank from physical bytes ONLY. -/
theorem run_exact (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    SemiprimeD1StackCalls.run program (runBound banks i) (source banks i)=some (target banks i) :=by
  have ht:=source_trace banks i
  obtain ⟨finish,hf,hAt⟩:=ht [] (source banks i) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (target banks i).data [] finish hAt
  have hc:runBound banks i=
      (SemiprimeD1StackHeapReadBounds.readTimeAt (records banks) (index banks i)+8*mass banks[i.val] 0+387)+1:=by
    unfold runBound
    omega
  rw [hc,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Own bounded whole-source API supports all-prefix resource proofs at the actual finite clock. -/
theorem source_run (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    ∃q≤ runBound banks i,SemiprimeD1StackCalls.run program q (source banks i)=some (target banks i) :=
  ⟨runBound banks i,le_rfl,run_exact banks i⟩
/-- Restored phase projection is IDENTICALLY the actual selected bank, including every rejected field. -/
theorem phase_restored (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (k:P.Stack) :
    (target banks i).data (phaseStack k)=banks[i.val] k :=rfl
/-- Every actual reader word equals the original heap/counter/reference bank with work clear. -/
theorem heap_retained (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (k:H.Stack) :
    (target banks i).data (heapStack k)=H.input (SemiprimeD1StackHeapAllocate.heapBytes (records banks))
      (List.replicate banks.length true) (List.replicate i.val true) k :=rfl
/-- Genuine58-role compiled-machine certificate, charging its own physical whole consumer clock. -/
noncomputable def restoreInTime (banks:List (P.Stack→List Bool)) (i:Fin banks.length) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source banks i))
      (some (SemiprimeD1StackCalls.configuration (target banks i))) (runBound banks i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (ctl .start) program
  exact ⟨⟨runBound banks i,run_exact banks i⟩,le_rfl⟩
end RiemannGaussian.SemiprimeD1StackPhaseBankRestoreExecution
