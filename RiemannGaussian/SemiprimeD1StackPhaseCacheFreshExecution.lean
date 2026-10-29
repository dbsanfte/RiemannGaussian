/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseCacheFreshComponents
/-! # Whole physical phase-heap→sharedP48cache→original fresh generator source
Logical bank/phase parameters below only identify producer-encoded record bytes
and the exact expected final state. The literal runtime input has FOUR words:
heap, allocation counter, issued reference and old UNARY-axis header.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseCacheFreshExecution
open SemiprimeD1StackPhaseCacheFresh SemiprimeD1StackPhaseCacheFreshComponents
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual producer heap bytes, not a selected-bank getter. -/
def heap (banks:List (P.Stack→List Bool)) :List Bool :=
  SemiprimeD1StackHeapAllocate.heapBytes (SemiprimeD1StackPhaseBankRestoreExecution.records banks)
/-- Actual whole prepared front door contains only encoded original allocator/header words. -/
def source (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (axes:List Nat) :C.State Stack Label :=
  initial (heap banks) (List.replicate banks.length true) (List.replicate i.val true)
    (SemiprimeD1StackPhaseChildContextPrimitives.header axes)
/-- Exact stopped cache/output bank, retaining all actual physical heap/counter/reference words. -/
def done (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (a u edges:Nat) (t p:List Bool) (axes:List Nat) :C.State Stack Label :=
  ⟨none,none,none,completed a u edges t p axes (heap banks) (List.replicate banks.length true) (List.replicate i.val true),[]⟩
/-- Own complete clock sums both ACTUAL calls, all context/rank/width/value expansion and actual halt. -/
def runBound (banks:List (P.Stack→List Bool)) (i:Fin banks.length) (a u edges:Nat) (t p:List Bool) (axes:List Nat) :Nat :=
  SemiprimeD1StackPhaseBankRestoreExecution.runBound banks i+
  SemiprimeD1StackPhaseChildContextFreshExecution.phaseReadyBound a u edges t p axes+3
/-- Literal same-machine trace dereferences the record, restores48roles and REAL-calls cached Fresh. -/
theorem source_trace (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) :
    ∃q,q+1≤ runBound banks i a u edges t p axes ∧ Runs program q (ctl .start)
      (source banks i axes).data (ctl .done) (done banks i a u edges t p axes).data :=by
  obtain ⟨b,hb,h0⟩:=restore_call banks i (SemiprimeD1StackPhaseChildContextPrimitives.header axes)
  rw [hbank] at h0
  obtain ⟨c,hc,h1⟩:=fresh_call a u edges t p axes hp (heap banks) (List.replicate banks.length true) (List.replicate i.val true)
  exact ⟨b+c,by unfold runBound;omega,join h0 h1⟩
/-- Whole actual halt has no decodedbank/a/u/M/t/p/q/P/rank/vector/clock input payload. -/
theorem source_run (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) :
    ∃q≤ runBound banks i a u edges t p axes,
      SemiprimeD1StackCalls.run program q (source banks i axes)=some (done banks i a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=source_trace banks i a u edges t p axes hp hbank
  obtain ⟨finish,hf,hAt⟩:=hr [] (source banks i axes) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (done banks i a u edges t p axes).data [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine143-role compiled-machine whole-consumer certificate, with its own VALUE-charged clock. -/
noncomputable def cacheFreshInTime (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (source banks i axes))
      (some (SemiprimeD1StackCalls.configuration (done banks i a u edges t p axes)))
      (runBound banks i a u edges t p axes) :=by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (ctl .start) program
  let h:=source_run banks i a u edges t p axes hp hbank
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseCacheFreshExecution
