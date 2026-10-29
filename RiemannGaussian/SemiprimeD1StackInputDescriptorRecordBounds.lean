/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDescriptorRecordExecution
import RiemannGaussian.SemiprimeD1StackDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicInputRecordClock
/-! # Concrete139-role descriptor-to-input-record own clock and all prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackInputDescriptorRecordBounds
open SemiprimeD1StackInputDescriptorRecord SemiprimeD1StackInputDescriptorRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All actual physical inputs, including every old template word and all six sources. -/
def inputSize (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordBounds.inputSize I.static oldTemplate inputFields bank hist out
/-- Complete same-source clock: real template drain/load plus the entire
concrete input-checker table, physical ordinal conversion and consuming log. -/
def runBound (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (M : Nat) (hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields (vectorBits words) hist out+
    SemiprimeD1StackPublicInputRecordClock.runBound (inputFields 0) (inputFields 3) words M+2
/-- Every charged old-template byte and every selected-source copy is paid. -/
theorem prepareBound_eq (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields bank hist out=
      52*(6*inputSize oldTemplate inputFields bank hist out+5)+2 := by
  unfold SemiprimeD1StackDescriptorRecordExecution.prepareBound SemiprimeD1StackDescriptorRecordLoad.loadUnit
  exact congrArg (fun n:Nat=>n*(6*inputSize oldTemplate inputFields bank hist out+5)+2)
    SemiprimeD1StackPublicInputTable.roles_length
/-- Closed own bit clock; no native report or evaluator bound is substituted. -/
theorem timeBound_le (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (M : Nat) (hist out : List Bool) (hl : ∀w∈words,w.length≤M)
    (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound oldTemplate inputFields words hist out≤runBound oldTemplate inputFields words M hist out := by
  have h:=SemiprimeD1StackPublicInputRecordClock.timeBound_le (inputFields 0) (inputFields 3) words M hl hv
  unfold timeBound SemiprimeD1StackDescriptorRecordExecution.timeBound runBound
  rw [selected_fields]
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) 2
/-- Complete actual concrete source, including descriptor initialization. -/
theorem source_run_bounded (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (M : Nat) (hist out : List Bool)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    ∃t≤runBound oldTemplate inputFields words M hist out,SemiprimeD1StackCalls.run program t
      (initial oldTemplate inputFields (vectorBits words) hist out)=some (done inputFields words hist out) := by
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate inputFields hb words hist out
  exact ⟨t,ht.trans (timeBound_le oldTemplate inputFields words M hist out hl hv),hr⟩
/-- All139 roles, six retained physical sources, every dormant shadow and every
real nested return-stack cell at every reached source prefix. -/
theorem prefix_cells (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) (fuel : Nat)
    (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial oldTemplate inputFields (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      140*(inputSize oldTemplate inputFields (vectorBits words) hist out+timeBound oldTemplate inputFields words hist out+1) := by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields I.static.raw=[]:=by rw [selected_fields];rfl
  have hc:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields)
      (T.answer (inputFields 0) (inputFields 3)) (T.budget (inputFields 0) (inputFields 3)):=by
    rw [selected_fields];exact T.actual_trace (inputFields 0) (inputFields 3) hb
  have h:=SemiprimeD1StackDescriptorRecordBounds.prefix_cells I.static sourceMap oldTemplate inputFields hraw
    (T.answer (inputFields 0) (inputFields 3)) (T.budget (inputFields 0) (inputFields 3)) hc words hist out fuel finish hr
  rw [SemiprimeD1StackPublicInput.stack_card] at h
  exact h
/-- Same full physical prefix certificate on the genuine finite machine itself. -/
theorem machine_prefix_cells (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial oldTemplate inputFields (vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      140*(inputSize oldTemplate inputFields (vectorBits words) hist out+timeBound oldTemplate inputFields words hist out+1) := by
  have hraw:SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields I.static.raw=[]:=by rw [selected_fields];rfl
  have hc:SemiprimeD1StackStaticTableSpec.CheckerTrace I.static
      (SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields)
      (T.answer (inputFields 0) (inputFields 3)) (T.budget (inputFields 0) (inputFields 3)):=by
    rw [selected_fields];exact T.actual_trace (inputFields 0) (inputFields 3) hb
  have h:=SemiprimeD1StackDescriptorRecordBounds.machine_prefix_cells I.static sourceMap oldTemplate inputFields hraw
    (T.answer (inputFields 0) (inputFields 3)) (T.budget (inputFields 0) (inputFields 3)) hc words hist out fuel cfg hr
  rw [SemiprimeD1StackPublicInput.stack_card] at h
  exact h
end RiemannGaussian.SemiprimeD1StackInputDescriptorRecordBounds
