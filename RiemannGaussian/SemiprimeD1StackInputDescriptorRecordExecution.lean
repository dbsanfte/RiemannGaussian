/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDescriptorRecord
import RiemannGaussian.SemiprimeD1StackDescriptorRecordExecution
/-! # Concrete physical input descriptor initialization and entire old input row -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackInputDescriptorRecordExecution
open SemiprimeD1StackInputDescriptorRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace T
export SemiprimeD1StackPublicInputTableTrace (answer budget actual_trace)
end T
/-- Six physical source fields equal their literal coordinate projection;
this is proof-side extensionality, never an executed metadata supplier. -/
theorem fields_eta (inputFields : Fin 6→List Bool) :
    fields (inputFields 0) (inputFields 1) (inputFields 2) (inputFields 3) (inputFields 4) (inputFields 5)=inputFields := by
  funext i;fin_cases i <;> rfl
/-- Arbitrary actual acquired fields initialize EXACTLY the frozen original
input template: only binary N and the original coord1 input-index markers. -/
theorem selected_fields (inputFields : Fin 6→List Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap inputFields=I.inputTemplate (inputFields 0) (inputFields 3) := by
  have h:=selected_template (inputFields 0) (inputFields 1) (inputFields 2) (inputFields 3) (inputFields 4) (inputFields 5)
  rw [fields_eta] at h
  exact h
/-- Whole139-role result after real load, compilation, scope conversion and logging. -/
def done (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackDescriptorRecord.done I.static sourceMap inputFields words
    (T.answer (inputFields 0) (inputFields 3)) hist out
/-- Complete actual source clock, including the arbitrary dirty template. -/
def timeBound (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (words : List (List Bool))
    (hist out : List Bool) : Nat :=
  SemiprimeD1StackDescriptorRecordExecution.timeBound I.static sourceMap oldTemplate inputFields words
    (T.answer (inputFields 0) (inputFields 3)) (T.budget (inputFields 0) (inputFields 3)) hist out
/-- The real52-role template loader's complete trace; all original descriptor
fields and every non-template component role are retained exactly. -/
theorem template_run (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    ∃t≤SemiprimeD1StackDescriptorRecordExecution.prepareBound I.static oldTemplate inputFields bank hist out,
      SemiprimeD1StackProcedureTrace.Runs program t (.inl .start) (initial oldTemplate inputFields bank hist out).data
        (.inl .record) (SemiprimeD1StackDescriptorRecord.data
          (SemiprimeD1StackPublicInputRecord.initial (inputFields 0) (inputFields 3) bank hist out).data inputFields []) := by
  have h:=SemiprimeD1StackDescriptorRecordExecution.prepare_call I.static sourceMap oldTemplate inputFields bank hist out
  simpa only [SemiprimeD1StackDescriptorRecord.afterLoad,selected_fields,
    SemiprimeD1StackInputDescriptorRecord.program,SemiprimeD1StackInputDescriptorRecord.initial,
    SemiprimeD1StackPublicInputRecord.initial] using h
/-- Fully concrete actual source: no checker/template/count/table/verdict
supplier premise remains. Scope and all six source words are already acquired. -/
theorem source_run (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound oldTemplate inputFields words hist out,SemiprimeD1StackCalls.run program t
      (initial oldTemplate inputFields (vectorBits words) hist out)=some (done inputFields words hist out) := by
  apply SemiprimeD1StackDescriptorRecordExecution.source_run I.static sourceMap oldTemplate inputFields
  · rw [selected_fields];rfl
  · rw [selected_fields]
    exact T.actual_trace (inputFields 0) (inputFields 3) hb
/-- Genuine finite-machine trace with the same full actual own source clock. -/
noncomputable def recordInTime (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool)
    (hb : inputFields 0≠[]) (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial oldTemplate inputFields (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done inputFields words hist out)))
      (timeBound oldTemplate inputFields words hist out) := by
  apply SemiprimeD1StackDescriptorRecordExecution.recordInTime I.static sourceMap oldTemplate inputFields
  · rw [selected_fields];rfl
  · rw [selected_fields]
    exact T.actual_trace (inputFields 0) (inputFields 3) hb
/-- Every actual component data cell agrees with the frozen concrete132-role
input-record result, after physical descriptor initialization rather than advice. -/
theorem component_done (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool)
    (k : SemiprimeD1StackPublicInputRecord.Stack) :
    (done inputFields words hist out).data (D.recordStack k)=
      (SemiprimeD1StackPublicInputRecordExecution.done (inputFields 0) (inputFields 3) words hist out).data k := by
  unfold done SemiprimeD1StackDescriptorRecord.done
  rw [selected_fields]
  rfl
/-- All six actual source words are retained byte for byte, including tag and unused coordinates. -/
theorem retained_source (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) (i : Fin 6) :
    (done inputFields words hist out).data (D.source i)=inputFields i := rfl
/-- The actual loader scratch is physically empty at completion. -/
theorem scratch_clear (inputFields : Fin 6→List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done inputFields words hist out).data D.scratch=[] := rfl
end RiemannGaussian.SemiprimeD1StackInputDescriptorRecordExecution
