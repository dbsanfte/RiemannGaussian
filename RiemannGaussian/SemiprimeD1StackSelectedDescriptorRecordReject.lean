/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordComponents
import RiemannGaussian.SemiprimeD1StackTransformSelectorsReject
/-! # Actual unknown-constructor abort before any metadata-record acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordReject
open SemiprimeD1StackSelectedDescriptorRecord SemiprimeD1StackProcedureTrace
variable {K L : Type} [DecidableEq K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Unknown-constructor final store: old template/scope/caller bytes untouched;
old selectors physically erased, all original raw fields retained, no new row. -/
def aborted (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (bank hist out : List Bool) :
    C.State (Stack K) (Label L s.roles.length) :=
  ⟨none,none,none,data
    (SemiprimeD1StackDescriptorRecord.initial s oldTemplate (fields raw [] []) bank hist out).data
    (raw 1) (raw 2),[]⟩
/-- The actual included selector's unknown-tag abort returns empty selectors;
no selector value or failure result is supplied by the enclosing caller. -/
theorem selector_abort_call (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (code : Fin 18) (htag : raw 1=List.replicate code.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch code=.abort)
    (oldStage oldInverse bank hist out : List Bool) :
    Runs (program s sourceMap) (oldStage.length+oldInverse.length+6*code.val+9)
      (.inl .start) (initial s oldTemplate raw oldStage oldInverse bank hist out).data (.inl .guard)
      (aborted s oldTemplate raw bank hist out).data :=by
  have hr:=SemiprimeD1StackTransformSelectorsReject.tag_abort_run code hcode (raw 2) oldStage oldInverse
  rw [←htag] at hr
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s sourceMap) selectorStack selectorLabel
    selectorStack_injective S.program .start (fun _=>rfl) (.inl .start) (.inl .guard) rfl
    (oldStage.length+oldInverse.length+6*code.val+8)
    (S.initial (raw 1) (raw 2) oldStage oldInverse)
    (SemiprimeD1StackTransformSelectorsReject.aborted (raw 1) (raw 2) [] [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      cases k with
      | inl k=>
        cases k with
        | inl k=>rfl
        | inr k=>
          cases k with
          | inl i=>
            fin_cases i
            · rfl
            · exact (hk SemiprimeD1StackTransformSelectors.Stack.stage rfl).elim
            · exact (hk SemiprimeD1StackTransformSelectors.Stack.inverse rfl).elim
            · rfl
            · rfl
            · rfl
          | inr k=>rfl
      | inr k=>cases k <;> rfl
/-- Actual success peek follows the EMPTY branch after an unknown constructor,
then the actual enclosing source halts before ANY loader/table/row instruction. -/
theorem source_abort_run (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (code : Fin 18) (htag : raw 1=List.replicate code.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch code=.abort)
    (oldStage oldInverse bank hist out : List Bool) :
    C.run (program s sourceMap) (oldStage.length+oldInverse.length+6*code.val+11)
      (initial s oldTemplate raw oldStage oldInverse bank hist out)=some (aborted s oldTemplate raw bank hist out) :=by
  have h0:=selector_abort_call s sourceMap oldTemplate raw code htag hcode oldStage oldInverse bank hist out
  have h1:Runs (program s sourceMap) 1 (.inl .guard) (aborted s oldTemplate raw bank hist out).data
      (.inl .abort) (aborted s oldTemplate raw bank hist out).data:=by
    apply one_base (program s sourceMap) _ _ (.peek (selectorStack .stage) (.inl .abort) (.inl .record) (.inl .record)) _ _ rfl
    · rfl
    · rfl
  have h:=runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,ho⟩:=h [] (initial s oldTemplate raw oldStage oldInverse bank hist out) ⟨rfl,rfl,rfl⟩
  rw [show oldStage.length+oldInverse.length+6*code.val+11=
    ((oldStage.length+oldInverse.length+6*code.val+9)+1)+1 by omega,
    SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases ho with ⟨hp,hd,hf⟩
  change SemiprimeD1StackCalls.step (program s sourceMap) finish=some (aborted s oldTemplate raw bank hist out)
  simp [SemiprimeD1StackCalls.step,hp,program,SemiprimeD1StackCalls.execute,hd,hf,aborted]
end RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordReject
