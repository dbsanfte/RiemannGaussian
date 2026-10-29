/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanRecord
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Actual nested source calls with shared acquired logger operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanRecordComponents
open SemiprimeD1StackBooleanRecord SemiprimeD1StackProcedureTrace
/-- Actual whole Boolean table acquisition leaves the scope bank and accumulators alone. -/
theorem table_call (mode : SemiprimeD1StackBooleanEntry.Mode) (bank hist out : List Bool) :
    Runs program ((table mode).length+2) (.inl (.start mode))
      (data (fun _=>[]) (S.initial bank).data hist out) (.inl .scope)
      (data (fun _=>table mode) (S.initial bank).data hist out) := by
  apply SemiprimeD1StackProcedureTrace.included_call program tableStack tableLabel
    Sum.inl_injective T.code (mode,0) (fun _=>rfl) (.inl (.start mode)) (.inl .scope) rfl
    ((table mode).length+1) (T.initial mode) (T.done mode)
  · rfl
  · rfl
  · exact SemiprimeD1StackBooleanTableSource.source_run mode
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k => exact (hk k rfl).elim
      | inr k => rfl
/-- The actual binary bank is preserved and its serialized output is the logger input. -/
theorem scope_call (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackPortOrdinalStreamExecution.timeBound words,
      Runs program (t+1) (.inl .scope)
        (data (fun _=>table mode) (S.initial (SemiprimeD1TensorTapeCodec.vectorBits words)).data hist out)
        (.inl .record)
        (data (fun _=>table mode) (SemiprimeD1StackPortOrdinalStreamExecution.done words).data hist out) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPortOrdinalStreamExecution.source_run words
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program scopeStack scopeLabel
    (by intro a b h;exact Sum.inl_injective (Sum.inr_injective h))
    S.program (.control .start) (fun _=>rfl) (.inl .scope) (.inl .record) rfl t
    (S.initial (SemiprimeD1TensorTapeCodec.vectorBits words))
    (SemiprimeD1StackPortOrdinalStreamExecution.done words)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k with
        | inl k => exact (hk k rfl).elim
        | inr k => rfl
/-- Actual logger consumes the two aliased source outputs, with no encoded-answer copy. -/
theorem record_call (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool)) (hist out : List Bool) :
    Runs program (R.recordTime (S.result words) (table mode)+1) (.inl .record)
      (data (fun _=>table mode) (SemiprimeD1StackPortOrdinalStreamExecution.done words).data hist out)
      (.inl .done) (done mode words hist out).data := by
  apply SemiprimeD1StackProcedureTrace.included_call program recordStack recordLabel recordStack_injective
    R.code .record (fun _=>rfl) (.inl .record) (.inl .done) rfl _
    (⟨some .record,none,R.data (S.result words) (table mode) hist out⟩:
      SemiprimeD1StackBytecode.State R.Stack R.Label)
    (⟨none,none,R.data [] [] ((R.row (S.result words) (table mode)).reverse++hist) out⟩:
      SemiprimeD1StackBytecode.State R.Stack R.Label)
  · rfl
  · rfl
  · exact SemiprimeD1StackVertexRecordStream.record_run _ _ _ _ _
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      cases k <;> simp only [done,data,recordStack,scopeStack,tableStack,R.data,
        Sum.elim_inl,Sum.elim_inr,Function.update_same]
    · intro k hk
      rcases k with k|k
      · cases k
        exact (hk SemiprimeD1StackVertexRecordStream.Stack.table rfl).elim
      · cases k with
        | inl k =>
          have hne:k≠SemiprimeD1StackPortOrdinalStream.Stack.output:=by intro h;subst k;exact hk SemiprimeD1StackVertexRecordStream.Stack.ports rfl
          simp only [done,data,Sum.elim_inl,Sum.elim_inr,Function.update_of_ne hne]
        | inr k =>
          cases k with
          | ports => rfl
          | table => rfl
          | history => exact (hk SemiprimeD1StackVertexRecordStream.Stack.history rfl).elim
          | output => exact (hk SemiprimeD1StackVertexRecordStream.Stack.output rfl).elim
end RiemannGaussian.SemiprimeD1StackBooleanRecordComponents
