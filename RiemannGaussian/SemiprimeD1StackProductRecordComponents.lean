/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductRecord
/-! # Actual nested source calls with shared acquired logger operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductRecordComponents
open SemiprimeD1StackProductRecord SemiprimeD1StackProcedureTrace
/-- Actual whole product-table acquisition leaves the scope bank and accumulators alone. -/
theorem table_call (bits bank hist out : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackProductTableExecution.timeBound bits,
      Runs program (t+1) (.inl .start)
        (data (Z.initial bits).data (S.initial bank).data hist out) (.inl .scope)
        (data (Z.done bits).data (S.initial bank).data hist out) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductTableExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program tableStack tableLabel
    Sum.inl_injective Z.program .start (fun _=>rfl) (.inl .start) (.inl .scope) rfl t
    (Z.initial bits) (Z.done bits)
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
      cases k with
      | inl k => exact (hk k rfl).elim
      | inr k => rfl
/-- The actual binary bank is preserved and its serialized output is the logger input. -/
theorem scope_call (bits : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackPortOrdinalStreamExecution.timeBound words,
      Runs program (t+1) (.inl .scope)
        (data (Z.done bits).data (S.initial (SemiprimeD1TensorTapeCodec.vectorBits words)).data hist out)
        (.inl .record)
        (data (Z.done bits).data (SemiprimeD1StackPortOrdinalStreamExecution.done words).data hist out) := by
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
theorem record_call (bits : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    Runs program (R.recordTime (S.result words) (table bits)+1) (.inl .record)
      (data (Z.done bits).data (SemiprimeD1StackPortOrdinalStreamExecution.done words).data hist out)
      (.inl .done) (done bits words hist out).data := by
  apply SemiprimeD1StackProcedureTrace.included_call program recordStack recordLabel recordStack_injective
    R.code .record (fun _=>rfl) (.inl .record) (.inl .done) rfl _
    (⟨some .record,none,R.data (S.result words) (table bits) hist out⟩:
      SemiprimeD1StackBytecode.State R.Stack R.Label)
    (⟨none,none,R.data [] [] ((R.row (S.result words) (table bits)).reverse++hist) out⟩:
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
      · have hne:k≠Z.output:=by intro h;subst k;exact hk SemiprimeD1StackVertexRecordStream.Stack.table rfl
        simp only [done,data,Sum.elim_inl,Function.update_of_ne hne]
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
end RiemannGaussian.SemiprimeD1StackProductRecordComponents
