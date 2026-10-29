/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecord
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Actual table, preserved shared scope and consuming row calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 32768
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordComponents
open SemiprimeD1StackOwnerRecord SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)
namespace TE
export SemiprimeD1StackOwnerTableExecution (done traceTime source_run)
end TE
namespace SE
export SemiprimeD1StackPortOrdinalStreamExecution (done timeBound source_run)
end SE
/-- Actual table-count and prefix/table writing call; no degree/flags advice. -/
theorem table_call (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    Runs program (TE.traceTime key rows words hs+1) (.inl .start)
      (data (T.initial key (records rows tail) (vectorBits words)).data
        (S.initial (vectorBits words)).data hist out) (.inl .scope)
      (data (TE.done key rows tail words hs).data (S.initial (vectorBits words)).data hist out) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program tableStack tableLabel tableStack_injective
    T.program .start (fun _=>rfl) (.inl .start) (.inl .scope) rfl
    (TE.traceTime key rows words hs) (T.initial key (records rows tail) (vectorBits words))
    (TE.done key rows tail words hs)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact TE.source_run key rows tail words hs
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      fin_cases k <;> first | rfl | (exfalso;revert hk;decide)
/-- The SAME physically acquired binary bank supplies the actual ordinal source. -/
theorem scope_call (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    ∃t≤SE.timeBound words,Runs program (t+1) (.inl .scope)
      (data (TE.done key rows tail words hs).data (S.initial (vectorBits words)).data hist out)
      (.inl .record)
      (data (TE.done key rows tail words hs).data (SE.done words).data hist out) := by
  obtain ⟨t,ht,hr⟩:=SE.source_run words
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program scopeStack scopeLabel scopeStack_injective
    S.program (.control .start) (fun _=>rfl) (.inl .scope) (.inl .record) rfl t
    (S.initial (vectorBits words)) (SE.done words)
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
      · fin_cases k <;> rfl
      · cases k with
        | inl k => exact (hk k rfl).elim
        | inr k => rfl
/-- The actual logger consumes real table bytes and physically converted unary ports. -/
theorem record_call (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    Runs program (R.recordTime (S.result words) (table key rows tail words hs)+1) (.inl .record)
      (data (TE.done key rows tail words hs).data (SE.done words).data hist out)
      (.inl .done) (done key rows tail words hs hist out).data := by
  apply SemiprimeD1StackVertexRecordStreamExecution.call program recordStack recordLabel recordStack_injective
    .record (fun _=>rfl) (.inl .record) (.inl .done) rfl
    (R.recordTime (S.result words) (table key rows tail words hs))
    (R.data (S.result words) (table key rows tail words hs) hist out)
    (R.data [] [] ((R.row (S.result words) (table key rows tail words hs)).reverse++hist) out)
  · exact SemiprimeD1StackVertexRecordStream.record_run _ _ _ _ _
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      fin_cases k <;> first | rfl | (exfalso;revert hk;decide)
end RiemannGaussian.SemiprimeD1StackOwnerRecordComponents
