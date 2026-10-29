/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecord
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Real component calls with directly shared acquired operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticRecordComponents
open SemiprimeD1StackStaticRecord SemiprimeD1StackProcedureTrace
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L)
/-- The actual whole table trace is included with its genuine nested returns;
all serializer shadows and caller accumulators are retained. -/
theorem table_call (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackStaticTableExecution.timeBound s template words answer budget,
      Runs (program s) (t+1) (.inl .start)
        (initial s template (vectorBits words) hist out).data (.inl .scope)
        (afterTable template words answer hist out) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackStaticTableExecution.source_run s template hraw answer budget hc words
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s) tableStack tableLabel
    Sum.inl_injective (T.program s) .start (fun _=>rfl) (.inl .start) (.inl .scope) rfl t
    (T.initial s template (vectorBits words))
    (SemiprimeD1StackStaticTableExecution.done s template words answer)
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
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
omit [Fintype K] in
/-- Every serializer bit is acquired from the actual retained scope bank;
the aliased bank remains in the table component and its private shadow is empty. -/
theorem scope_call (template : K→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackPortOrdinalStreamExecution.timeBound words,
      Runs (program s) (t+1) (.inl .scope) (afterTable template words answer hist out)
        (.inl .record) (afterScope template words answer hist out) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPortOrdinalStreamExecution.source_run words
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call (program s) scopeStack scopeLabel
    scopeStack_injective S.program (.control .start) (fun _=>rfl) (.inl .scope) (.inl .record) rfl t
    (S.initial (vectorBits words)) (SemiprimeD1StackPortOrdinalStreamExecution.done words)
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
      | inl k=>rfl
      | inr k=>
        cases k with
        | inl k=>
          cases k with
          | bank=>rfl
          | reader=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.reader rfl).elim
          | word=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.word rfl).elim
          | fieldScratch=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.fieldScratch rfl).elim
          | valid=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.valid rfl).elim
          | copyScratch=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.copyScratch rfl).elim
          | digits=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.digits rfl).elim
          | unaryScratch=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.unaryScratch rfl).elim
          | unary=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.unary rfl).elim
          | logScratch=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.logScratch rfl).elim
          | history=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.history rfl).elim
          | output=>exact (hk SemiprimeD1StackPortOrdinalStream.Stack.output rfl).elim
        | inr k=>rfl
omit [Fintype K] in
/-- Actual logging consumes exactly the acquired unary-port and tensor tapes. -/
theorem record_call (template : K→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (hist out : List Bool) :
    Runs (program s)
      (R.recordTime (S.result words) (SemiprimeD1StackStaticTableExecution.outputTape answer words)+1)
      (.inl .record) (afterScope template words answer hist out) (.inl .done)
      (done s template words answer hist out).data := by
  apply SemiprimeD1StackProcedureTrace.included_call (program s) recordStack recordLabel recordStack_injective
    R.code .record (fun _=>rfl) (.inl .record) (.inl .done) rfl _
    (⟨some .record,none,R.data (S.result words)
      (SemiprimeD1StackStaticTableExecution.outputTape answer words) hist out⟩:
      SemiprimeD1StackBytecode.State R.Stack R.Label)
    (⟨none,none,R.data [] [] ((R.row (S.result words)
      (SemiprimeD1StackStaticTableExecution.outputTape answer words)).reverse++hist) out⟩:
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
      cases k with
      | inl k=>
        have hn:k≠T.aux .output:=by
          intro he;subst k;exact hk SemiprimeD1StackVertexRecordStream.Stack.table rfl
        exact Function.update_of_ne hn _ _
      | inr k=>
        cases k with
        | inl k=>
          have hn:k≠SemiprimeD1StackPortOrdinalStream.Stack.output:=by
            intro he;subst k;exact hk SemiprimeD1StackVertexRecordStream.Stack.ports rfl
          exact Function.update_of_ne hn _ _
        | inr k=>
          cases k with
          | ports=>rfl
          | table=>rfl
          | history=>exact (hk SemiprimeD1StackVertexRecordStream.Stack.history rfl).elim
          | output=>exact (hk SemiprimeD1StackVertexRecordStream.Stack.output rfl).elim
end RiemannGaussian.SemiprimeD1StackStaticRecordComponents
