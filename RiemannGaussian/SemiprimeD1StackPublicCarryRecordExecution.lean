/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryRecord
import RiemannGaussian.SemiprimeD1StackStaticRecordExecution
import RiemannGaussian.SemiprimeD1StackPublicCarryTableExecution
/-! # Closed actual carry-family whole-table, scope and original row execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicCarryRecordExecution
open SemiprimeD1StackPublicCarryRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace T
export SemiprimeD1StackPublicCarryTableTrace (answer budget actual_trace)
end T
/-- Actual final130-role store after consuming the acquired scope/table tapes. -/
def done (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticRecord.done I.static (I.inputTemplate bits indexWord) words (T.answer bits indexWord) hist out
/-- Every acquisition, conversion, frame byte, actual call/return and halt. -/
def timeBound (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticRecordExecution.timeBound I.static (I.inputTemplate bits indexWord) words
    (T.answer bits indexWord) (T.budget bits indexWord)
/-- No checker supplier premise remains: the concrete actual carry checker
trace is proved once for ALL original N/index words and every physical scope. -/
theorem source_run (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound bits indexWord words,SemiprimeD1StackCalls.run program t
      (initial bits indexWord (vectorBits words) hist out)=some (done bits indexWord words hist out) :=
  SemiprimeD1StackStaticRecordExecution.source_run I.static (I.inputTemplate bits indexWord)
    (I.template_raw bits indexWord) (T.answer bits indexWord) (T.budget bits indexWord)
    (T.actual_trace bits indexWord hb) words hist out
/-- Same complete genuine finite machine, with every real return cell. -/
noncomputable def recordInTime (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits indexWord (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits indexWord words hist out))) (timeBound bits indexWord words) :=
  SemiprimeD1StackStaticRecordExecution.recordInTime I.static (I.inputTemplate bits indexWord)
    (I.template_raw bits indexWord) (T.answer bits indexWord) (T.budget bits indexWord)
    (T.actual_trace bits indexWord hb) words hist out
/-- All original carry template bytes survive; no metadata or verdict was supplied. -/
theorem retained_template (bits indexWord : List Bool) (words : List (List Bool))
    (hist out : List Bool) (k : SemiprimeD1StackPublicCarry.Stack) :
    (done bits indexWord words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.template k))=
      I.inputTemplate bits indexWord k := rfl
/-- Exact original binary occurrence IDs survive in their actual aliased bank. -/
theorem retained_scope (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits indexWord words hist out).data G.original=vectorBits words := rfl
/-- Scope count was acquired by a real scan and is retained in unary. -/
theorem acquired_count (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits indexWord words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.counter .count))=
      List.replicate words.length true := rfl
/-- Exactly one newly acquired row is prepended in reverse to caller history. -/
theorem history_row (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits indexWord words hist out).data G.history=
      (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackPortOrdinalStream.result words)
        (SemiprimeD1StackPublicCarryTableExecution.table bits indexWord words)).reverse++hist := rfl
/-- Caller final output bytes survive unchanged. -/
theorem retained_output (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits indexWord words hist out).data G.output=out := rfl
/-- Both physically acquired source outputs are actually consumed. -/
theorem consumed_outputs (bits indexWord : List Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits indexWord words hist out).data (G.recordStack .ports)=[] ∧
    (done bits indexWord words hist out).data (G.recordStack .table)=[] := ⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackPublicCarryRecordExecution
