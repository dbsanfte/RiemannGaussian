/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformRecord
import RiemannGaussian.SemiprimeD1StackStaticRecordExecution
import RiemannGaussian.SemiprimeD1StackPublicTransformTableExecution
/-! # Closed actual transform-family whole-table, scope and original row execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRecordExecution
open SemiprimeD1StackPublicTransformRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace T
export SemiprimeD1StackPublicTransformTableTrace (answer budget actual_trace)
end T
/-- Actual final436-role store after consuming the acquired scope/table tapes. -/
def done (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticRecord.done I.static (I.inputTemplate bits second inverse) words (T.answer bits second inverse) hist out
/-- Every acquisition, conversion, frame byte, actual call/return and halt. -/
def timeBound (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticRecordExecution.timeBound I.static (I.inputTemplate bits second inverse) words
    (T.answer bits second inverse) (T.budget bits)
/-- No checker supplier premise remains: the concrete actual transform checker
trace is proved once for ALL original N/two-flags words and every physical scope. -/
theorem source_run (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound bits second inverse words,SemiprimeD1StackCalls.run program t
      (initial bits second inverse (vectorBits words) hist out)=some (done bits second inverse words hist out) :=
  SemiprimeD1StackStaticRecordExecution.source_run I.static (I.inputTemplate bits second inverse)
    (I.template_raw bits second inverse) (T.answer bits second inverse) (T.budget bits)
    (T.actual_trace bits second inverse hc hN) words hist out
/-- Same complete genuine finite machine, with every real return cell. -/
noncomputable def recordInTime (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits second inverse (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits second inverse words hist out))) (timeBound bits second inverse words) :=
  SemiprimeD1StackStaticRecordExecution.recordInTime I.static (I.inputTemplate bits second inverse)
    (I.template_raw bits second inverse) (T.answer bits second inverse) (T.budget bits)
    (T.actual_trace bits second inverse hc hN) words hist out
/-- All original transform template bytes survive; no metadata or verdict was supplied. -/
theorem retained_template (bits : List Bool) (second inverse : Bool) (words : List (List Bool))
    (hist out : List Bool) (k : SemiprimeD1StackPublicTransform.Stack) :
    (done bits second inverse words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.template k))=
      I.inputTemplate bits second inverse k := rfl
/-- Exact original binary occurrence IDs survive in their actual aliased bank. -/
theorem retained_scope (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits second inverse words hist out).data G.original=vectorBits words := rfl
/-- Scope count was acquired by a real scan and is retained in unary. -/
theorem acquired_count (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits second inverse words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.counter .count))=
      List.replicate words.length true := rfl
/-- Exactly one newly acquired row is prepended in reverse to caller history. -/
theorem history_row (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits second inverse words hist out).data G.history=
      (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackPortOrdinalStream.result words)
        (SemiprimeD1StackPublicTransformTableExecution.table bits second inverse words)).reverse++hist := rfl
/-- Caller final output bytes survive unchanged. -/
theorem retained_output (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits second inverse words hist out).data G.output=out := rfl
/-- Both physically acquired source outputs are actually consumed. -/
theorem consumed_outputs (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits second inverse words hist out).data (G.recordStack .ports)=[] ∧
    (done bits second inverse words hist out).data (G.recordStack .table)=[] := ⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformRecordExecution
