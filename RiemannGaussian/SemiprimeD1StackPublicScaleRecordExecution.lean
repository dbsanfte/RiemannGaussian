/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleRecord
import RiemannGaussian.SemiprimeD1StackStaticRecordExecution
import RiemannGaussian.SemiprimeD1StackPublicScaleTableExecution
/-! # Closed actual scale-family whole-table, scope and original row execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleRecordExecution
open SemiprimeD1StackPublicScaleRecord
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace T
export SemiprimeD1StackPublicScaleTableTrace (answer budget actual_trace)
end T
/-- Actual final348-role store after consuming the acquired scope/table tapes. -/
def done (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticRecord.done I.static (I.inputTemplate bits stride frequency inverse) words (T.answer bits stride frequency inverse) hist out
/-- Every acquisition, conversion, frame byte, actual call/return and halt. -/
def timeBound (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticRecordExecution.timeBound I.static (I.inputTemplate bits stride frequency inverse) words
    (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
/-- No checker supplier premise remains: the concrete actual scale checker
trace is proved once for ALL original N/j/k/selector words and every physical scope. -/
theorem source_run (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound bits stride frequency inverse words,SemiprimeD1StackCalls.run program t
      (initial bits stride frequency inverse (vectorBits words) hist out)=some (done bits stride frequency inverse words hist out) :=
  SemiprimeD1StackStaticRecordExecution.source_run I.static (I.inputTemplate bits stride frequency inverse)
    (I.template_raw bits stride frequency inverse) (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
    (T.actual_trace bits stride frequency inverse hj hk hc hN) words hist out
/-- Same complete genuine finite machine, with every real return cell. -/
noncomputable def recordInTime (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits stride frequency inverse words hist out))) (timeBound bits stride frequency inverse words) :=
  SemiprimeD1StackStaticRecordExecution.recordInTime I.static (I.inputTemplate bits stride frequency inverse)
    (I.template_raw bits stride frequency inverse) (T.answer bits stride frequency inverse) (T.budget bits stride frequency)
    (T.actual_trace bits stride frequency inverse hj hk hc hN) words hist out
/-- All original scale template bytes survive; no metadata or verdict was supplied. -/
theorem retained_template (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool))
    (hist out : List Bool) (k : SemiprimeD1StackPublicScale.Stack) :
    (done bits stride frequency inverse words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.template k))=
      I.inputTemplate bits stride frequency inverse k := rfl
/-- Exact original binary occurrence IDs survive in their actual aliased bank. -/
theorem retained_scope (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits stride frequency inverse words hist out).data G.original=vectorBits words := rfl
/-- Scope count was acquired by a real scan and is retained in unary. -/
theorem acquired_count (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits stride frequency inverse words hist out).data (G.tableStack (SemiprimeD1StackStaticTable.counter .count))=
      List.replicate words.length true := rfl
/-- Exactly one newly acquired row is prepended in reverse to caller history. -/
theorem history_row (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits stride frequency inverse words hist out).data G.history=
      (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackPortOrdinalStream.result words)
        (SemiprimeD1StackPublicScaleTableExecution.table bits stride frequency inverse words)).reverse++hist := rfl
/-- Caller final output bytes survive unchanged. -/
theorem retained_output (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits stride frequency inverse words hist out).data G.output=out := rfl
/-- Both physically acquired source outputs are actually consumed. -/
theorem consumed_outputs (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (hist out : List Bool) :
    (done bits stride frequency inverse words hist out).data (G.recordStack .ports)=[] ∧
    (done bits stride frequency inverse words hist out).data (G.recordStack .table)=[] := ⟨rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackPublicScaleRecordExecution
