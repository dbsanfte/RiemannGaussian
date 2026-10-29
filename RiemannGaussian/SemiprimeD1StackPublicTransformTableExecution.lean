/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformTableTrace
import RiemannGaussian.SemiprimeD1StackStaticTableBounds
/-! # Actual complete public integer transform truth-table acquisition
The actual fixed420-role program scans its scope vector, copies only original
N/two-flag template inputs, executes the original transform checker at every real
assignment and writes the full original-order tape. No evaluator is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2040000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTableExecution
open SemiprimeD1StackPublicTransformTable SemiprimeD1StackPublicTransformTableTrace
namespace G
export SemiprimeD1StackStaticTableExecution (outputTape)
end G
/-- Exact complete acquired tensor tape, specified at the real scope-vector arity. -/
def table (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) : List Bool :=
  G.outputTape (answer bits second inverse) words
/-- All204 checker work roles clear; original template and scope/count survive. -/
def done (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTableExecution.done static (inputTemplate bits second inverse) words (answer bits second inverse)
/-- Complete OWN actual source bound, including actual scope-byte acquisition. -/
def timeBound (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticTableBounds.runBound static (inputTemplate bits second inverse) words (budget bits)
/-- Whole actual source: original physical N/two-flag/scope words ONLY. Generic
trace premises are instantiated by the frozen complete real transform checker. -/
theorem source_run (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    ∃t≤ timeBound bits second inverse words,SemiprimeD1StackCalls.run program t
      (initial bits second inverse (SemiprimeD1TensorTapeCodec.vectorBits words))=some (done bits second inverse words) :=
  SemiprimeD1StackStaticTableBounds.source_run_bounded static (inputTemplate bits second inverse)
    (template_raw bits second inverse) (answer bits second inverse) (budget bits) (actual_trace bits second inverse hc hN) words
/-- SAME genuine fixed finite machine, including all actual template copies,
recursive calls, checker arithmetic, cleanup and real return-stack cells. -/
noncomputable def tableInTime (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits second inverse (SemiprimeD1TensorTapeCodec.vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits second inverse words))) (timeBound bits second inverse words) :=
  SemiprimeD1StackStaticTableBounds.tableInTime static (inputTemplate bits second inverse)
    (template_raw bits second inverse) (answer bits second inverse) (budget bits) (actual_trace bits second inverse hc hN) words
/-- Every actual original checker-input template role survives byte for byte. -/
theorem retained_template (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits second inverse words).data (SemiprimeD1StackStaticTable.template k)=inputTemplate bits second inverse k := rfl
/-- The physically acquired scope-ID vector survives unchanged. -/
theorem retained_scope (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) :
    (done bits second inverse words).data (SemiprimeD1StackStaticTable.counter .bank)=
      SemiprimeD1TensorTapeCodec.vectorBits words := rfl
/-- Physically counted and restored unary arity; it was never initialized as advice. -/
theorem acquired_count (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) :
    (done bits second inverse words).data (SemiprimeD1StackStaticTable.counter .count)=
      List.replicate words.length true := rfl
/-- ALL204 actual checker fields, including retained arithmetic caches/shadows,
are physically empty after their complete cleanup, rather than silently discarded. -/
theorem checker_clear (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits second inverse words).data (SemiprimeD1StackStaticTable.checker k)=[] := rfl
/-- Exact complete tape is actually present in the unique output role. -/
theorem output_table (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) :
    (done bits second inverse words).data (SemiprimeD1StackStaticTable.aux .output)=table bits second inverse words := rfl
end RiemannGaussian.SemiprimeD1StackPublicTransformTableExecution
