/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleTableTrace
import RiemannGaussian.SemiprimeD1StackStaticTableBounds
/-! # Actual complete public integer scale truth-table acquisition
The actual fixed332-role program scans its scope vector, copies only original
N/j/k/selector template inputs, executes the original scale checker at every real
assignment and writes the full original-order tape. No evaluator is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTableExecution
open SemiprimeD1StackPublicScaleTable SemiprimeD1StackPublicScaleTableTrace
namespace G
export SemiprimeD1StackStaticTableExecution (outputTape)
end G
/-- Exact complete acquired tensor tape, specified at the real scope-vector arity. -/
def table (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) : List Bool :=
  G.outputTape (answer bits stride frequency inverse) words
/-- All160 checker work roles clear; original template and scope/count survive. -/
def done (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTableExecution.done static (inputTemplate bits stride frequency inverse) words (answer bits stride frequency inverse)
/-- Complete OWN actual source bound, including actual scope-byte acquisition. -/
def timeBound (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticTableBounds.runBound static (inputTemplate bits stride frequency inverse) words (budget bits stride frequency)
/-- Whole actual source: original physical N/j/k/selector/scope words ONLY. Generic
trace premises are instantiated by the frozen complete real scale checker. -/
theorem source_run (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    ∃t≤ timeBound bits stride frequency inverse words,SemiprimeD1StackCalls.run program t
      (initial bits stride frequency inverse (SemiprimeD1TensorTapeCodec.vectorBits words))=some (done bits stride frequency inverse words) :=
  SemiprimeD1StackStaticTableBounds.source_run_bounded static (inputTemplate bits stride frequency inverse)
    (template_raw bits stride frequency inverse) (answer bits stride frequency inverse) (budget bits stride frequency) (actual_trace bits stride frequency inverse hj hk hc hN) words
/-- SAME genuine fixed finite machine, including all actual template copies,
recursive calls, checker arithmetic, cleanup and real return-stack cells. -/
noncomputable def tableInTime (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (SemiprimeD1TensorTapeCodec.vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits stride frequency inverse words))) (timeBound bits stride frequency inverse words) :=
  SemiprimeD1StackStaticTableBounds.tableInTime static (inputTemplate bits stride frequency inverse)
    (template_raw bits stride frequency inverse) (answer bits stride frequency inverse) (budget bits stride frequency) (actual_trace bits stride frequency inverse hj hk hc hN) words
/-- Every actual original checker-input template role survives byte for byte. -/
theorem retained_template (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits stride frequency inverse words).data (SemiprimeD1StackStaticTable.template k)=inputTemplate bits stride frequency inverse k := rfl
/-- The physically acquired scope-ID vector survives unchanged. -/
theorem retained_scope (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) :
    (done bits stride frequency inverse words).data (SemiprimeD1StackStaticTable.counter .bank)=
      SemiprimeD1TensorTapeCodec.vectorBits words := rfl
/-- Physically counted and restored unary arity; it was never initialized as advice. -/
theorem acquired_count (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) :
    (done bits stride frequency inverse words).data (SemiprimeD1StackStaticTable.counter .count)=
      List.replicate words.length true := rfl
/-- ALL160 actual checker fields, including retained arithmetic caches/shadows,
are physically empty after their complete cleanup, rather than silently discarded. -/
theorem checker_clear (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits stride frequency inverse words).data (SemiprimeD1StackStaticTable.checker k)=[] := rfl
/-- Exact complete tape is actually present in the unique output role. -/
theorem output_table (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) :
    (done bits stride frequency inverse words).data (SemiprimeD1StackStaticTable.aux .output)=table bits stride frequency inverse words := rfl
end RiemannGaussian.SemiprimeD1StackPublicScaleTableExecution
