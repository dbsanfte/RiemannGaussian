/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
import RiemannGaussian.SemiprimeD1StackStaticTableBounds
/-! # Actual complete public input truth-table acquisition
The actual fixed116-role program scans its scope vector, copies only original
N/index template inputs, executes the original input checker at every real
assignment and writes the full original-order tape. No evaluator is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicInputTableExecution
open SemiprimeD1StackPublicInputTable SemiprimeD1StackPublicInputTableTrace
namespace G
export SemiprimeD1StackStaticTableExecution (outputTape)
end G
/-- Exact complete acquired tensor tape, specified at the real scope-vector arity. -/
def table (bits indexWord : List Bool) (words : List (List Bool)) : List Bool :=
  G.outputTape (answer bits indexWord) words
/-- All52 checker work roles clear; original template and scope/count survive. -/
def done (bits indexWord : List Bool) (words : List (List Bool)) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTableExecution.done static (inputTemplate bits indexWord) words (answer bits indexWord)
/-- Complete OWN actual source bound, including actual scope-byte acquisition. -/
def timeBound (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticTableBounds.runBound static (inputTemplate bits indexWord) words (budget bits indexWord)
/-- Whole actual source: original physical N/index/scope words ONLY. Generic
trace premises are instantiated by the frozen complete real input checker. -/
theorem source_run (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool)) :
    ∃t≤ timeBound bits indexWord words,SemiprimeD1StackCalls.run program t
      (initial bits indexWord (SemiprimeD1TensorTapeCodec.vectorBits words))=some (done bits indexWord words) :=
  SemiprimeD1StackStaticTableBounds.source_run_bounded static (inputTemplate bits indexWord)
    (template_raw bits indexWord) (answer bits indexWord) (budget bits indexWord) (actual_trace bits indexWord hb) words
/-- SAME genuine fixed finite machine, including all actual template copies,
recursive calls, checker arithmetic, cleanup and real return-stack cells. -/
noncomputable def tableInTime (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits indexWord (SemiprimeD1TensorTapeCodec.vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits indexWord words))) (timeBound bits indexWord words) :=
  SemiprimeD1StackStaticTableBounds.tableInTime static (inputTemplate bits indexWord)
    (template_raw bits indexWord) (answer bits indexWord) (budget bits indexWord) (actual_trace bits indexWord hb) words
/-- Every actual original checker-input template role survives byte for byte. -/
theorem retained_template (bits indexWord : List Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits indexWord words).data (SemiprimeD1StackStaticTable.template k)=inputTemplate bits indexWord k := rfl
/-- The physically acquired scope-ID vector survives unchanged. -/
theorem retained_scope (bits indexWord : List Bool) (words : List (List Bool)) :
    (done bits indexWord words).data (SemiprimeD1StackStaticTable.counter .bank)=
      SemiprimeD1TensorTapeCodec.vectorBits words := rfl
/-- Physically counted and restored unary arity; it was never initialized as advice. -/
theorem acquired_count (bits indexWord : List Bool) (words : List (List Bool)) :
    (done bits indexWord words).data (SemiprimeD1StackStaticTable.counter .count)=
      List.replicate words.length true := rfl
/-- ALL52 actual checker fields, including retained arithmetic caches/shadows,
are physically empty after their complete cleanup, rather than silently discarded. -/
theorem checker_clear (bits indexWord : List Bool) (words : List (List Bool)) (k : P.Stack) :
    (done bits indexWord words).data (SemiprimeD1StackStaticTable.checker k)=[] := rfl
/-- Exact complete tape is actually present in the unique output role. -/
theorem output_table (bits indexWord : List Bool) (words : List (List Bool)) :
    (done bits indexWord words).data (SemiprimeD1StackStaticTable.aux .output)=table bits indexWord words := rfl
end RiemannGaussian.SemiprimeD1StackPublicInputTableExecution
