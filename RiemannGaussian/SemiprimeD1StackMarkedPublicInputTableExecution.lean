/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableTrace
import RiemannGaussian.SemiprimeD1StackStaticWordTableBounds
/-! # Entire actual marked input-table source, with no table or arity input -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableExecution
open SemiprimeD1StackMarkedPublicInputTable SemiprimeD1StackMarkedPublicInputTableTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
namespace G
export SemiprimeD1StackStaticWordTableExecution (outputTape result)
end G
/-- Every output leaf is one actual compact NONNEGATIVE coefficient word. -/
def outputTape (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) : List Bool :=
  G.outputTape (answer bits indexWord side) words
/-- Exact stopped whole144-role bank, including retained input template and scope/count cache. -/
def result (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) : Stack → List Bool :=
  G.result (inputTemplate bits indexWord side) words (answer bits indexWord side)
/-- Actual halt state; every live66 checker field and all DFS work are empty. -/
def done (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) :
    SemiprimeD1StackCalls.State Stack Label :=
  ⟨none,none,none,result bits indexWord side words,[]⟩
/-- Complete own source clock, summing actual count, DFS, source, framing and final reverse caps. -/
def runBound (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackStaticWordTableBounds.runBound static (inputTemplate bits indexWord side) words (budget bits indexWord)
/-- SAME literal full table source runs from original physical template/scope only. -/
theorem source_run (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) (hb : bits≠[]) :
    ∃ t ≤ runBound bits indexWord side words,
      SemiprimeD1StackCalls.run program t (initial bits indexWord side (vectorBits words))=
        some (done bits indexWord side words) :=
  SemiprimeD1StackStaticWordTableBounds.source_run_bounded static (inputTemplate bits indexWord side)
    (template_raw bits indexWord side) (answer bits indexWord side) (budget bits indexWord)
    (actual_trace bits indexWord side hb) words
/-- Every144-role compiled prefix includes both66 banks, the actual counter,
all DFS fields, the temporarily dirty compaction shadow and all real returns. -/
theorem machine_prefix_cells (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) (hb : bits≠[])
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q => q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits indexWord side (vectorBits words))))=some cfg) :
    (∑ k : Stack, (cfg.stk (some k)).length)+(cfg.stk none).length ≤
      145*(SemiprimeD1StackStaticWordTableSpec.inputBytes (inputTemplate bits indexWord side)+
        (vectorBits words).length+runBound bits indexWord side words+1) := by
  have hh := SemiprimeD1StackStaticWordTableBounds.machine_prefix_cells static
    (inputTemplate bits indexWord side) (template_raw bits indexWord side)
    (answer bits indexWord side) (budget bits indexWord) (actual_trace bits indexWord side hb) words fuel cfg hr
  norm_num only [SemiprimeD1StackMarkedPublicInputCompact.stack_card,runBound] at hh ⊢
  exact hh
/-- Actual compact coefficient byte result, with no reordering of assignments. -/
theorem output_bytes (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) :
    (done bits indexWord side words).data (SemiprimeD1StackStaticWordTable.aux .output)=
      outputTape bits indexWord side words := by
  change Function.update (SemiprimeD1StackStaticWordTable.data (inputTemplate bits indexWord side)
    (vectorBits words) words.length [] []) (SemiprimeD1StackStaticWordTable.aux .output)
    (outputTape bits indexWord side words) (SemiprimeD1StackStaticWordTable.aux .output)=_
  exact Function.update_self _ _ _
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableExecution

