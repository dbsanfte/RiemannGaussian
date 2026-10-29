/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlock
/-! # Whole physical block-vector column loop
A real final row-history reverse restores ascending block order. Empty phases
still acquire the literal empty vector and will be logged by the outer loop.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlocks
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackRecoveryCoordinateLogger
open SemiprimeD1StackRecoveryCoordinateBlock SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact same-program block-loop clock, including its single final real row reverse. -/
def budget (key:List Bool):List (List (List Bool))→List Bool→Nat
  | [],h=>1+(2*h.length+3)
  | block::rest,h=>blockTime key block+budget key rest ((chunk (coefficient key block)).reverse++h)
/-- The entire actual block scan acquires the defaulting column without an upstream coordinate-cache input. -/
theorem blocks_run (key original outerReader rowOutput history out:List Bool)
    (blocks:List (List (List Bool))) (rowHistory:List Bool):
    Runs program (budget key blocks rowHistory) (.local .blockLoop)
      (data key (words {phases:=original,reader:=outerReader,blocks:=vectorBits (blocks.map vectorBits),rowHistory:=rowHistory,rowOutput:=rowOutput,history:=history,output:=out})) (.local .phaseFrame)
      (data key (words {phases:=original,reader:=outerReader,rowOutput:=rowHistory.reverse++chunks (row key blocks)++rowOutput,history:=history,output:=out})):=by
  induction blocks generalizing rowHistory with
  | nil=>
    rw [budget]
    let v:Words:={phases:=original,reader:=outerReader,blocks:=[false],rowHistory:=rowHistory,rowOutput:=rowOutput,history:=history,output:=out}
    have h0:=pop_run (.local .blockLoop) (.local .abort) (.local .rowReverse) (.local .blockField)
      .blocks key (words v) [false] rfl rfl
    change Runs program 1 (.local .blockLoop) (data key (words v)) (.local .rowReverse)
      (data key (Function.update (words v) .blocks [])) at h0
    rw [words_update] at h0
    have h1:=reverse_call 1 (.local .rowReverse) (.local .phaseFrame) key
      (words {v with blocks:=[]}) rfl
    change Runs program (2*rowHistory.length+3) (.local .rowReverse)
      (data key (words {v with blocks:=[]})) (.local .phaseFrame)
      (data key (Function.update (Function.update (words {v with blocks:=[]}) .rowHistory []) .rowOutput (rowHistory.reverse++rowOutput))) at h1
    simp only [words_update,setWord] at h1
    have h:=join h0 h1
    simpa only [v,row,List.map_nil,chunks,List.foldr_nil,List.append_nil,vectorBits] using h
  | cons block blocks ih=>
    rw [budget]
    have h0:=block_run key original outerReader rowHistory rowOutput history out block blocks
    have h1:=ih ((chunk (coefficient key block)).reverse++rowHistory)
    have h:=join h0 h1
    simpa only [row,List.map_cons,chunks,List.foldr_cons,coefficient,List.reverse_append,List.reverse_reverse,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlocks
