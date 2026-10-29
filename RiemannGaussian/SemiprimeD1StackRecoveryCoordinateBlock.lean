/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateFields
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCalls
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLogger
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
/-! # Real block-column step with paid parsing, binary lookup and logging
Every selected/default coefficient is framed before the two real reader result
words are physically drained. No prior phase or row history is scanned here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlock
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackRecoveryCoordinateFields
open SemiprimeD1StackRecoveryCoordinateCalls SemiprimeD1StackRecoveryCoordinateLogger
open SemiprimeD1StackRecoveryCoordinateEncoding SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Literal defaulting actual coefficient of one block, proof notation only. -/
def coefficient (key:List Bool) (block:List (List Bool)):List Bool:=
  (block[SemiprimeBitArithmetic.bitValue key]?).getD []
/-- Actual one-block source clock, independent of all prior histories. -/
def blockTime (key:List Bool) (block:List (List Bool)):Nat:=
  1+(8*(vectorBits block).length+8)+(X.timeBound block key+1)+
    (6*(coefficient key block).length+5)+1+(2*(chunk (coefficient key block)).length+3)+
    ((vectorBits block).length+1)+((coefficient key block).length+1)
/-- One actual block tag, parser, real binary lookup, preserving frame, reverse and two drains. -/
theorem block_run (key original outerReader rowHistory rowOutput history out:List Bool)
    (block:List (List Bool)) (rest:List (List (List Bool))):
    Runs program (blockTime key block) (.local .blockLoop)
      (data key (words {phases:=original,reader:=outerReader,blocks:=vectorBits (vectorBits block::rest.map vectorBits),rowHistory:=rowHistory,rowOutput:=rowOutput,history:=history,output:=out})) (.local .blockLoop)
      (data key (words {phases:=original,reader:=outerReader,blocks:=vectorBits (rest.map vectorBits),rowHistory:=(chunk (coefficient key block)).reverse++rowHistory,rowOutput:=rowOutput,history:=history,output:=out})):=by
  let v:Words:={phases:=original,reader:=outerReader,blocks:=vectorBits (vectorBits block::rest.map vectorBits),rowHistory:=rowHistory,rowOutput:=rowOutput,history:=history,output:=out}
  let afterTag:Words:={v with blocks:=SemiprimeSourceHistogramKeyBits.frame (vectorBits block) (vectorBits (rest.map vectorBits))}
  let parsed:Words:={v with blocks:=vectorBits (rest.map vectorBits),cache:=vectorBits block}
  let acquired:Words:={parsed with value:=coefficient key block}
  let framed:Words:={acquired with buffer:=SemiprimeSourceHistogramKeyBits.frame (coefficient key block) []}
  let tagged:Words:={framed with buffer:=chunk (coefficient key block)}
  let logged:Words:={acquired with rowHistory:=(chunk (coefficient key block)).reverse++rowHistory}
  have h0:=pop_run (.local .blockLoop) (.local .abort) (.local .rowReverse) (.local .blockField)
    .blocks key (words v) (vectorBits (vectorBits block::rest.map vectorBits)) rfl rfl
  change Runs program 1 (.local .blockLoop) (data key (words v)) (.local .blockField)
    (data key (Function.update (words v) .blocks afterTag.blocks)) at h0
  rw [words_update] at h0
  have h1:=field_read true key (words afterTag) (vectorBits block) (vectorBits (rest.map vectorBits)) rfl rfl rfl
  simp only [words_update,setWord] at h1
  have h2:=index_call key (words parsed) block rfl rfl
  rw [words_update] at h2
  have h3:=frame_call false key (words acquired)
  rw [words_update] at h3
  have h4:=push_run (.local .coefficientTag) (.local .coefficientReverse) .buffer true key (words framed) rfl
  rw [words_update] at h4
  have h5:=reverse_call 0 (.local .coefficientReverse) (.local .clearBlock) key (words tagged) rfl
  simp only [words_update,setWord] at h5
  have h6:=drain_run (.local .clearBlock) (.local .clearSelected) .cache key (words logged) (vectorBits block) rfl rfl
  rw [words_update] at h6
  have h7:=drain_run (.local .clearSelected) (.local .blockLoop) .value key
    (words {logged with cache:=[]}) (coefficient key block) rfl rfl
  rw [words_update] at h7
  have h:=join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlock
