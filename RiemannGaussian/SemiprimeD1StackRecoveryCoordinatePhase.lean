/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlocks
/-! # Complete actual per-phase column acquisition and occurrence-preserving log
The actual block payload comes from the parsed phase field. Every empty phase
still contributes one literal empty child row. No coordinate cache is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePhase
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackRecoveryCoordinateFields
open SemiprimeD1StackRecoveryCoordinateLogger SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace B
export SemiprimeD1StackRecoveryCoordinateBlocks (budget blocks_run)
end B
/-- Actual completed phase row, including its one physical false sentinel. -/
def phaseRow (key:List Bool) (blocks:List (List (List Bool))):List Bool:=vectorBits (row key blocks)
/-- Actual whole phase clock, independent of the prior outer phase history. -/
def phaseTime (key:List Bool) (blocks:List (List (List Bool))):Nat:=
  1+(8*(vectorBits (blocks.map vectorBits)).length+8)+1+B.budget key blocks []+
    (6*(phaseRow key blocks).length+5)+1+(2*(chunk (phaseRow key blocks)).length+3)+((phaseRow key blocks).length+1)
/-- Real phase parse, all physical block lookups, exact child-row framing, outer log and cleanup. -/
theorem phase_run (key original history out:List Bool) (blocks:List (List (List Bool))) (rest:Phases):
    Runs program (phaseTime key blocks) (.local .phaseLoop)
      (data key (words {phases:=original,reader:=tape (blocks::rest),history:=history,output:=out})) (.local .phaseLoop)
      (data key (words {phases:=original,reader:=tape rest,history:=(chunk (phaseRow key blocks)).reverse++history,output:=out})):=by
  let v:Words:={phases:=original,reader:=tape (blocks::rest),history:=history,output:=out}
  let afterTag:Words:={v with reader:=SemiprimeSourceHistogramKeyBits.frame (vectorBits (blocks.map vectorBits)) (tape rest)}
  let parsed:Words:={v with reader:=tape rest,blocks:=vectorBits (blocks.map vectorBits)}
  let acquired:Words:={v with reader:=tape rest,rowOutput:=phaseRow key blocks}
  let framed:Words:={acquired with buffer:=SemiprimeSourceHistogramKeyBits.frame (phaseRow key blocks) []}
  let tagged:Words:={framed with buffer:=chunk (phaseRow key blocks)}
  let logged:Words:={acquired with history:=(chunk (phaseRow key blocks)).reverse++history}
  have h0:=pop_run (.local .phaseLoop) (.local .abort) (.local .finish) (.local .phaseField)
    .reader key (words v) (tape (blocks::rest)) rfl rfl
  change Runs program 1 (.local .phaseLoop) (data key (words v)) (.local .phaseField)
    (data key (Function.update (words v) .reader afterTag.reader)) at h0
  rw [words_update] at h0
  have h1:=field_read false key (words afterTag) (vectorBits (blocks.map vectorBits)) (tape rest) rfl rfl rfl
  simp only [words_update,setWord] at h1
  have h2:=push_run (.local .rowSeed) (.local .blockLoop) .rowOutput false key (words parsed) rfl
  rw [words_update] at h2
  have h3:=B.blocks_run key original (tape rest) [false] history out blocks []
  simp only [List.reverse_nil,List.nil_append,chunks_vector] at h3
  have h4:=frame_call true key (words acquired)
  rw [words_update] at h4
  have h5:=push_run (.local .phaseTag) (.local .phaseReverse) .buffer true key (words framed) rfl
  rw [words_update] at h5
  have h6:=reverse_call 2 (.local .phaseReverse) (.local .clearRow) key (words tagged) rfl
  simp only [words_update,setWord] at h6
  have h7:=drain_run (.local .clearRow) (.local .phaseLoop) .rowOutput key (words logged) (phaseRow key blocks) rfl rfl
  rw [words_update] at h7
  have h:=join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePhase
