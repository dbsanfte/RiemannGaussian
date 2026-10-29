/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePhase
/-! # Full original-order physical phase-bank column loop
A single real final reverse restores phase order. Every original phase appears,
including rejected phases whose actual block tape is the empty vector.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLoop
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackRecoveryCoordinateLogger
open SemiprimeD1StackRecoveryCoordinatePhase SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1StackProcedureTrace
/-- Exact same-program phase-loop clock including its single final real output reverse. -/
def budget (key:List Bool):Phases→List Bool→Nat
  | [],h=>1+(2*h.length+3)
  | blocks::rest,h=>phaseTime key blocks+budget key rest ((chunk (phaseRow key blocks)).reverse++h)
/-- Entire actual phase-bank scan, including all empty phase occurrences and the genuine final output reverse. -/
theorem loop_run (key original:List Bool) (phases:Phases) (history out:List Bool):
    Runs program (budget key phases history) (.local .phaseLoop)
      (data key (words {phases:=original,reader:=tape phases,history:=history,output:=out})) (.local .done)
      (data key (words {phases:=original,output:=history.reverse++chunks ((columns phases key).map SemiprimeD1TensorTapeCodec.vectorBits)++out})):=by
  induction phases generalizing history with
  | nil=>
    rw [budget]
    let v:Words:={phases:=original,reader:=[false],history:=history,output:=out}
    have h0:=pop_run (.local .phaseLoop) (.local .abort) (.local .finish) (.local .phaseField)
      .reader key (words v) [false] rfl rfl
    change Runs program 1 (.local .phaseLoop) (data key (words v)) (.local .finish)
      (data key (Function.update (words v) .reader [])) at h0
    rw [words_update] at h0
    have h1:=reverse_call 3 (.local .finish) (.local .done) key (words {v with reader:=[]}) rfl
    change Runs program (2*history.length+3) (.local .finish) (data key (words {v with reader:=[]})) (.local .done)
      (data key (Function.update (Function.update (words {v with reader:=[]}) .history []) .output (history.reverse++out))) at h1
    simp only [words_update,setWord] at h1
    have h:=join h0 h1
    simpa only [v,columns,List.map_nil,chunks,List.foldr_nil,List.append_nil,tape,SemiprimeD1TensorTapeCodec.vectorBits] using h
  | cons blocks phases ih=>
    rw [budget]
    have h0:=phase_run key original history out blocks phases
    have h1:=ih ((chunk (phaseRow key blocks)).reverse++history)
    have h:=join h0 h1
    simpa only [columns,List.map_cons,chunks,List.foldr_cons,phaseRow,List.reverse_append,List.reverse_reverse,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLoop
