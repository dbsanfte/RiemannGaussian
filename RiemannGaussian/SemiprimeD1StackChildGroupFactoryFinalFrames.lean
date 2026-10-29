/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Six literal final output frames
Each frame is emitted by its real preserving primitive, including its scratch
restoration and return. The six actual source words remain retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinalFrames
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace F
export SemiprimeSourceHistogramKeyBits (frame)
end F
/-- Fixed physical source addresses, determined before every input. -/
def wordRole (i:Fin 6):Stack:=match i.val with
  | 0=>aux .oldEndpoints
  | 1=>aux .orders
  | 2=>aux .leftPorts
  | 3=>aux .buckets
  | 4=>aux .endpoints
  | _=>aux .activation
/-- Actual successive output bytes; this is proof notation, never a runtime value. -/
def buffer (before:Stack→List Bool):Nat→List Bool
  | 0=>before (aux .output)
  | n+1=>F.frame (before (wordRole ⟨n%6,Nat.mod_lt _ (by decide)⟩)) (buffer before n)
/-- Full physical bank after the first n real frames. -/
def stage (before:Stack→List Bool) (n:Nat):Stack→List Bool:=
  Function.update before (aux .output) (buffer before n)
/-- Actual bank after all six literal preserving frame calls. -/
def result (before:Stack→List Bool):Stack→List Bool:=stage before 6
/-- Own exact primitive clocks for all six complete preserving frames. -/
def timeBound (before:Stack→List Bool):Nat:=
  (6*(before (aux .oldEndpoints)).length+5)+(6*(before (aux .orders)).length+5)+(6*(before (aux .leftPorts)).length+5)+(6*(before (aux .buckets)).length+5)+(6*(before (aux .endpoints)).length+5)+(6*(before (aux .activation)).length+5)
/-- Whole actual six-frame output source. -/
theorem source_trace (before:Stack→List Bool) (hc:before (aux .copyScratch)=[]):
    Runs program (timeBound before) (.local 15 7) before (.local 15 13) (result before):=by
  have h0:=frame_call 19 (.local 15 7) (.local 15 8) rfl before
    (before (aux .oldEndpoints)) (buffer before 0)
    (by rfl)
    (by rfl)
    (by exact hc)
  change Runs program _ _ before _ (stage before 1) at h0
  have h1:=frame_call 20 (.local 15 8) (.local 15 9) rfl (stage before 1)
    (before (aux .orders)) (buffer before 1)
    (by simp [stage,frameStack,framePorts,aux])
    (by exact Function.update_self _ _ _)
    (by simpa [stage,frameStack,framePorts,aux] using hc)
  change Runs program _ _ (stage before 1) _ (Function.update (stage before 1) (aux .output) (buffer before 2)) at h1
  have h1':Runs program (6*(before (aux .orders)).length+5) (.local 15 8) (stage before 1) (.local 15 9) (stage before 2):=by
    simpa only [stage,Function.update_idem] using h1
  have h2:=frame_call 21 (.local 15 9) (.local 15 10) rfl (stage before 2)
    (before (aux .leftPorts)) (buffer before 2)
    (by simp [stage,frameStack,framePorts,aux])
    (by exact Function.update_self _ _ _)
    (by simpa [stage,frameStack,framePorts,aux] using hc)
  change Runs program _ _ (stage before 2) _ (Function.update (stage before 2) (aux .output) (buffer before 3)) at h2
  have h2':Runs program (6*(before (aux .leftPorts)).length+5) (.local 15 9) (stage before 2) (.local 15 10) (stage before 3):=by
    simpa only [stage,Function.update_idem] using h2
  have h3:=frame_call 22 (.local 15 10) (.local 15 11) rfl (stage before 3)
    (before (aux .buckets)) (buffer before 3)
    (by simp [stage,frameStack,framePorts,aux])
    (by exact Function.update_self _ _ _)
    (by simpa [stage,frameStack,framePorts,aux] using hc)
  change Runs program _ _ (stage before 3) _ (Function.update (stage before 3) (aux .output) (buffer before 4)) at h3
  have h3':Runs program (6*(before (aux .buckets)).length+5) (.local 15 10) (stage before 3) (.local 15 11) (stage before 4):=by
    simpa only [stage,Function.update_idem] using h3
  have h4:=frame_call 23 (.local 15 11) (.local 15 12) rfl (stage before 4)
    (before (aux .endpoints)) (buffer before 4)
    (by simp [stage,frameStack,framePorts,aux])
    (by exact Function.update_self _ _ _)
    (by simpa [stage,frameStack,framePorts,aux] using hc)
  change Runs program _ _ (stage before 4) _ (Function.update (stage before 4) (aux .output) (buffer before 5)) at h4
  have h4':Runs program (6*(before (aux .endpoints)).length+5) (.local 15 11) (stage before 4) (.local 15 12) (stage before 5):=by
    simpa only [stage,Function.update_idem] using h4
  have h5:=frame_call 24 (.local 15 12) (.local 15 13) rfl (stage before 5)
    (before (aux .activation)) (buffer before 5)
    (by simp [stage,frameStack,framePorts,aux])
    (by exact Function.update_self _ _ _)
    (by simpa [stage,frameStack,framePorts,aux] using hc)
  change Runs program _ _ (stage before 5) _ (Function.update (stage before 5) (aux .output) (buffer before 6)) at h5
  have h5':Runs program (6*(before (aux .activation)).length+5) (.local 15 12) (stage before 5) (.local 15 13) (stage before 6):=by
    simpa only [stage,Function.update_idem] using h5
  have h:=join h0 (join h1' (join h2' (join h3' (join h4' h5'))))
  simpa only [timeBound,result,Nat.add_assoc] using h
/-- All nonoutput physical words, including all six sources, are preserved. -/
theorem result_other (before:Stack→List Bool) (k:Stack) (hk:k≠aux .output):
    result before k=before k:=Function.update_of_ne hk _ _
/-- Exact literal six-field output codec, with any original output tail retained. -/
theorem result_output (before:Stack→List Bool):
    result before (aux .output)=
      F.frame (before (aux .activation)) (F.frame (before (aux .endpoints))
        (F.frame (before (aux .buckets)) (F.frame (before (aux .leftPorts))
          (F.frame (before (aux .orders)) (F.frame (before (aux .oldEndpoints)) (before (aux .output))))))):=rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinalFrames
