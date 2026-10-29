/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateLoop
/-! # Actual whole two-input phase-coordinate acquisition
The source owns its initial preserving copy, literal output sentinel, all nested
reads/logging/drains, one final reverse and actual halt. It retains both inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateExecution
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinatePrimitives SemiprimeD1StackRecoveryCoordinateLoop
open SemiprimeD1StackRecoveryCoordinateEncoding SemiprimeD1StackProcedureTrace
/-- Actual bank copy and one physical output false, charged before any phase read. -/
theorem setup_run (phases key:List Bool):
    Runs program (5*phases.length+5) (.local .start) (initial phases key).data (.local .phaseLoop)
      (data key (words {phases:=phases,reader:=phases,output:=[false]})):=by
  rw [initial_data]
  have h0:=copy_run key (words {phases:=phases})
  rw [words_update] at h0
  change Runs program (5*phases.length+4) (.local .start)
    (data key (words {phases:=phases})) (.local .sentinel)
    (data key (words {phases:=phases,reader:=phases++[]})) at h0
  rw [List.append_nil] at h0
  have h1:=push_run (.local .sentinel) (.local .phaseLoop) .output false key (words {phases:=phases,reader:=phases}) rfl
  rw [words_update] at h1
  have h:=join h0 h1
  exact h
/-- Exact whole-source count before its real final halt. -/
def bodyTime (phases:Phases) (key:List Bool):Nat:=5*(tape phases).length+5+budget key phases []
/-- Exact complete physical21-role source clock, including every real call/return and halt. -/
def timeBound (phases:Phases) (key:List Bool):Nat:=bodyTime phases key+1
/-- Both actual original operands retained, exact nested child tape acquired, every other18 role empty. -/
def done (phases:Phases) (key:List Bool):C.State Stack Label:=
  ⟨none,none,none,data key (words {phases:=tape phases,output:=result phases key}),[]⟩
/-- Whole actual source trace from phase-block bytes and binary coordinate ONLY. -/
theorem source_trace (phases:Phases) (key:List Bool):
    Runs program (bodyTime phases key) (.local .start) (initial (tape phases) key).data
      (.local .done) (done phases key).data:=by
  have h0:=setup_run (tape phases) key
  have h1:=loop_run key (tape phases) phases [] [false]
  simp only [List.reverse_nil,List.nil_append,chunks_vector] at h1
  exact join h0 h1
/-- SAME finite physical program genuinely halts after acquiring all original-order phase coordinates. -/
theorem source_run (phases:Phases) (key:List Bool):
    SemiprimeD1StackCalls.run program (timeBound phases key) (initial (tape phases) key)=some (done phases key):=by
  obtain ⟨out,hr,ha⟩:=source_trace phases key [] (initial (tape phases) key) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (done phases key).data [] out ha
  rw [timeBound,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- Output is literally the nested coefficient column expected by RecoveryEntries. -/
theorem output_tape (phases:Phases) (key:List Bool):(done phases key).data output=result phases key:=rfl
/-- Original retained bank and raw binary coordinate survive; no private result or workspace is silently reset. -/
theorem result_bank (phases:Phases) (key:List Bool):
    (done phases key).data=Function.update (input (tape phases) key) output (result phases key):=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateExecution
