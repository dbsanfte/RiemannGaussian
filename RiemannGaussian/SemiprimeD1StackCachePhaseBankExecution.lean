/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankLoop
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrepare
/-! # Whole four-input actual phase-bank acquisition
The sole fixed program copies both actual vectors, parses each real pair,
executes one real phase source, logs its actual output, cleans all236 roles,
checks both EOFs, reverses once and writes true status before the actual halt.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankExecution
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankEncoding SemiprimeD1StackCachePhaseBankLoop
open SemiprimeD1StackCachePhaseBankPrepare SemiprimeD1StackCachePhaseBankPrimitives
open SemiprimeD1StackProcedureTrace
attribute [local irreducible] SemiprimeD1StackRootPhaseFreshRecordsEncoding.result
  SemiprimeD1StackRootPhaseParametersEncoding.phases
  SemiprimeD1StackRootPhaseParametersEncoding.exponentValue
  SemiprimeD1StackRootPhaseParametersEncoding.levelsValue
  SemiprimeD1StackRootPhaseParametersEncoding.edgeValue
/-- Whole physical source cap: actual reader preparation, same-source replay caps and genuine final halt. -/
def timeBound (bits:List Bool) (requests:List (Request bits)):Nat:=
  prepareTime (references bits requests) (children requests)+replayBound bits requests []+1
/-- Complete SAMEprogram source trace, before the actual final halt. -/
theorem source_trace (bits:List Bool) (requests:List (Request bits)):
    ∃t,t+1 ≤timeBound bits requests ∧Runs program t (.local .start) (source bits requests).data
      (.local .done) (done bits requests).data:=by
  have h0:=prepare_run (R.result bits R.heap) (R.result bits (R.aux .counter)) (references bits requests) (children requests)
  obtain ⟨t,ht,h1⟩:=replay_run bits requests (references bits requests) (children requests) [] [false]
  simp only [List.reverse_nil,List.nil_append,chunks_vector] at h1
  have h:=join h0 h1
  exact ⟨_,by unfold timeBound;omega,h⟩
/-- Actual whole source from ONLY real heap/counter/reference-vector/child-vector words, with clear real return frames. -/
theorem source_run (bits:List Bool) (requests:List (Request bits)):
    ∃t ≤timeBound bits requests,SemiprimeD1StackCalls.run program t (source bits requests)=some (done bits requests):=by
  obtain ⟨t,ht,h⟩:=source_trace bits requests
  obtain ⟨out,hr,ha⟩:=h [] (source bits requests) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (done bits requests).data [] out ha
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- True status is a real singleton written AFTER the scratch's final use, not an input validity flag. -/
theorem status_true (bits:List Bool) (requests:List (Request bits)):(done bits requests).data status=[true]:=by
  simp only [done,Function.update_self]
/-- The acquired phase-bank vector contains every actual per-reference output in chronological source order. -/
theorem output_tape (bits:List Bool) (requests:List (Request bits)):(done bits requests).data output=result bits requests:=rfl
/-- Entire original reference/child vector words remain literally unchanged. -/
theorem inputs_retained (bits:List Bool) (requests:List (Request bits)):
    (done bits requests).data (aux .references)=references bits requests ∧
      (done bits requests).data (aux .children)=children requests:=⟨rfl,rfl⟩
/-- Generic final projection precedes substitution of any original-N heap/context. -/
theorem final_heap_counter (hp cn:List Bool) (w:Aux→List Bool) (flag:List Bool):
    (Function.update (data (P.input hp cn [] []) w) status flag) heap=hp ∧
      (Function.update (data (P.input hp cn [] []) w) status flag) counter=cn:=⟨rfl,rfl⟩
/-- Original physical heap/counter remain literally unchanged after every source and cleanup. -/
theorem heap_counter_retained (bits:List Bool) (requests:List (Request bits)):
    (done bits requests).data heap=R.result bits R.heap ∧
      (done bits requests).data counter=R.result bits (R.aux .counter):=by
  have h:=final_heap_counter (R.result bits R.heap) (R.result bits (R.aux .counter))
    (words {references:=references bits requests,children:=children requests,output:=result bits requests}) [true]
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankExecution
