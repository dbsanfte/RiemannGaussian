/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceOuter
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSetup
import RiemannGaussian.SemiprimeD1StackSourceIncidenceFinish
/-! # Complete same-program prepared incidence-only query with its own actual whole trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceExecution
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceOuter SemiprimeD1StackSourceIncidenceSetup SemiprimeD1StackSourceIncidenceFinish
open SemiprimeD1StackProcedureTrace
/-- Whole own clock sums actual query saving, complete ordered scan, restoration, cleanup and literal final halt. -/
def runBound (i:Inputs) :Nat :=setupTime i+outerClock i i.rows []+finishTime i+1
/-- Complete source follows the SAME47-role finite program; no original/native query clock is transported. -/
theorem source_trace (i:Inputs) :
    ∃q,q+1 ≤ runBound i ∧ Runs program q .start (source i).data .done (result i) :=by
  have h0:=setup_run i
  obtain ⟨q,hq,h1⟩:=outer_run i i.rows []
  have he:outerResult i i.rows []=SemiprimeD1StackSourceIncidenceSpec.total i.ids i.square i.cube i.fourth i.rows:=rfl
  rw [he] at h1
  have h2:=finish_run i (SemiprimeD1StackSourceIncidenceSpec.total i.ids i.square i.cube i.fourth i.rows)
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold runBound
  omega
/-- Whole literal query includes its actual final halt, clearing both flags and all real return cells. -/
theorem source_run (i:Inputs) :
    ∃q ≤ runBound i,SemiprimeD1StackCalls.run program q (source i)=some (done i) :=by
  obtain ⟨q,hq,hr⟩:=source_trace i
  obtain ⟨finish,hf,hAt⟩:=hr [] (source i) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result i) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine fixed-machine certificate starts with the actual acquired multiple-word prepared bank.
Acquisition by the N-only occurrence/alphabet/environment caller is explicit, not an extra front-door claim. -/
noncomputable def queryInTime (i:Inputs) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (runBound i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .total) .start program
  let h:=source_run i
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceExecution
