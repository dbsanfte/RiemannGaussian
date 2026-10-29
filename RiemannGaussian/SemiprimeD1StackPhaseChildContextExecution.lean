/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextComponents
/-! # Whole actual phase/header/context pipeline and exact P48-cache ready entry -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextExecution
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContextComponents SemiprimeD1StackProcedureTrace
/-- Exact done state retains actual phase/context caches, with flags and internal returns clear. -/
def done (a u edges : Nat) (t p : List Bool) (axes : List Nat) : C.State Stack Label :=
  ⟨none,none,none,result a u edges t p axes,[]⟩
/-- Own entire source clock is the actual P48 call plus the actual VALUE-charged ready pipeline. -/
def runBound (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=
  SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p+readyBound a u edges t p axes+1
/-- Whole original phase P48 source runs before any context rank/width supplier. -/
theorem phase_call (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    ∃q≤ SemiprimeD1StackPhaseWorkingPrecisionExecution.runBound a u edges t p+1,
      Runs program q .start (input a u edges t p (header axes)) .guard (S.waiting a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionExecution.source_run a u edges t p
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program phaseStack Label.phase phase_injective
    P.program .start (fun _=>rfl) .start .guard rfl q
    (SemiprimeD1StackPhaseWorkingPrecision.initial a u edges t p)
    (SemiprimeD1StackPhaseWorkingPrecisionExecution.done a u edges t p) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Direct ready continuation consumes the ACTUALLY acquired P48 cache, with no P/geometry rerun. -/
theorem ready_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ readyBound a u edges t p axes,
      SemiprimeD1StackCalls.run program q (ready a u edges t p (header axes))=some (done a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=ready_trace a u edges t p axes hp
  obtain ⟨finish,hf,hAt⟩:=hr [] (ready a u edges t p (header axes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p axes) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Whole original-only source acquires q/P/oldrank/newrank/width itself on ONE fixed program. -/
theorem source_trace (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q,q+1≤ runBound a u edges t p axes ∧ Runs program q .start (input a u edges t p (header axes))
      .done (result a u edges t p axes) :=by
  obtain ⟨b,hb,h0⟩:=phase_call a u edges t p axes
  obtain ⟨c,hc,h1⟩:=ready_trace a u edges t p axes hp
  exact ⟨b+c,by unfold runBound;omega,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
/-- Exact whole halt has no supplied dimension/rank/context/precision answer. -/
theorem source_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ runBound a u edges t p axes,
      SemiprimeD1StackCalls.run program q (initial a u edges t p (header axes))=some (done a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a u edges t p axes hp
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a u edges t p (header axes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p axes) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine finite-machine whole-source certificate includes all required numerical VALUE expansion. -/
noncomputable def contextInTime (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a u edges t p (header axes)))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p axes))) (runBound a u edges t p axes) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (oldStack J.axesCache) (childStack J.rankCache) .start program
  let h:=source_run a u edges t p axes hp
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
/-- SAME fixed machine continues from P48's actual acquired cache, with its own paid clock. -/
noncomputable def readyInTime (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (ready a u edges t p (header axes)))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p axes))) (readyBound a u edges t p axes) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (oldStack J.axesCache) (childStack J.rankCache) .start program
  let h:=ready_run a u edges t p axes hp
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseChildContextExecution
