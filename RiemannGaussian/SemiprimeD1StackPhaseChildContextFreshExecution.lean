/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshComponents
/-! # Whole fresh-generator machine and two exact acquired-cache continuation entries -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshExecution
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackPhaseChildContextFreshComponents
open SemiprimeD1StackPhaseChildContextFreshPrimitives SemiprimeD1StackProcedureTrace
/-- Exact halt retains every80-role acquired context cache and clears all allocator work. -/
def done (a u edges : Nat) (t p : List Bool) (axes : List Nat) : C.State Stack Label :=⟨none,none,none,result a u edges t p axes,[]⟩
/-- Own whole clock sums actual original phase/context and allocation calls. -/
def runBound (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=
  SemiprimeD1StackPhaseChildContextExecution.runBound a u edges t p axes+readyBound a u edges t axes+1
/-- P48-ready clock pays context/header suppliers and fresh allocation, with no P48 rerun. -/
def phaseReadyBound (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=
  SemiprimeD1StackPhaseChildContextComponents.readyBound a u edges t p axes+readyBound a u edges t axes+1
/-- Actual whole header source runs from original fields; no rank/precision answer enters this call. -/
theorem context_call (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ SemiprimeD1StackPhaseChildContextExecution.runBound a u edges t p axes+1,
      Runs program q .start (input a u edges t p (Old.header axes)) .guard
        (store (cache a u edges t p axes) [] [] [] [] []) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseChildContextExecution.source_run a u edges t p axes hp
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program contextStack Label.context context_injective
    H.program .start (fun _=>rfl) .start .guard rfl q
    (H.initial a u edges t p (Old.header axes)) (SemiprimeD1StackPhaseChildContextExecution.done a u edges t p axes) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Literal ready call starts at the actual P48 cache and reuses ALL48 words unchanged. -/
theorem phase_ready_call (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ SemiprimeD1StackPhaseChildContextComponents.readyBound a u edges t p axes+1,
      Runs program q .phaseReady (phaseReady a u edges t p (Old.header axes)).data .guard
        (store (cache a u edges t p axes) [] [] [] [] []) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseChildContextExecution.ready_run a u edges t p axes hp
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program contextStack Label.context context_injective
    H.program .guard (fun _=>rfl) .phaseReady .guard rfl q
    (H.ready a u edges t p (Old.header axes)) (SemiprimeD1StackPhaseChildContextExecution.done a u edges t p axes) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Direct acquired-context continuation has its OWN halt and complete byte-allocation clock. -/
theorem ready_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    ∃q≤ readyBound a u edges t axes,
      SemiprimeD1StackCalls.run program q (ready a u edges t p axes)=some (done a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=ready_trace a u edges t p axes
  obtain ⟨finish,hf,hAt⟩:=hr [] (ready a u edges t p axes) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p axes) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Full original source followed by physical fresh allocation, preserving every real outer return. -/
theorem source_trace (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q,q+1≤ runBound a u edges t p axes ∧ Runs program q .start (input a u edges t p (Old.header axes)) .done (result a u edges t p axes) :=by
  obtain ⟨b,hb,h0⟩:=context_call a u edges t p axes hp
  obtain ⟨c,hc,h1⟩:=ready_trace a u edges t p axes
  exact ⟨b+c,by unfold runBound;omega,join h0 h1⟩
/-- Whole fixed machine produces the entire original fresh vector, with all work clear at halt. -/
theorem source_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ runBound a u edges t p axes,
      SemiprimeD1StackCalls.run program q (initial a u edges t p (Old.header axes))=some (done a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a u edges t p axes hp
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a u edges t p (Old.header axes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p axes) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- SAME program starts from actual P48cache, acquires both context caches, and allocates fresh coefficients. -/
theorem phase_ready_trace (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q,q+1≤ phaseReadyBound a u edges t p axes ∧ Runs program q .phaseReady
      (phaseReady a u edges t p (Old.header axes)).data .done (result a u edges t p axes) :=by
  obtain ⟨b,hb,h0⟩:=phase_ready_call a u edges t p axes hp
  obtain ⟨c,hc,h1⟩:=ready_trace a u edges t p axes
  exact ⟨b+c,by unfold phaseReadyBound;omega,join h0 h1⟩
/-- Actual readyP48 halt repeats no geometry/metadata/P acquisition and takes no rank answer. -/
theorem phase_ready_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤ phaseReadyBound a u edges t p axes,
      SemiprimeD1StackCalls.run program q (phaseReady a u edges t p (Old.header axes))=some (done a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=phase_ready_trace a u edges t p axes hp
  obtain ⟨finish,hf,hAt⟩:=hr [] (phaseReady a u edges t p (Old.header axes)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p axes) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine original-only finite-machine certificate for the full coefficient-vector acquisition. -/
noncomputable def freshInTime (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial a u edges t p (Old.header axes)))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p axes))) (runBound a u edges t p axes) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program
  let h:=source_run a u edges t p axes hp
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
/-- Genuine same-machine P48-cache certificate includes both context and fresh-value expansion. -/
noncomputable def phaseReadyInTime (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (phaseReady a u edges t p (Old.header axes)))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p axes))) (phaseReadyBound a u edges t p axes) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (contextStack (H.oldStack H.J.axesCache)) (aux .output) .start program
  let h:=phase_ready_run a u edges t p axes hp
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshExecution
