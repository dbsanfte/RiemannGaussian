/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionComponents
/-! # Whole original working-precision source and acquired-cache ready entry -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionExecution
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionComponents
open SemiprimeD1StackProcedureTrace
/-- Exact actual halt has retained metadata, BINARY D/P and clear flags/internal returns. -/
def done (a u edges : Nat) (t p : List Bool) : C.State Stack Label :=⟨none,none,none,result a u edges t p,[]⟩
/-- Whole fixed polynomial includes actual metadata acquisition and all binary work. -/
def runBound (a u edges : Nat) (t p : List Bool) : Nat :=1000000000000*(edges+a+u+t.length+p.length+1)^4
/-- Ready initialization is exactly the actual37-role cache and eleven empty binary fields. -/
theorem ready_data (a u edges : Nat) (t p : List Bool) :
    (ready a u edges t p).data=clean a u edges t p :=by
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Genuine whole real call obtains h/q/r/delta/order/guard from ONLY original operands. -/
theorem metadata_call (a u edges : Nat) (t p : List Bool) :
    ∃q≤ SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.runBound a u edges t p+1,
      Runs program q .start (input a u edges t p) .branch (clean a u edges t p) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.source_run a u edges t p
  refine ⟨q+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program metadataStack Label.metadata metadata_injective
    M.program .start (fun _=>rfl) .start .branch rfl q
    (SemiprimeD1StackPhaseWorkingPrecisionMetadata.initial a u edges t p)
    (SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.done a u edges t p) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
/-- Complete halt from the ACTUALLY acquired cache, with NO repeated metadata/geometry call. -/
theorem ready_run (a u edges : Nat) (t p : List Bool) :
    ∃q≤ readyBound a u edges t p,SemiprimeD1StackCalls.run program q (ready a u edges t p)=some (done a u edges t p) :=by
  obtain ⟨q,hq,hr⟩:=ready_trace a u edges t p
  obtain ⟨finish,hf,hAt⟩:=hr [] (ready a u edges t p) ⟨rfl,ready_data a u edges t p,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- ENTIRE paid original-input precision pipeline executes on ONE fixed finite source. -/
theorem source_trace (a u edges : Nat) (t p : List Bool) :
    ∃q,q+1≤ runBound a u edges t p ∧ Runs program q .start (input a u edges t p) .done (result a u edges t p) :=by
  obtain ⟨b,hb,h0⟩:=metadata_call a u edges t p
  obtain ⟨c,hc,h1⟩:=ready_trace a u edges t p
  refine ⟨b+c,?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  let I:=edges+a+u+t.length+p.length+1
  have hI:1≤ I^4:=by
    have hpos:0<I^4:=by dsimp [I];positivity
    omega
  have hp:I^2≤ I^4:=by
    calc
      _≤(I^2)^2:=Nat.le_pow (by decide : 0<(2:Nat))
      _=_:=by ring
  change b≤1000000*I^2+1 at hb
  change c+1≤1000000000*I^4 at hc
  change _≤1000000000000*I^4
  omega
/-- Whole actual source halts from only original physical a/u/M and binary t/p words. -/
theorem source_run (a u edges : Nat) (t p : List Bool) :
    ∃q≤ runBound a u edges t p,SemiprimeD1StackCalls.run program q (initial a u edges t p)=some (done a u edges t p) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a u edges t p
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a u edges t p) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u edges t p) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine finite-machine whole-source certificate, with original precision kept binary. -/
noncomputable def precisionInTime (a u edges : Nat) (t p : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial a u edges t p))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p))) (runBound a u edges t p) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (metadataStack (M.aux .edges)) (aux .output) .start program
  let h:=source_run a u edges t p
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
/-- Genuine SAME-machine ready continuation, with its OWN paid binary-only polynomial. -/
noncomputable def readyInTime (a u edges : Nat) (t p : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (ready a u edges t p))
      (some (SemiprimeD1StackCalls.configuration (done a u edges t p))) (readyBound a u edges t p) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (metadataStack (M.aux .edges)) (aux .output) .start program
  let h:=ready_run a u edges t p
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionExecution
