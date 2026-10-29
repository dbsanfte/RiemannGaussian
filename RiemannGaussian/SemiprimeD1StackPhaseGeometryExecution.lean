/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryComponents
/-! # Actual complete halt from the two original physical operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryExecution
open SemiprimeD1StackPhaseGeometry SemiprimeD1StackPhaseGeometryComponents
open SemiprimeD1StackProcedureTrace
/-- Exact halt has no flags, internal returns or transient physical work. -/
def done (a t : List Bool) : C.State Stack Label :=⟨none,none,none,result a t,[]⟩
/-- Complete executed source on the SAME fixed finite program for every a/t word. -/
theorem source_run (a t : List Bool) :
    ∃q≤ runBound a t,SemiprimeD1StackCalls.run program q (initial a t)=some (done a t) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a t
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a t) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a t) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Actual finite-machine time certificate; only the two original physical fields
are initially nonempty. No computed geometry or comparison result is supplied. -/
noncomputable def geometryInTime (a t : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial a t))
      (some (SemiprimeD1StackCalls.configuration (done a t))) (runBound a t) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .exponent) (subStack .output) .start program
  let h:=source_run a t
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseGeometryExecution
