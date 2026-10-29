/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardComponents
/-! # Whole real phase geometry and branch source from only original a/u/t -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardExecution
open SemiprimeD1StackPhaseGeometryGuard SemiprimeD1StackPhaseGeometryGuardComponents
open SemiprimeD1StackProcedureTrace
/-- Exact halt retains the complete acquired cache and caller u, with flags/returns clear. -/
def done (a u : Nat) (t : List Bool) : C.State Stack Label :=⟨none,none,none,result a u t,[]⟩
/-- Actual source halt includes the WHOLE paid geometry acquisition and both guard tests. -/
theorem source_run (a u : Nat) (t : List Bool) :
    ∃q≤ runBound a u t,SemiprimeD1StackCalls.run program q (initial a u t)=some (done a u t) :=by
  obtain ⟨q,hq,hr⟩:=source_trace a u t
  obtain ⟨finish,hf,hAt⟩:=hr [] (initial a u t) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result a u t) [] finish hAt
  exact ⟨q+1,hq,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- Genuine fixed finite machine, initialized with ONLY original physical metadata/index. -/
noncomputable def guardInTime (a u : Nat) (t : List Bool) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial a u t))
      (some (SemiprimeD1StackCalls.configuration (done a u t))) (runBound a u t) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (geometryStack (G.aux .exponent)) (aux .output) .start program
  let h:=source_run a u t
  let q:=Classical.choose h
  have hq:=Classical.choose_spec h
  exact ⟨⟨q,hq.2⟩,hq.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseGeometryGuardExecution
