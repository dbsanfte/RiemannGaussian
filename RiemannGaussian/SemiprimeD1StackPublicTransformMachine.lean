/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformTraceBudget
import RiemannGaussian.SemiprimeD1StackPublicTransformPublic
/-! # Genuine fixed finite-machine transform execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformMachine
open SemiprimeD1StackPublicTransform SemiprimeD1StackPublicTransformState
open SemiprimeD1StackPublicTransformExecution SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
/-- Actual clean halt, preserving branch-specific acquired caches. -/
def done (bits raw : List Bool) (second inverse : Bool) : C.State Stack Label :=
  ⟨none,none,none,data (finalParts bits raw second inverse),[]⟩
/-- Complete actual halt adds the literal final halt instruction to the trace. -/
theorem source_run (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t≤SemiprimeD1StackPublicTransformTraceBudget.timeBound bits raw second inverse+1,
      C.run program t (initial bits raw second inverse)=some (done bits raw second inverse) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicTransformTraceBudget.source_run_bounded bits raw second inverse hc hN
  obtain ⟨out,hout,ho⟩:=hr [] (initial bits raw second inverse) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (data (finalParts bits raw second inverse)) [] out ho
  refine ⟨t+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hout,Option.bind_some,hh]
  rfl
/-- Source execution certificate; witness selection is entirely proof-side. -/
noncomputable def sourceCheck (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw second inverse)
      (some (done bits raw second inverse))
      (SemiprimeD1StackPublicTransformTraceBudget.timeBound bits raw second inverse+1) := by
  let h:=source_run bits raw second inverse hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Same trace at the SAME step count in actual FinTM2, not a report primitive. -/
noncomputable def machineCheck (bits raw : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits raw second inverse))
      (some (SemiprimeD1StackCalls.configuration (done bits raw second inverse)))
      (SemiprimeD1StackPublicTransformTraceBudget.timeBound bits raw second inverse+1) :=
  SemiprimeD1StackCalls.evalsCorrect
    (.roots (.inl (SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))))
    (.aux .output) Label.start program _ _ _ (sourceCheck bits raw second inverse hc hN)
end RiemannGaussian.SemiprimeD1StackPublicTransformMachine
