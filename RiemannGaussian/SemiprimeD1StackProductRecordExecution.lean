/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductRecordComponents
/-! # Whole actual original-N and acquired-scope product record execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductRecordExecution
open SemiprimeD1StackProductRecord SemiprimeD1StackProductRecordComponents
/-- Every actual acquisition, framing bit, call/return and final halt is retained. -/
def timeBound (bits : List Bool) (words : List (List Bool)) : Nat :=
  SemiprimeD1StackProductTableExecution.timeBound bits+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    R.recordTime (S.result words) (table bits)+4
/-- The closed physical join has no table, arity, decoded port, verdict or clock input. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound bits words,C.run program t
      (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=
      some (done bits words hist out) := by
  obtain ⟨a,ha,h0⟩:=table_call bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out hb
  obtain ⟨b,hb,h1⟩:=scope_call bits words hist out
  have h2:=record_call bits words hist out
  have h:=SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hr,hAt⟩:=h [] (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨((a+1)+(b+1))+(R.recordTime (S.result words) (table bits)+1)+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hAt with ⟨hpc,hd,hframes⟩
    change SemiprimeD1StackCalls.step program finish=some (done bits words hist out)
    simp [SemiprimeD1StackCalls.step,hpc,program,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- Same source trace on the genuine fixed finite-control machine and real return alphabet. -/
noncomputable def productRecordInTime (bits : List Bool) (hb : bits≠[])
    (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done bits words hist out))) (timeBound bits words) := by
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl .start) program
  let h:=source_run bits hb words hist out
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackProductRecordExecution
