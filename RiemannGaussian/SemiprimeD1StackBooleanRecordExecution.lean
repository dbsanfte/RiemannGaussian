/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanRecordComponents
/-! # Whole actual Boolean table and acquired-scope original record execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanRecordExecution
open SemiprimeD1StackBooleanRecord SemiprimeD1StackBooleanRecordComponents
/-- Every actual acquisition, framing bit, call/return and final halt is retained. -/
def timeBound (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool)) : Nat :=
  (table mode).length+1+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    R.recordTime (S.result words) (table mode)+4
/-- The closed physical join has no table, arity, decoded port, verdict or clock input. -/
theorem source_run (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound mode words,C.run program t
      (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=
      some (done mode words hist out) := by
  have h0:=table_call mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out
  obtain ⟨b,hb,h1⟩:=scope_call mode words hist out
  have h2:=record_call mode words hist out
  have h:=SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hr,hAt⟩:=h [] (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨(((table mode).length+2)+(b+1))+(R.recordTime (S.result words) (table mode)+1)+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hAt with ⟨hpc,hd,hframes⟩
    change SemiprimeD1StackCalls.step program finish=some (done mode words hist out)
    simp [SemiprimeD1StackCalls.step,hpc,program,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- Same source trace on the genuine fixed finite-control machine and real return alphabet. -/
noncomputable def booleanRecordInTime (mode : SemiprimeD1StackBooleanEntry.Mode)
    (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime (machine mode).step
      (SemiprimeD1StackCalls.configuration (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done mode words hist out))) (timeBound mode words) := by
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl (.start mode)) program
  let h:=source_run mode words hist out
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackBooleanRecordExecution
