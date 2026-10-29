/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecordComponents
/-! # Whole actual static-table and acquired-scope original record execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticRecordExecution
open SemiprimeD1StackStaticRecord SemiprimeD1StackStaticRecordComponents
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L)
/-- Complete same-source clock, including table compilation, actual ordinal
conversion, both consumed frames, all calls/returns and the final halt. -/
def timeBound (template : K→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (budget : Nat→Nat) : Nat :=
  SemiprimeD1StackStaticTableExecution.timeBound s template words answer budget+
    SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+
    R.recordTime (S.result words) (SemiprimeD1StackStaticTableExecution.outputTape answer words)+4
/-- Whole actual join. The checker contract is a proof about the fixed literal
checker; no answer predicate, arity, table or clock belongs to the program. -/
theorem source_run (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound s template words answer budget,C.run (program s) t
      (initial s template (vectorBits words) hist out)=some (done s template words answer hist out) := by
  obtain ⟨a,ha,h0⟩:=table_call s template hraw answer budget hc words hist out
  obtain ⟨b,hb,h1⟩:=scope_call s template words answer hist out
  have h2:=record_call s template words answer hist out
  have h:=SemiprimeD1StackProcedureTrace.runs_trans (program s) _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans (program s) _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hr,hAt⟩:=h [] (initial s template (vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨((a+1)+(b+1))+
    (R.recordTime (S.result words) (SemiprimeD1StackStaticTableExecution.outputTape answer words)+1)+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hAt with ⟨hpc,hd,hframes⟩
    change SemiprimeD1StackCalls.step (program s) finish=some (done s template words answer hist out)
    simp [SemiprimeD1StackCalls.step,hpc,program,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- The same trace on the genuine finite-control machine and real return stack. -/
noncomputable def recordInTime [Fintype L] (template : K→List Bool) (hraw : template s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s template answer budget)
    (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime (machine s).step
      (SemiprimeD1StackCalls.configuration (initial s template (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done s template words answer hist out)))
      (timeBound s template words answer budget) := by
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl .start) (program s)
  let h:=source_run s template hraw answer budget hc words hist out
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackStaticRecordExecution
