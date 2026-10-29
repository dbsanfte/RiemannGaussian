/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecordLoad
/-! # Actual descriptor loader, whole static-table source and record execution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecordExecution
open SemiprimeD1StackDescriptorRecord SemiprimeD1StackDescriptorRecordLoadView
open SemiprimeD1StackDescriptorRecordLoad SemiprimeD1StackProcedureTrace
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
omit [DecidableEq K] [Fintype K] in
/-- The proved loaded store is exactly the actual component initialization,
with every unselected metadata/assignment/result/cache field empty. -/
theorem loaded_initial (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (bank hist out : List Bool) :
    loaded sourceMap (initial s oldTemplate fields bank hist out).data=afterLoad s sourceMap fields bank hist out := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
    · rfl
  · rfl
/-- Actual input inventory and every old template byte contribute to loader time. -/
def prepareBound (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (bank hist out : List Bool) : Nat :=
  s.roles.length*loadUnit (initial s oldTemplate fields bank hist out).data+2
/-- The finite template loader makes real copies and a real return for every
static position, including all empty/unselected private and alias fields. -/
theorem prepare_call (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (bank hist out : List Bool) :
    ∃t≤prepareBound s oldTemplate fields bank hist out,Runs (program s sourceMap) t (.inl .start)
      (initial s oldTemplate fields bank hist out).data (.inl .record) (afterLoad s sourceMap fields bank hist out) := by
  obtain ⟨t,ht,hr⟩:=load_returns s sourceMap (initial s oldTemplate fields bank hist out).data rfl
  have h:=SemiprimeD1StackProcedureReturns.call (program s sourceMap) t (.inl .start) (.inl (.load 0))
    (.inl .record) _ _ rfl hr
  rw [loaded_initial] at h
  exact ⟨1+t,by unfold prepareBound;omega,h⟩
/-- The actual static-record call consumes its acquired source outputs and
retains all six original physical descriptor/N fields and loader scratch. -/
theorem record_call (fields : Fin 6→List Bool) (hraw : selected sourceMap fields s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat) (hc : CheckerTrace s (selected sourceMap fields) answer budget)
    (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤SemiprimeD1StackStaticRecordExecution.timeBound s (selected sourceMap fields) words answer budget,
      Runs (program s sourceMap) (t+1) (.inl .record) (afterLoad s sourceMap fields (vectorBits words) hist out)
        (.inl .done) (done s sourceMap fields words answer hist out).data := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackStaticRecordExecution.source_run s (selected sourceMap fields) hraw
    answer budget hc words hist out
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call (program s sourceMap) recordStack recordLabel
    Sum.inl_injective (R.program s) (.inl .start) (fun _=>rfl) (.inl .record) (.inl .done) rfl t
    (SemiprimeD1StackStaticRecord.initial s (selected sourceMap fields) (vectorBits words) hist out)
    (SemiprimeD1StackStaticRecord.done s (selected sourceMap fields) words answer hist out)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- Full same-source clock: charged dirty-template drain/load, actual whole
table source, scope serialization, consuming logger, all calls and final halt. -/
def timeBound (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (budget : Nat→Nat) (hist out : List Bool) : Nat :=
  prepareBound s oldTemplate fields (vectorBits words) hist out+
    SemiprimeD1StackStaticRecordExecution.timeBound s (selected sourceMap fields) words answer budget+2
/-- Entire real descriptor-to-record execution. Every mathematical checker
contract is a correctness proof for a checker fixed before original N. -/
theorem source_run (oldTemplate : K→List Bool) (fields : Fin 6→List Bool)
    (hraw : selected sourceMap fields s.raw=[]) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (selected sourceMap fields) answer budget) (words : List (List Bool)) (hist out : List Bool) :
    ∃t≤timeBound s sourceMap oldTemplate fields words answer budget hist out,C.run (program s sourceMap) t
      (initial s oldTemplate fields (vectorBits words) hist out)=some (done s sourceMap fields words answer hist out) := by
  obtain ⟨a,ha,h0⟩:=prepare_call s sourceMap oldTemplate fields (vectorBits words) hist out
  obtain ⟨b,hb,h1⟩:=record_call s sourceMap fields hraw answer budget hc words hist out
  have h:=runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hr,hAt⟩:=h [] (initial s oldTemplate fields (vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨a+(b+1)+1,by unfold timeBound;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hAt with ⟨hpc,hd,hframes⟩
  change SemiprimeD1StackCalls.step (program s sourceMap) finish=some (done s sourceMap fields words answer hist out)
  simp [SemiprimeD1StackCalls.step,hpc,program,SemiprimeD1StackCalls.execute,hd,hframes,done]
/-- Complete trace of the same genuine finite machine and actual return cells. -/
noncomputable def recordInTime [Fintype L] (oldTemplate : K→List Bool) (fields : Fin 6→List Bool)
    (hraw : selected sourceMap fields s.raw=[]) (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (selected sourceMap fields) answer budget) (words : List (List Bool)) (hist out : List Bool) :
    StateTransition.EvalsToInTime (machine s sourceMap).step
      (SemiprimeD1StackCalls.configuration (initial s oldTemplate fields (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done s sourceMap fields words answer hist out)))
      (timeBound s sourceMap oldTemplate fields words answer budget hist out) := by
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl .start) (program s sourceMap)
  let h:=source_run s sourceMap oldTemplate fields hraw answer budget hc words hist out
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩
end RiemannGaussian.SemiprimeD1StackDescriptorRecordExecution
