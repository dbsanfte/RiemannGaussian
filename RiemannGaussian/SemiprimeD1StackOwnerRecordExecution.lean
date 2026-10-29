/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordComponents
/-! # Complete actual owner-table/scope/log trace -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 32768
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordExecution
open SemiprimeD1StackOwnerRecord SemiprimeD1StackOwnerRecordComponents
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)
/-- All computed-table work, actual ordinal conversion, framing, calls and halt. -/
def timeBound (key : List Bool) (rows : List (List Bool×Bool))
    (words : List (List Bool)) (hs : words.length≤2) : Nat :=
  TE.traceTime key rows words hs+SE.timeBound words+
    R.recordTime (S.result words) (table key rows [] words hs)+4
/-- Full physical join; the proof-side degree bound NEVER enters control or initial data. -/
theorem source_run (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    ∃t≤timeBound key rows words hs,C.run program t
      (initial key (records rows tail) (vectorBits words) hist out)=
      some (done key rows tail words hs hist out) := by
  have h0:=table_call key rows tail words hs hist out
  obtain ⟨b,hb,h1⟩:=scope_call key rows tail words hs hist out
  have h2:=record_call key rows tail words hs hist out
  have h:=SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _
    (SemiprimeD1StackProcedureTrace.runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2
  obtain ⟨finish,hr,hAt⟩:=h [] (initial key (records rows tail) (vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨((TE.traceTime key rows words hs+1)+(b+1))+
    (R.recordTime (S.result words) (table key rows tail words hs)+1)+1,?_,?_⟩
  · unfold timeBound
    have ht:table key rows tail words hs=table key rows [] words hs:=rfl
    rw [ht];omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    exact SemiprimeD1StackProcedureTrace.halt_run program (.inl .done) rfl
      (done key rows tail words hs hist out).data [] finish hAt
/-- The same trace on ONE genuine fixed finite machine and actual return alphabet. -/
noncomputable def ownerRecordInTime (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial key (records rows tail) (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done key rows tail words hs hist out)))
      (timeBound key rows words hs) := by
  apply SemiprimeD1StackCalls.evalsCorrect original output (.inl .start) program
  let h:=source_run key rows tail words hs hist out
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackOwnerRecordExecution
