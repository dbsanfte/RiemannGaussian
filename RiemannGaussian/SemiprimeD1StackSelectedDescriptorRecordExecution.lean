/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordComponents
/-! # Complete actual finite selector to metadata template to original row join -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordExecution
open SemiprimeD1StackSelectedDescriptorRecord SemiprimeD1StackSelectedDescriptorRecordComponents
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackStaticTableSpec (CheckerTrace)
open SemiprimeD1TensorTapeCodec (vectorBits)
variable {K L : Type} [DecidableEq K] [Fintype K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Every source copy/pop/push, gate peek, metadata load, actual whole table,
ordinal serialization, consuming logger, all real calls/returns and final halt. -/
def timeBound (oldTemplate : K→List Bool) (raw : Fin 6→List Bool) (second inverse : Bool)
    (words : List (List Bool)) (answer : List Bool→Bool) (budget : Nat→Nat)
    (oldStage oldInverse hist out : List Bool) : Nat :=
  SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+
    SemiprimeD1StackDescriptorRecordExecution.timeBound s sourceMap oldTemplate (fields raw [second] [inverse])
      words answer budget hist out+4
/-- Complete actual prepared bridge from six physical original fields and a
physical binary scope. No selector, template, table or verdict is supplied. -/
theorem source_run (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2])) answer budget)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    ∃t≤timeBound s sourceMap oldTemplate raw second (trCode.val==2) words answer budget oldStage oldInverse hist out,
      C.run (program s sourceMap) t (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out)=
        some (done s sourceMap raw second (trCode.val==2) words answer hist out) :=by
  have h0:=selector_call s sourceMap oldTemplate raw tagCode trCode second htag htr hcode
    oldStage oldInverse (vectorBits words) hist out
  have h1:=guard_run s sourceMap oldTemplate raw second (trCode.val==2) (vectorBits words) hist out
  obtain ⟨b,hb,h2⟩:=descriptor_call s sourceMap oldTemplate raw second (trCode.val==2) hraw answer budget hc words hist out
  have h:=runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h0
    (runs_trans (program s sourceMap) _ _ _ _ _ _ _ _ h1 h2)
  obtain ⟨finish,hr,ho⟩:=h [] (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out) ⟨rfl,rfl,rfl⟩
  refine ⟨(SemiprimeD1StackTransformSelectorsExecution.timeBound (raw 1) (raw 2) oldStage oldInverse+1)+(1+(b+1))+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases ho with ⟨hp,hd,hf⟩
    change SemiprimeD1StackCalls.step (program s sourceMap) finish=some (done s sourceMap raw second (trCode.val==2) words answer hist out)
    simp [SemiprimeD1StackCalls.step,hp,program,SemiprimeD1StackCalls.execute,hd,hf,done]
/-- The same complete trace on the genuine fixed finite-control machine. -/
noncomputable def recordInTime [Fintype L] (oldTemplate : K→List Bool) (raw : Fin 6→List Bool)
    (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (htag : raw 1=List.replicate tagCode.val true) (htr : raw 2=List.replicate trCode.val true)
    (hcode : SemiprimeD1StackTransformSelectors.tagDispatch tagCode=.copyTransform second)
    (hraw : SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2]) s.raw=[])
    (answer : List Bool→Bool) (budget : Nat→Nat)
    (hc : CheckerTrace s (SemiprimeD1StackDescriptorRecord.selected sourceMap (fields raw [second] [trCode.val==2])) answer budget)
    (words : List (List Bool)) (oldStage oldInverse hist out : List Bool) :
    StateTransition.EvalsToInTime (machine s sourceMap).step
      (SemiprimeD1StackCalls.configuration (initial s oldTemplate raw oldStage oldInverse (vectorBits words) hist out))
      (some (SemiprimeD1StackCalls.configuration (done s sourceMap raw second (trCode.val==2) words answer hist out)))
      (timeBound s sourceMap oldTemplate raw second (trCode.val==2) words answer budget oldStage oldInverse hist out) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (rawSource 0) output (.inl .start) (program s sourceMap)
  let h:=source_run s sourceMap oldTemplate raw tagCode trCode second htag htr hcode hraw answer budget hc words oldStage oldInverse hist out
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
omit [Fintype K] in
/-- Every original acquired raw field survives in its physical source location. -/
theorem retained_raw (raw : Fin 6→List Bool) (second inverse : Bool) (words : List (List Bool))
    (answer : List Bool→Bool) (hist out : List Bool) (i : Fin 6) :
    (done s sourceMap raw second inverse words answer hist out).data (rawSource i)=raw i :=by
  fin_cases i <;> rfl
end RiemannGaussian.SemiprimeD1StackSelectedDescriptorRecordExecution
