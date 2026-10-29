/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyPrimitives
/-! # Real sentinel and strict-maximum calls, including nested procedures and returns -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCalls
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyPrimitives
open SemiprimeD1StackProcedureTrace
/-- The sentinel is physically pushed and preserving Copy actually visits every raw byte. -/
theorem sentinel_call (before:Stack→List Bool) (word:List Bool)
    (hw:before (aux .raw)=word) (hq:before query=[]) (hs:before copyScratch=[]) :
    Runs program (5*word.length+7) .encode before .copyDictionary
      (Function.update before query (word++[true])) :=by
  let start:=SemiprimeD1StackOwnerEqualityKey.initial word
  let stop:=SemiprimeD1StackOwnerEqualityKey.done word
  have hi:Link.DataRel sentinelStack before start.data before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hq
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update sentinelStack sentinel_injective before start.data before hi (1:Fin 3) (word++[true])
  have he:Function.update start.data 1 (word++[true])=stop.data:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact SemiprimeD1StackProcedureCallsTrace.included_call program sentinelStack Label.sentinel sentinel_injective
    K.program (.inl 0) (fun _=>rfl) .encode .copyDictionary rfl (5*word.length+6) start stop before _
    rfl rfl rfl rfl (SemiprimeD1StackOwnerEqualityKey.source_run word) hi ho
/-- Both actual comparison operands are consumed and all borrow/difference work is cleared before the physical result pop. -/
theorem less_call (before:Stack→List Bool) (left right:List Bool)
    (hi:∀k,before (lessStack k)=(SemiprimeD1StackWordLess.initial left right).data k) :
    Runs program (SemiprimeD1StackWordLessExecution.totalTime left right+1) .compare before .readMaximum
      (Function.update (Function.update (Function.update before (lookupStack (.inl .left)) [])
        (lookupStack (.inl .right)) []) (lookupStack (.inr .discard)) [SemiprimeD1StackWordLessExecution.answer left right]) :=by
  let start:=SemiprimeD1StackWordLess.initial left right
  let stop:=SemiprimeD1StackWordLessExecution.done left right
  have hin:Link.DataRel lessStack before start.data before:=⟨hi,fun _ _=>rfl⟩
  have h0:=Link.data_update lessStack less_injective before start.data before hin (.inl .left) []
  have h1:=Link.data_update lessStack less_injective before _ _ h0 (.inl .right) []
  have h2:=Link.data_update lessStack less_injective before _ _ h1 (.inr ()) [SemiprimeD1StackWordLessExecution.answer left right]
  have he:Function.update (Function.update (Function.update start.data (.inl .left) []) (.inl .right) []) (.inr ())
      [SemiprimeD1StackWordLessExecution.answer left right]=stop.data:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  exact SemiprimeD1StackProcedureCallsTrace.included_call program lessStack Label.less less_injective Less.program .start
    (fun _=>rfl) .compare .readMaximum rfl (SemiprimeD1StackWordLessExecution.totalTime left right)
    start stop before _ rfl rfl rfl rfl (SemiprimeD1StackWordLessExecution.source_run left right) hin h2
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCalls
