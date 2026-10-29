/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsView
/-! # One actual N-only phase producer call, one paid reference copy and one root header seed -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSource
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackRootPhaseFreshRecordsView
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Abstract caller bank before the one reference copy; all new physical words are empty. -/
def beforeCopy (root:R.Stack→List Bool) :Stack→List Bool :=
  view root (cacheInput root [] []) (work [] [] [] [] [] [] [])
/-- Abstract empty source extension avoids reducing any concrete N-dependent source heap. -/
theorem beforeCopy_data (root:R.Stack→List Bool) :beforeCopy root=data root (fun _=>[]) (fun _=>[]) :=by
  funext k
  rcases k with k|k
  · exact congrFun (rootView_eq root _ rfl rfl) k
  · rcases k with k|k
    · change privateCache (SemiprimeD1StackPhaseCacheFresh.input _ _ _ _) k=[]
      rw [private_input]
      exact ite_self []
    · cases k <;> rfl
/-- Literal header replacement changes no acquired heap/count/reference or private work. -/
theorem update_input_header (hp cn ref axes next:List Bool) :
    Function.update (SemiprimeD1StackPhaseCacheFresh.input hp cn ref axes) I.oldHeader next=
      SemiprimeD1StackPhaseCacheFresh.input hp cn ref next :=by
  funext k
  by_cases hk:k=I.oldHeader
  · subst k
    rw [Function.update_same]
    rfl
  · rw [Function.update_of_ne hk,input_only,input_only]
    simp only [hk,ite_false]
/-- The actual original source bank is retained through its sole physical reference-vector copy. -/
theorem copy_refs (root:R.Stack→List Bool) :
    Runs program (5*(root R.output).length+4) .copy (beforeCopy root) .seedHeader
      (view root (cacheInput root [] []) (work (root R.output) [] [] [] [] [] [])) :=by
  have h:=copy_call (beforeCopy root) rfl rfl
  change Runs program (5*(root R.output).length+4) .copy (beforeCopy root) .seedHeader
    (Function.update (view root (cacheInput root [] []) (work [] [] [] [] [] [] [])) (aux .reader) (root R.output)) at h
  rw [update_reader] at h
  exact h
/-- Root axes[] are encoded by ONE physical false push, not a supplied context/rank/value cache. -/
theorem seed_header (root:R.Stack→List Bool) (reader:List Bool) :
    Runs program 1 .seedHeader (view root (cacheInput root [] []) (work reader [] [] [] [] [] []))
      .header (loop root reader [] 0 []) :=by
  apply one_base program _ _ (.push oldHeader false .header) _ _ rfl
  · rfl
  · change Function.update (view root (cacheInput root [] []) (work reader [] [] [] [] [] []))
      (cacheStack I.oldHeader) [false]=_
    rw [update_cache]
    change view root (Function.update (SemiprimeD1StackPhaseCacheFresh.input _ _ _ _) I.oldHeader [false]) _=_
    rw [update_input_header]
    rfl
/-- One actual whole original-N phase source acquires every phase bank/heap/reference from N alone. -/
theorem root_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ SemiprimeD1StackRootPhaseParametersExecution.runBound bits,
      Runs program (q+1) .start (input bits) .copy (afterRoot bits) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootPhaseParametersExecution.source_run bits hc hN
  refine ⟨q,hq,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root root_injective R.program .start
    (fun _=>rfl) .start .copy rfl q (R.initial bits) (SemiprimeD1StackRootPhaseParametersEncoding.done bits)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The real source output is a retained188-cell bank with all new client/work roles empty. -/
theorem afterRoot_view (bits:List Bool) :
    afterRoot bits=beforeCopy (SemiprimeD1StackRootPhaseParametersEncoding.result bits) :=
  (beforeCopy_data _).symm
/-- Concrete stopped P48 bank list associated with a chronological source phase list. -/
def banks (a u edges:Nat) (rows:List (List Bool)) :List (SemiprimeD1StackPhaseWorkingPrecision.Stack→List Bool) :=
  rows.map (SemiprimeD1StackRootPhaseParametersRows.stopped a u edges)
/-- The consumer's record grammar is EXACTLY the actual producer's consecutive48frames, in order. -/
theorem records_bridge (a u edges:Nat) (rows:List (List Bool)) :
    SemiprimeD1StackPhaseBankRestoreExecution.records (banks a u edges rows)=
      SemiprimeD1StackRootPhaseParametersEncoding.records a u edges rows :=by
  simp only [SemiprimeD1StackPhaseBankRestoreExecution.records,banks,
    SemiprimeD1StackRootPhaseParametersEncoding.records,List.map_map]
  rfl
/-- Each actual issued ordinal selects exactly its own originally produced phase bank. -/
theorem bank_at (a u edges:Nat) (rows:List (List Bool)) (i:Fin rows.length) :
    (banks a u edges rows)[i.val]'((by simpa only [banks,List.length_map] using i.isLt))=SemiprimeD1StackPhaseCacheFreshComponents.phase a u edges rows[i.val] [false,true] :=by
  simp only [banks,List.getElem_map]
  rfl
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSource
