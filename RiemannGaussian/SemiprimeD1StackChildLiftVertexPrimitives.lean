/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertex
/-! # Actual source call, two preserving frame sites and literal tag writes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexPrimitives
open SemiprimeD1StackChildLiftVertex SemiprimeD1StackProcedureTrace
namespace M
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end M
/-- Exact data-bank update; no field is reconstructed or dropped. -/
theorem update_record (source : T.Stack→List Bool) (record scratch word : List Bool) :
    Function.update (bank source record scratch) (aux .record) word=bank source word scratch := by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Real whole134-source call, including its nested calls and actual return. -/
theorem table_call (time : ℕ) (source out : C.State T.Stack T.Label)
    (hentry : source.pc=some .start) (hstart : source.frames=[])
    (hstop : out.pc=none) (hframes : out.frames=[])
    (hr : SemiprimeD1StackCalls.run T.program time source=some out) :
    Runs program (time+1) (.local .start) (bank source.data [] []) (.local .seed) (bank out.data [] []) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program table Label.source table_injective
    T.program .start (fun _=>rfl) (.local .start) (.local .seed) rfl time source out
    _ _ hentry hstart hstop hframes hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Actual literal push is independent of stale flags and preserves every return. -/
theorem push_run (pc next : Control) (bit : Bool) (source : T.Stack→List Bool) (record scratch : List Bool)
    (hcode : program (.local pc)=.base (.push (aux .record) bit (.local next))) :
    Runs program 1 (.local pc) (bank source record scratch) (.local next) (bank source (bit::record) scratch) := by
  apply one_base program (.local pc) (.local next) (.push (aux .record) bit (.local next))
    _ _ hcode rfl
  exact update_record source record scratch (bit::record)
/-- Every source bit is physically restored while its exact frame is prepended to the already acquired tail. -/
theorem frame_call (scope : Bool) (pc next : Control) (data : Stack→List Bool) (word tail : List Bool)
    (hcall : program (.local pc)=.call (.frame scope 0) (.local next))
    (hin : ∀i,data (frameStack scope i)=SemiprimeD1StackFrame.payload word tail [] i) :
    Runs program (6*word.length+5) (.local pc) data (.local next)
      (Function.update data (aux .record) (SemiprimeSourceHistogramKeyBits.frame word tail)) := by
  let source:=SemiprimeD1StackFrame.state 0 none word tail []
  let result:=SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word tail)
  have hd : M.DataRel (frameStack scope) data source.store data:=⟨hin,fun _ _=>rfl⟩
  have hu:=M.data_update (frameStack scope) (frame_injective scope) data source.store data hd 1
    (SemiprimeSourceHistogramKeyBits.frame word tail)
  have he : Function.update source.store 1 (SemiprimeSourceHistogramKeyBits.frame word tail)=result.store := by
    funext i
    fin_cases i <;> simp [source,result,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.done,
      SemiprimeD1StackFrame.payload,Function.update]
  rw [he] at hu
  exact SemiprimeD1StackProcedureTrace.included_call program (frameStack scope) (Label.frame scope)
    (frame_injective scope) SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (.local pc) (.local next) hcall (6*word.length+4) source result data _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word tail none) hd hu
end RiemannGaussian.SemiprimeD1StackChildLiftVertexPrimitives
