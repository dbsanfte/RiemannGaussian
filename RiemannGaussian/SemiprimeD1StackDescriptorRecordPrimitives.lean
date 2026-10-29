/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecord
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual generic copy, reverse, read and physical drain instructions -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecordPrimitives
open SemiprimeD1StackDescriptorRecord SemiprimeD1StackProcedureTrace
variable {K L : Type} [DecidableEq K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Physical clearing consumes each payload bit and the actual EOF. -/
theorem drain (pc next : Label L s.roles.length) (key : Stack K)
    (hc : program s sourceMap pc=.base (.pop key next pc pc)) (d : Stack K→List Bool) :
    Runs (program s sourceMap) ((d key).length+1) pc d next (Function.update d key []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain (program s sourceMap) pc next key hc d (d key)
  rw [Function.update_eq_self] at h
  exact h
/-- One preserving copy executes its literal program and actual return. -/
theorem copy_call (position : Fin s.roles.length) (pc next : Label L s.roles.length)
    (hc : program s sourceMap pc=.call (copyLabel position 0) next) (d : Stack K→List Bool)
    (hd : d (copyStack s sourceMap position 1)=[]) (hs : d scratch=[]) :
    Runs (program s sourceMap) (5*(d (copyStack s sourceMap position 0)).length+4) pc d next
      (Function.update d (copyStack s sourceMap position 1) (d (copyStack s sourceMap position 0))) := by
  let word:=d (copyStack s sourceMap position 0)
  have hin : Link.DataRel (copyStack s sourceMap position) d (SemiprimeD1StackCopy.state 0 none word [] []).store d := by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  have hout:=Link.data_update (copyStack s sourceMap position) (copyStack_injective s sourceMap position) _ _ _ hin (1:Fin 3) word
  have he:Function.update (SemiprimeD1StackCopy.state 0 none word [] []).store 1 word=
      (SemiprimeD1StackCopy.done word word).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call (program s sourceMap) (copyStack s sourceMap position) (copyLabel position) (copyStack_injective s sourceMap position)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hin hout
end RiemannGaussian.SemiprimeD1StackDescriptorRecordPrimitives
