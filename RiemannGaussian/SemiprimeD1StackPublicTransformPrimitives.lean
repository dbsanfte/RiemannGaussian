/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransform
/-! # Literal copies, pushes, pops and drains of the public transform machine
The generic data functions below are proof views of physical Bool stacks, never
executing source/getter/clock arguments. Final endpoints use actual N acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformPrimitives
open SemiprimeD1StackPublicTransform SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Every actual preserving-copy instance has three physically disjoint roles. -/
theorem copy_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by
  cases kind with
  | root inverse=>cases inverse <;> decide
  | modulus destination=>fin_cases destination <;> decide
  | axis second destination=>cases second <;> fin_cases destination <;> decide
  | vector fromOutput destination=>cases fromOutput <;> fin_cases destination <;> decide
  | normalizer=>decide
  | rawInput=>decide
  | rawOutput=>decide
  | remaining=>decide
  | frequency=>decide
  | index=>decide
  | normOperand=>decide
  | dotOperand=>decide
  | productResult=>decide
  | outputWord=>decide
/-- One literal physical push with its exact stack update. -/
theorem push (pc next : Label) (role : Stack) (b : Bool)
    (hc : program pc=.base (.push role b next)) (data : Stack→List Bool) :
    Runs program 1 pc data next (Function.update data role (b::data role)) := by
  apply one_base program pc next (.push role b next) _ _ hc <;> rfl
/-- One physical pop selects only its actual Boolean/EOF, never supplied truth. -/
theorem pop (pc empty low high : Label) (role : Stack)
    (hc : program pc=.base (.pop role empty low high)) (data : Stack→List Bool) :
    Runs program 1 pc data (SemiprimeD1StackBytecode.choose empty low high (data role).head?)
      (Function.update data role (data role).tail) := by
  apply one_base program pc _ (.pop role empty low high) _ _ hc <;> rfl
/-- Every cleared cell is actually popped; no unit-cost clearing primitive exists. -/
theorem drain (pc next : Label) (role : Stack)
    (hc : program pc=.base (.pop role next pc pc)) (data : Stack→List Bool) :
    Runs program ((data role).length+1) pc data next (Function.update data role []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program pc next role hc data (data role)
  rw [Function.update_eq_self] at h
  exact h
/-- The actual preserving copy, restoring source and empty scratch and including
its REAL call/return. No copied-word or component-clock answer is an input. -/
theorem copy_call (kind : CopyKind) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (data : Stack→List Bool) (hd : data (copyDestination kind)=[]) (hs : data (.aux .scratch)=[]) :
    Runs program (5*(data (copySource kind)).length+4) pc data next
      (Function.update data (copyDestination kind) (data (copySource kind))) := by
  let word:=data (copySource kind)
  have hin : Link.DataRel (copyStack kind) data (SemiprimeD1StackCopy.state 0 none word [] []).store data := by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  have hout:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hin (1:Fin 3) word
  have he : Function.update (SemiprimeD1StackCopy.state 0 none word [] []).store 1 word=
      (SemiprimeD1StackCopy.done word word).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hin hout
end RiemannGaussian.SemiprimeD1StackPublicTransformPrimitives
