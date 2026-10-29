/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTable
import RiemannGaussian.SemiprimeD1StackProcedureReturns
/-! # Actual copy, reverse and pop traces of the product-table program -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTablePrimitives
open SemiprimeD1StackProductTable SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Every preserving-copy site uses distinct real source/destination/scratch. -/
theorem copy_injective (kind : CopyKind) : Function.Injective (copyStack kind) := by cases kind <;> decide
/-- Every real reversal consumes one distinct physical input into its output. -/
theorem reverse_injective (kind : ReverseKind) : Function.Injective (reverseStack kind) := by cases kind <;> decide
/-- One actual physical push, independent of prior finite flags. -/
theorem push (pc next : Label) (role : Stack) (b : Bool)
    (hc : program pc=.base (.push role b next)) (data : Stack→List Bool) :
    Runs program 1 pc data next (Function.update data role (b::data role)) := by
  apply one_base program pc next (.push role b next) _ _ hc <;> rfl
/-- One physical pop branches on the actual bit/EOF and consumes that cell. -/
theorem pop (pc empty lo hi : Label) (role : Stack)
    (hc : program pc=.base (.pop role empty lo hi)) (data : Stack→List Bool) :
    Runs program 1 pc data (SemiprimeD1StackBytecode.choose empty lo hi (data role).head?)
      (Function.update data role (data role).tail) := by
  apply one_base program pc _ (.pop role empty lo hi) _ _ hc <;> rfl
/-- Physical clearing visits every cell and the actual EOF. -/
theorem drain (pc next : Label) (role : Stack)
    (hc : program pc=.base (.pop role next pc pc)) (data : Stack→List Bool) :
    Runs program ((data role).length+1) pc data next (Function.update data role []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program pc next role hc data (data role)
  rw [Function.update_eq_self] at h
  exact h
/-- Actual preserving copy and real return, retaining every unrelated cell. -/
theorem copy_call (kind : CopyKind) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (data : Stack→List Bool) (hd : data (copyStack kind 1)=[]) (hs : data (.inr .scratch)=[]) :
    Runs program (5*(data (copyStack kind 0)).length+4) pc data next
      (Function.update data (copyStack kind 1) (data (copyStack kind 0))) := by
  let word:=data (copyStack kind 0)
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
/-- Actual consuming reversal visits every bit, includes its real return, and
preserves every other checker/private register. -/
theorem reverse_call (kind : ReverseKind) (pc next : Label) (hc : program pc=.call (.reverse kind 0) next)
    (data : Stack→List Bool) :
    Runs program (2*(data (reverseStack kind 0)).length+3) pc data next
      (Function.update (Function.update data (reverseStack kind 0) []) (reverseStack kind 1)
        ((data (reverseStack kind 0)).reverse++data (reverseStack kind 1))) := by
  let xs:=data (reverseStack kind 0)
  let ys:=data (reverseStack kind 1)
  have hin : Link.DataRel (reverseStack kind) data (SemiprimeD1StackReverseWord.state none xs ys).store data := by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack kind) (reverse_injective kind) _ _ _ hin (0:Fin 2) []
  have hout:=Link.data_update (reverseStack kind) (reverse_injective kind) _ _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he : Function.update (Function.update (SemiprimeD1StackReverseWord.state none xs ys).store 0 []) 1 (xs.reverse++ys)=
      (SemiprimeD1StackReverseWord.done (xs.reverse++ys)).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call program (reverseStack kind) (Label.reverse kind) (reverse_injective kind)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2)
    (SemiprimeD1StackReverseWord.state none xs ys) (SemiprimeD1StackReverseWord.done (xs.reverse++ys))
    _ _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run xs ys none) hin hout
end RiemannGaussian.SemiprimeD1StackProductTablePrimitives
