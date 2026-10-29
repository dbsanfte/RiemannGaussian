/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTable
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual generic copy, reverse, read and physical drain instructions -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackStaticTablePrimitives
open SemiprimeD1StackStaticTable SemiprimeD1StackProcedureTrace
variable {K L : Type} [DecidableEq K] (s : Static K L)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
omit [DecidableEq K] in
/-- Read-only source, writable destination and scratch never alias at any site. -/
theorem copy_injective (position : Option (Fin s.roles.length)) : Function.Injective (copyStack s position) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> cases position <;>
    simp_all [copyStack,checker,template,aux]
omit [DecidableEq K] in
/-- Both consuming reversals have distinct physical operands. -/
theorem reverse_injective (table : Bool) : Function.Injective (reverseStack s table) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> cases table <;> simp_all [reverseStack,checker,aux]
/-- One actual literal Boolean push. -/
theorem push (pc next : Label L s.roles.length) (key : Stack K) (bit : Bool)
    (hc : program s pc=.base (.push key bit next)) (d : Stack K→List Bool) :
    Runs (program s) 1 pc d next (Function.update d key (bit::d key)) := by
  apply one_base (program s) pc next (.push key bit next) _ _ hc <;> rfl
/-- Physical clearing consumes each payload bit and the actual EOF. -/
theorem drain (pc next : Label L s.roles.length) (key : Stack K)
    (hc : program s pc=.base (.pop key next pc pc)) (d : Stack K→List Bool) :
    Runs (program s) ((d key).length+1) pc d next (Function.update d key []) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain (program s) pc next key hc d (d key)
  rw [Function.update_eq_self] at h
  exact h
/-- One preserving copy executes its literal program and actual return. -/
theorem copy_call (position : Option (Fin s.roles.length)) (pc next : Label L s.roles.length)
    (hc : program s pc=.call (.copy position 0) next) (d : Stack K→List Bool)
    (hd : d (copyStack s position 1)=[]) (hs : d (aux .scratch)=[]) :
    Runs (program s) (5*(d (copyStack s position 0)).length+4) pc d next
      (Function.update d (copyStack s position 1) (d (copyStack s position 0))) := by
  let word:=d (copyStack s position 0)
  have hin : Link.DataRel (copyStack s position) d (SemiprimeD1StackCopy.state 0 none word [] []).store d := by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  have hout:=Link.data_update (copyStack s position) (copy_injective s position) _ _ _ hin (1:Fin 3) word
  have he:Function.update (SemiprimeD1StackCopy.state 0 none word [] []).store 1 word=
      (SemiprimeD1StackCopy.done word word).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call (program s) (copyStack s position) (Label.copy position) (copy_injective s position)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none) hin hout
/-- Actual prefix/table reversal, retaining every other template/cache/work word. -/
theorem reverse_call (table : Bool) (pc next : Label L s.roles.length)
    (hc : program s pc=.call (.reverse table 0) next) (d : Stack K→List Bool) :
    Runs (program s) (2*(d (reverseStack s table 0)).length+3) pc d next
      (Function.update (Function.update d (reverseStack s table 0) []) (reverseStack s table 1)
        ((d (reverseStack s table 0)).reverse++d (reverseStack s table 1))) := by
  let xs:=d (reverseStack s table 0)
  let ys:=d (reverseStack s table 1)
  have hin : Link.DataRel (reverseStack s table) d (SemiprimeD1StackReverseWord.state none xs ys).store d := by
    constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack s table) (reverse_injective s table) _ _ _ hin (0:Fin 2) []
  have hout:=Link.data_update (reverseStack s table) (reverse_injective s table) _ _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update (SemiprimeD1StackReverseWord.state none xs ys).store 0 []) 1 (xs.reverse++ys)=
      (SemiprimeD1StackReverseWord.done (xs.reverse++ys)).store := by funext k;fin_cases k <;> rfl
  rw [he] at hout
  apply included_call (program s) (reverseStack s table) (Label.reverse table) (reverse_injective s table)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*xs.length+2)
    (SemiprimeD1StackReverseWord.state none xs ys) (SemiprimeD1StackReverseWord.done (xs.reverse++ys))
    _ _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run xs ys none) hin hout
end RiemannGaussian.SemiprimeD1StackStaticTablePrimitives
