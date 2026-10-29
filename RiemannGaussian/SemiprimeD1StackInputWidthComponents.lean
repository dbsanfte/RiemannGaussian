/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputWidth

/-! # Actual input-width cache copies and physical offset acquisition -/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackInputWidthComponents
open SemiprimeD1StackInputWidth SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)

/-- Real preserving Copy, including actual return and restored shared scratch. -/
theorem copy_call (kind : Fin 3) (data : Stack→List Bool) (hs : data .scratch=[])
    (pc next : Label) (hc : program pc=.call (.copy kind 0) next) :
    Runs program (5*(data (copyStack kind 0)).length+4) pc data next
      (Function.update data (copyStack kind 1) (data (copyStack kind 0)++data (copyStack kind 1))) := by
  apply included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc
    (5*(data (copyStack kind 0)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (copyStack kind 0)) (data (copyStack kind 1)) [])
    (SemiprimeD1StackCopy.done (data (copyStack kind 0)) (data (copyStack kind 0)++data (copyStack kind 1))) _ _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k
      fin_cases kind <;> fin_cases k <;>
        simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases kind <;> fin_cases k <;>
        simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,Function.update,hs]
    · intro k hk
      have hd:k≠copyStack kind 1 := by intro h;subst k;exact hk 1 rfl
      exact Function.update_of_ne hd _ _

/-- The original bitwidth is physically copied, not given as a difference. -/
theorem copy_width (c : Cache) :
    Runs program (5*c.width.length+4) .start (store c [] [] [] [] [])
      .copyIndex (store c c.width [] [] [] []) := by
  have h:=copy_call 0 (store c [] [] [] [] []) rfl .start .copyIndex rfl
  change Runs program (5*c.width.length+4) .start (store c [] [] [] [] []) .copyIndex
    (Function.update (store c [] [] [] [] []) .remaining (c.width++[])) at h
  convert h using 1
  funext k;cases k <;> simp [store,Function.update]
/-- The actual descriptor index is physically copied before multiplication. -/
theorem copy_index (c : Cache) :
    Runs program (5*c.index.length+4) .copyIndex (store c c.width [] [] [] [])
      .multiply (store c c.width c.index [] [] []) := by
  have h:=copy_call 1 (store c c.width [] [] [] []) rfl .copyIndex .multiply rfl
  change Runs program (5*c.index.length+4) .copyIndex (store c c.width [] [] [] []) .multiply
    (Function.update (store c c.width [] [] [] []) .multiplier (c.index++[])) at h
  convert h using 1
  funext k;cases k <;> simp [store,Function.update]
/-- The physical radix limit is copied, preserving the actual unskipped width. -/
theorem copy_limit (c : Cache) (remaining : List Bool) :
    Runs program (5*c.radix.length+4) .copyLimit (store c remaining [] [] [] [])
      .initBound (store c remaining [] [] c.radix []) := by
  have h:=copy_call 2 (store c remaining [] [] [] []) rfl .copyLimit .initBound rfl
  change Runs program (5*c.radix.length+4) .copyLimit (store c remaining [] [] [] []) .initBound
    (Function.update (store c remaining [] [] [] []) .limit (c.radix++[])) at h
  convert h using 1
  funext k;cases k <;> simp [store,Function.update]

/-- The SAME real frozen product bytecode computes i*B from actual physical
counter lengths, retaining the exact radix bytes and without unary-format advice. -/
theorem product_call (c : Cache) :
    ∃t≤5*(c.index.length*(2*c.radix.length+3)+1),
      Runs program (t+1) .multiply (store c c.width c.index [] [] [])
        .skipLoop (store c c.width [] (unary (c.index.length*c.radix.length)) [] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackUnaryProductRaw.product_run c.index c.radix
  refine ⟨t,ht,?_⟩
  apply included_call program productStack Label.product product_injective U.code U.entry (fun _=>rfl)
    .multiply .skipLoop rfl t
    (⟨some U.entry,none,SemiprimeD1StackUnaryProduct.contents c.index c.radix [] []⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    (⟨none,none,SemiprimeD1StackUnaryProduct.contents [] c.radix [] (unary (c.index.length*c.radix.length))⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    _ _
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk .multiplier rfl).elim | exact (hk .product rfl).elim

end RiemannGaussian.SemiprimeD1StackInputWidthComponents
