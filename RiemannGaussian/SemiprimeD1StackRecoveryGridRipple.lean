/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
/-! # Real shared-ripple subtraction and equality inside original-grid acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRipple
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- Proof-side complete store after physically consuming two ripple operands and acquiring actual output. -/
def result (w:Words) (out:List Bool) :Words:=
  {w with rational:=Function.update (Function.update (Function.update (Function.update w.rational
    (SemiprimeD1StackRationalOperation.adderStack .left) []) (SemiprimeD1StackRationalOperation.adderStack .right) [])
    (SemiprimeD1StackRationalOperation.adderStack .scratch) []) (SemiprimeD1StackRationalOperation.adderStack .output) out}
/-- Complete four-role included primitive endpoint, with all100 external words preserved. -/
theorem result_data (w:Words) (out:List Bool) :
    SemiprimeD1StackMultiplierLink.DataRel rippleStack (bank w)
      (SemiprimeD1StackAdder.store [] [] [] out) (bank (result w out)):=by
  constructor
  · intro k;cases k <;> rfl
  · intro k hk
    rcases k with k|k
    · have hl:k≠SemiprimeD1StackRationalOperation.adderStack .left:=by intro he;exact (hk .left (congrArg rationalStack he.symm)).elim
      have hr:k≠SemiprimeD1StackRationalOperation.adderStack .right:=by intro he;exact (hk .right (congrArg rationalStack he.symm)).elim
      have hs:k≠SemiprimeD1StackRationalOperation.adderStack .scratch:=by intro he;exact (hk .scratch (congrArg rationalStack he.symm)).elim
      have ho:k≠SemiprimeD1StackRationalOperation.adderStack .output:=by intro he;exact (hk .output (congrArg rationalStack he.symm)).elim
      change Function.update (Function.update (Function.update (Function.update w.rational _ []) _ []) _ []) _ out k=w.rational k
      rw [Function.update_of_ne ho,Function.update_of_ne hs,Function.update_of_ne hr,Function.update_of_ne hl]
    · rfl
/-- Literal subtraction at either actual binary-index decrement site. -/
theorem subtract_call (part:Decrement) (w:Words) (xs ys:List Bool)
    (hi:∀k,bank w (rippleStack k)=SemiprimeD1StackAdder.store xs ys [] [] k) :
    Runs program (3*(max xs.length ys.length+1)+2*(SemiprimeBitDivision.subBits xs ys false).result.bits.length+3+1)
      (.local (.subtract part)) (bank w) (.local (.borrow part))
      (bank (result w ((SemiprimeBitDivision.subBits xs ys false).borrow::(SemiprimeBitDivision.subBits xs ys false).result.bits))):=by
  apply included_call program rippleStack Label.subtract ripple_injective S.code (.start false) (fun _=>rfl)
    (.local (.subtract part)) (.local (.borrow part)) rfl _
    (SemiprimeD1StackSubtractor.state (some (.start false)) none xs ys [] [])
    (SemiprimeD1StackSubtractor.state none none [] [] []
      ((SemiprimeBitDivision.subBits xs ys false).borrow::(SemiprimeBitDivision.subBits xs ys false).result.bits))
    _ _ rfl rfl (SemiprimeD1StackSubtractorExecution.source_run xs ys false)
  · exact ⟨hi,fun _ _=>rfl⟩
  · exact result_data w _
/-- Numeric word equality is an actual fixed comparison over both acquired binary operands, including padding. -/
theorem equal_call (w:Words) (xs ys:List Bool)
    (hi:∀k,bank w (rippleStack k)=SemiprimeD1StackAdder.store xs ys [] [] k) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime xs ys+1)
      (.local .equal) (bank w) (.local .equalRead)
      (bank (result w [decide (SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys)])):=by
  apply included_call program rippleStack Label.equal ripple_injective E.code .loop (fun _=>rfl)
    (.local .equal) (.local .equalRead) rfl _
    (SemiprimeD1StackWordEqual.state (some .loop) none xs ys [])
    (SemiprimeD1StackWordEqual.state none none [] [] [decide (SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys)])
    _ _ rfl rfl (SemiprimeD1StackWordEqualExecution.source_run xs ys none)
  · exact ⟨hi,fun _ _=>rfl⟩
  · exact result_data w _
end RiemannGaussian.SemiprimeD1StackRecoveryGridRipple
