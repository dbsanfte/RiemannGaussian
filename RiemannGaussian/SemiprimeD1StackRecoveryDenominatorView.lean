/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOperators
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding
/-! # Whole19-role actual row-loop boundary views
Only original row/template bytes, the actual reader, actual scalar operands and
the growing raw accumulator can be live at these physically reached boundaries.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorView
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
namespace O
export SemiprimeD1StackRecoveryDenominatorOperators (multiplied fitted replaceMul)
end O
/-- Complete actual boundary bank; every unlisted role and both shadows are empty. -/
def bank (rows reader widthTemplate xs ys acc out:List Bool):Values
  | .mul k=>M.payload xs ys [] [] acc [] [] [] [] k
  | .template=>widthTemplate | .counter|.fitScratch=>[]
  | .aux .rows=>rows | .aux .reader=>reader | .aux .output=>out | .aux .discard|.aux .valid=>[]
/-- Actual physical reader update. -/
theorem update_reader (rows reader widthTemplate xs ys acc out word:List Bool):
    Function.update (bank rows reader widthTemplate xs ys acc out) (.aux .reader) word=
      bank rows word widthTemplate xs ys acc out:=by
  funext k;cases k with
  | mul k=>rfl
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Actual first full-multiplier operand update. -/
theorem update_input (rows reader widthTemplate xs ys acc out word:List Bool):
    Function.update (bank rows reader widthTemplate xs ys acc out) (.mul M.input) word=
      bank rows reader widthTemplate word ys acc out:=by
  funext k;cases k with
  | mul k=>simpa only [Function.update_apply,Slot.mul.injEq,bank] using congrFun (SemiprimeD1StackMultiplierExecution.payload_xs xs ys [] [] acc [] [] [] [] word) k
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Actual second full-multiplier operand update. -/
theorem update_factor (rows reader widthTemplate xs ys acc out word:List Bool):
    Function.update (bank rows reader widthTemplate xs ys acc out) (.mul M.factor) word=
      bank rows reader widthTemplate xs word acc out:=by
  funext k;cases k with
  | mul k=>simpa only [Function.update_apply,Slot.mul.injEq,bank] using congrFun (SemiprimeD1StackMultiplierExecution.payload_ys xs ys [] [] acc [] [] [] [] word) k
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Actual raw-product accumulator update. -/
theorem update_accumulator (rows reader widthTemplate xs ys acc out word:List Bool):
    Function.update (bank rows reader widthTemplate xs ys acc out) (.mul (.inl .right)) word=
      bank rows reader widthTemplate xs ys word out:=by
  funext k;cases k with
  | mul k=>simpa only [Function.update_apply,Slot.mul.injEq,bank] using congrFun (SemiprimeD1StackMultiplierExecution.payload_acc xs ys [] [] acc [] [] [] [] word) k
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Actual final-result role update. -/
theorem update_output (rows reader widthTemplate xs ys acc out word:List Bool):
    Function.update (bank rows reader widthTemplate xs ys acc out) (.aux .output) word=
      bank rows reader widthTemplate xs ys acc word:=by
  funext k;cases k with
  | mul k=>rfl
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Whole real full-product call result is exactly the next clean loop boundary. -/
theorem multiplied_bank (rows reader widthTemplate xs ys:List Bool):
    O.multiplied (bank rows reader widthTemplate xs ys [] []) xs ys=
      bank rows reader widthTemplate [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits []:=by
  funext k;cases k with
  | mul k=>rfl
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
/-- Whole real final fit result retains the original source and physical template literally. -/
theorem fitted_bank (rows reader widthTemplate word:List Bool):
    O.fitted (bank rows reader widthTemplate [] [] word [])=
      bank rows reader widthTemplate [] [] [] (SemiprimeD1StackWordFitExecution.result word widthTemplate):=by
  unfold O.fitted
  rw [update_accumulator,update_output]
  rfl
/-- Exactly two initialized physical words, no advised product or width value. -/
theorem initial_bank (rows widthTemplate:List Bool):
    initialValues rows widthTemplate=bank rows [] widthTemplate [] [] [] []:=by
  funext k;cases k with
  | mul k=>
    rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|k
      · fin_cases k <;> rfl
      · cases k <;> rfl
  | template|counter|fitScratch=>rfl
  | aux k=>cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorView
