/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationCalls
/-! # Actual oriented raw products and physical accumulator cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationProduct
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (mulBits)
/-- Only the actually selected raw-product destination is updated. -/
def saveProduct (w:Words) (p:Product) (bits:List Bool) :Words:=match p with
  | .crossLeft=>{w with originalLeft:=bits} | .crossRight=>{w with output:=bits}
  | .numerator=>{w with originalSigned:=bits} | .denominator=>{w with originalRight:=bits}
/-- Literal product destination update, including direct normalization inputs. -/
theorem update_product (w:Words) (p:Product) (bits:List Bool) :
    Function.update (bank w) (productOutput p) bits=bank (saveProduct w p bits):=by
  cases p
  · exact update_originalLeft w bits
  · exact update_output w bits
  · exact update_originalSigned w bits
  · exact update_originalRight w bits
/-- Shared-bank resets leave every acquired product source word unchanged. -/
theorem operand_preserved (w:Words) (p:Product) (b:Bool) (xs ys:List Bool) :
    bank (multiplyReady w xs ys) (productOperand p b)=bank w (productOperand p b):=by
  cases p <;> cases b <;> rfl
/-- Shared multiplier output does not alias any raw product destination. -/
theorem destination_preserved (w:Words) (p:Product) (bits:List Bool) :
    bank (multiplyDone w bits) (productOutput p)=bank w (productOutput p):=by
  cases p <;> rfl
/-- Every multiplier input/result bank keeps the actual common copy scratch unchanged. -/
theorem copyScratch_preserved (w:Words) (xs ys:List Bool) :
    bank (multiplyReady w xs ys) copyScratch=w.copyScratch:=rfl
/-- Actual two input copies, full multiplication, result copy and complete raw accumulator drain. -/
def productTime (xs ys:List Bool) :Nat:=
  (5*xs.length+4)+(5*ys.length+4)+
    (2*xs.length+1+SemiprimeD1StackMultiplierExecution.loopClock ys xs.reverse []+1)+
    (5*(mulBits xs ys).bits.length+4)+((mulBits xs ys).bits.length+1)
/-- One complete paid product route preserves every source and every outer return, then clears all nine multiplier roles. -/
theorem product_run (p:Product) (op:Op) (sx sy:Bool) (w:Words) (pc:Label)
    (hc:program pc=.call (.copier (.productLeft p) 0) (localLabel (.productRight p) op sx sy))
    (hs:w.copyScratch=[]) (hd:bank w (productOutput p)=[]) :
    let xs:=bank w (productOperand p false)
    let ys:=bank w (productOperand p true)
    Runs program (productTime xs ys) pc (bank (multiplyReady w [] [])) (afterProduct p op sx sy)
      (bank (saveProduct (multiplyReady w [] []) p (mulBits xs ys).bits)):=by
  dsimp only
  let xs:=bank w (productOperand p false)
  let ys:=bank w (productOperand p true)
  have h0:=P.copy_call (.productLeft p) pc (localLabel (.productRight p) op sx sy) hc
    (bank (multiplyReady w [] [])) xs [] (operand_preserved w p false [] []) rfl hs
  change Runs _ _ _ _ _ (Function.update (bank _) (multiplierStack SemiprimeD1StackMultiplier.input) (xs++[])) at h0
  rw [List.append_nil,update_multInput] at h0
  change Runs program _ pc _ _ (bank (multiplyReady w xs [])) at h0
  have h1:=P.copy_call (.productRight p) (localLabel (.productRight p) op sx sy) (localLabel (.multiply p) op sx sy) rfl
    (bank (multiplyReady w xs [])) ys [] (operand_preserved w p true xs []) rfl hs
  change Runs _ _ _ _ _ (Function.update (bank _) (multiplierStack SemiprimeD1StackMultiplier.factor) (ys++[])) at h1
  rw [List.append_nil,update_multFactor] at h1
  change Runs program _ _ _ _ (bank (multiplyReady w xs ys)) at h1
  have h2:=multiplier_call w xs ys (localLabel (.multiply p) op sx sy) (localLabel (.productSave p) op sx sy) rfl
  have h3:=P.copy_call (.productSave p) (localLabel (.productSave p) op sx sy) (localLabel (.productClear p) op sx sy) rfl
    (bank (multiplyDone w (mulBits xs ys).bits)) (mulBits xs ys).bits [] rfl
    ((destination_preserved w p _).trans hd) hs
  change Runs _ _ _ _ _ (Function.update (bank _) (productOutput p) ((mulBits xs ys).bits++[])) at h3
  rw [List.append_nil,update_product] at h3
  have h4:=P.drain_loop (localLabel (.productClear p) op sx sy) (afterProduct p op sx sy) (adderStack .right) rfl
    (bank (saveProduct (multiplyDone w (mulBits xs ys).bits) p (mulBits xs ys).bits))
    (mulBits xs ys).bits (by cases p <;> rfl)
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .right))) []) at h4
  rw [update_right] at h4
  have he:{saveProduct (multiplyDone w (mulBits xs ys).bits) p (mulBits xs ys).bits with right:=[]}=
      saveProduct (multiplyReady w [] []) p (mulBits xs ys).bits:=by cases p <;> rfl
  rw [he] at h4
  exact P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
end RiemannGaussian.SemiprimeD1StackRationalOperationProduct
