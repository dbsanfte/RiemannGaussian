/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationCalls
/-! # Literal signed addition, borrow-driven operand reversal and exact cancellation sign -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationAdd
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (addBits)
open SemiprimeBitDivision (subBits)
/-- Both actual cross-products, in the subtraction orientation selected by real borrow. -/
def left (w:Words) (rev:Bool) :List Bool:=if rev then w.output else w.originalLeft
/-- The other actual cross-product, preserving legacy operand order. -/
def right (w:Words) (rev:Bool) :List Bool:=if rev then w.originalLeft else w.output
/-- Both acquired cross-products are physically copied into the actual ripple inputs. -/
theorem prepare_run (rev:Bool) (op:Op) (sx sy:Bool) (w:Words) (hs:w.copyScratch=[]) :
    Runs program ((5*(left w rev).length+4)+(5*(right w rev).length+4))
      (localLabel (.addLeft rev) op sx sy) (bank (rippleReady w [] []))
      (localLabel (.combine rev) op sx sy) (bank (rippleReady w (left w rev) (right w rev))):=by
  have h0:=P.copy_call (.addLeft rev) (localLabel (.addLeft rev) op sx sy) (localLabel (.addRight rev) op sx sy) rfl
    (bank (rippleReady w [] [])) (left w rev) [] (by cases rev <;> rfl) rfl hs
  change Runs _ _ _ _ _ (Function.update (bank _) (adderStack .left) ((left w rev)++[])) at h0
  rw [List.append_nil,adderStack,update_left] at h0
  change Runs program _ _ _ _ (bank (rippleReady w (left w rev) [])) at h0
  have h1:=P.copy_call (.addRight rev) (localLabel (.addRight rev) op sx sy) (localLabel (.combine rev) op sx sy) rfl
    (bank (rippleReady w (left w rev) [])) (right w rev) [] (by cases rev <;> rfl) rfl hs
  change Runs _ _ _ _ _ (Function.update (bank _) (adderStack .right) ((right w rev)++[])) at h1
  rw [List.append_nil,adderStack,update_right] at h1
  exact P.join h0 h1
/-- Exact raw output copy and actual complete ripple-output drain. -/
def saveTime (bits:List Bool) :Nat:=(5*bits.length+4)+(bits.length+1)
/-- The acquired raw numerator is copied before the consumed difference is physically erased. -/
theorem save_run (negative:Bool) (op:Op) (sx sy:Bool) (w:Words) (bits:List Bool)
    (hs:w.copyScratch=[]) (hz:w.originalSigned=[]) :
    Runs program (saveTime bits) (localLabel (.addSave negative) op sx sy)
      (bank (rippleDone w bits)) (localLabel (.rawSign negative) op sx sy)
      (bank (rippleDone {w with originalSigned:=bits} [])):=by
  have h0:=P.copy_call .addSave (localLabel (.addSave negative) op sx sy) (localLabel (.clearDifference negative) op sx sy) rfl
    (bank (rippleDone w bits)) bits [] rfl hz hs
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) (bits++[])) at h0
  rw [List.append_nil,update_originalSigned] at h0
  have h1:=P.drain_loop (localLabel (.clearDifference negative) op sx sy) (localLabel (.rawSign negative) op sx sy)
    (adderStack .output) rfl (bank {rippleDone w bits with originalSigned:=bits}) bits rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .output))) []) at h1
  rw [update_difference] at h1
  exact P.join h0 h1
/-- Actual same-sign full adder time, including real caller return. -/
def addTime (xs ys:List Bool) :Nat:=3*(max xs.length ys.length+1)+2*(addBits xs ys false).bits.length+2+1
/-- Actual full subtractor time, including borrow byte and real caller return. -/
def subtractTime (xs ys:List Bool) :Nat:=3*(max xs.length ys.length+1)+2*(subBits xs ys false).result.bits.length+3+1
/-- Both preserving cross-product copies are paid in their real physical orientation. -/
def prepareTime (xs ys:List Bool) :Nat:=(5*xs.length+4)+(5*ys.length+4)
/-- Own complete signed-add trace clock, selected only by actual signs/borrow bits. -/
def sumTime (sx:Bool) (xs:List Bool) (sy:Bool) (ys:List Bool) :Nat:=
  prepareTime xs ys+
    (if sx=sy then addTime xs ys+saveTime (addBits xs ys false).bits
    else subtractTime xs ys+1+
      (if (subBits xs ys false).borrow then
        ((subBits xs ys false).result.bits.length+1)+prepareTime ys xs+subtractTime ys xs+1+
          saveTime (subBits ys xs false).result.bits
      else saveTime (subBits xs ys false).result.bits))
/-- The actual borrow byte is popped, retaining only actual difference bytes and every other caller word. -/
theorem borrow_run (rev:Bool) (op:Op) (sx sy:Bool) (w:Words) (b:Bool) (bits:List Bool) :
    Runs program 1 (localLabel (.borrow rev) op sx sy) (bank (rippleDone w (b::bits)))
      (localLabel (if b then (if rev then .addSave sy else .discardDifference) else .addSave (if rev then sy else sx)) op sx sy)
      (bank (rippleDone w bits)):=by
  have h:=P.pop_run (localLabel (.borrow rev) op sx sy) (localLabel .abort op sx sy)
    (localLabel (.addSave (if rev then sy else sx)) op sx sy)
    (if rev then localLabel (.addSave sy) op sx sy else localLabel .discardDifference op sx sy)
    (adderStack .output) (bank (rippleDone w (b::bits))) (b::bits) rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .output))) bits) at h
  rw [update_difference] at h
  cases b <;> cases rev <;> exact h
/-- The physically rejected wrapped difference is actually consumed before reversed subtraction. -/
theorem discard_run (op:Op) (sx sy:Bool) (w:Words) (bits:List Bool) :
    Runs program (bits.length+1) (localLabel .discardDifference op sx sy) (bank (rippleDone w bits))
      (localLabel (.addLeft true) op sx sy) (bank (rippleReady w [] [])):=by
  have h:=P.drain_loop (localLabel .discardDifference op sx sy) (localLabel (.addLeft true) op sx sy)
    (adderStack .output) rfl (bank (rippleDone w bits)) bits rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl .output))) []) at h
  rw [update_difference] at h
  exact h
/-- Exact legacy signed-sum bytes and tie sign are acquired by real ripple calls and actual borrow branching. -/
theorem sum_run (op:Op) (sx sy:Bool) (w:Words) (hs:w.copyScratch=[]) (hz:w.originalSigned=[]) :
    let result:SemiprimeBitIndexClipping.SignedWord:=
      (SemiprimeBitIndexClipping.addSignedBits ⟨sx,w.originalLeft⟩ ⟨sy,w.output⟩).word
    Runs program (sumTime sx w.originalLeft sy w.output) (localLabel (.addLeft false) op sx sy)
      (bank (rippleReady w [] [])) (localLabel (.rawSign result.negative) op sx sy)
      (bank (rippleDone {w with originalSigned:=result.magnitude} [])):=by
  dsimp only
  have h0:=prepare_run false op sx sy w hs
  by_cases he:sx=sy
  · have h1:=adder_call w w.originalLeft w.output (localLabel (.combine false) op sx sy) (localLabel (.addSave sx) op sx sy)
      (by simp only [program,localLabel,he,ite_true])
    have h2:=save_run sx op sx sy w (addBits w.originalLeft w.output false).bits hs hz
    have h:=P.join h0 (P.join h1 h2)
    simpa only [left,right,Bool.false_eq_true,ite_false,ite_true,Nat.add_assoc,sumTime,prepareTime,addTime,SemiprimeBitIndexClipping.addSignedBits,he,ite_true] using h
  · have h1:=subtractor_call w w.originalLeft w.output (localLabel (.combine false) op sx sy) (localLabel (.borrow false) op sx sy)
      (by simp only [program,localLabel,he,ite_false])
    have h2:=borrow_run false op sx sy w (subBits w.originalLeft w.output false).borrow (subBits w.originalLeft w.output false).result.bits
    cases hb:(subBits w.originalLeft w.output false).borrow with
    | false=>
      rw [hb] at h1 h2
      have h3:=save_run sx op sx sy w (subBits w.originalLeft w.output false).result.bits hs hz
      have h:=P.join h0 (P.join (P.join h1 h2) h3)
      simpa only [left,right,Bool.false_eq_true,ite_false,ite_true,Nat.add_assoc,sumTime,prepareTime,subtractTime,SemiprimeBitIndexClipping.addSignedBits,he,hb,
        Bool.false_eq_true,ite_false] using h
    | true=>
      rw [hb] at h1 h2
      have h3:=discard_run op sx sy w (subBits w.originalLeft w.output false).result.bits
      have h4:=prepare_run true op sx sy w hs
      have h5:=subtractor_call w w.output w.originalLeft (localLabel (.combine true) op sx sy) (localLabel (.borrow true) op sx sy)
        (by simp only [program,localLabel,he,ite_false])
      have h6:=borrow_run true op sx sy w (subBits w.output w.originalLeft false).borrow (subBits w.output w.originalLeft false).result.bits
      have hx:(if (subBits w.output w.originalLeft false).borrow then (if true then Phase.addSave sy else .discardDifference)
          else .addSave (if true then sy else sx))=Phase.addSave sy:=by
        cases (subBits w.output w.originalLeft false).borrow <;> rfl
      rw [hx] at h6
      have h7:=save_run sy op sx sy w (subBits w.output w.originalLeft false).result.bits hs hz
      have h:=P.join h0 (P.join (P.join h1 h2) (P.join h3 (P.join h4 (P.join (P.join h5 h6) h7))))
      simpa only [left,right,Bool.false_eq_true,ite_false,ite_true,Nat.add_assoc,sumTime,prepareTime,subtractTime,SemiprimeBitIndexClipping.addSignedBits,he,hb,ite_true] using h
end RiemannGaussian.SemiprimeD1StackRationalOperationAdd
