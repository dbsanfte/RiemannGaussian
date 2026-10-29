/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridRipple
/-! # Actual binary-grid decrement and complete physical ripple cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridDecrement
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Ripple
export SemiprimeD1StackRecoveryGridRipple (result subtract_call)
end Ripple
/-- Two physically written subtractor input words. -/
def prepared (w:Words) (xs:List Bool) :Words:=
  {w with rational:=Function.update (Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .left) xs) (SemiprimeD1StackRationalOperation.adderStack .right) [true]}
/-- Subtraction consumes both actual input copies before producing the actual difference. -/
theorem result_prepared (w:Words) (xs out:List Bool) :Ripple.result (prepared w xs) out=Ripple.result w out:=by
  dsimp only [Ripple.result,SemiprimeD1StackRecoveryGridRipple.result,prepared]
  congr 1
  funext k
  by_cases hl:k=SemiprimeD1StackRationalOperation.adderStack .left
  · subst k;rfl
  · by_cases hr:k=SemiprimeD1StackRationalOperation.adderStack .right
    · subst k;rfl
    · by_cases hs:k=SemiprimeD1StackRationalOperation.adderStack .scratch
      · subst k;rfl
      · by_cases ho:k=SemiprimeD1StackRationalOperation.adderStack .output
        · subst k;rfl
        · simp [hl,hr,hs,ho]
/-- All actual output writes replace only the prior actual ripple output. -/
theorem update_output (w:Words) (out xs:List Bool) :
    Function.update (bank (Ripple.result w out)) (rippleStack .output) xs=bank (Ripple.result w xs):=by
  change Function.update (bank (Ripple.result w out))
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .output)) xs=_
  rw [update_rational]
  dsimp only [Ripple.result,SemiprimeD1StackRecoveryGridRipple.result]
  rw [Function.update_idem]
/-- Actual q writes commute with shared-ripple output acquisition. -/
theorem update_q (w:Words) (out xs:List Bool) :
    Function.update (bank (Ripple.result w out)) (aux .q) xs=
      bank (Ripple.result {w with auxiliary:=Function.update w.auxiliary .q xs} out):=by
  rw [update_auxiliary]
  rfl
/-- The complete physical ripple bank is restored to its original clean bytes after both drains. -/
theorem result_clean (w:Words)
    (hr:∀k,w.rational (SemiprimeD1StackRationalOperation.adderStack k)=[]) :Ripple.result w []=w:=by
  dsimp only [Ripple.result,SemiprimeD1StackRecoveryGridRipple.result]
  have h0:Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .left) []=w.rational:=
    Function.update_eq_self_iff.mpr (hr .left).symm
  rw [h0]
  have h1:Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .right) []=w.rational:=
    Function.update_eq_self_iff.mpr (hr .right).symm
  rw [h1]
  have h2:Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .scratch) []=w.rational:=
    Function.update_eq_self_iff.mpr (hr .scratch).symm
  rw [h2]
  have h3:Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .output) []=w.rational:=
    Function.update_eq_self_iff.mpr (hr .output).symm
  rw [h3]
/-- Real continuation distinguishes the initial true-alpha subtraction and later q decrements. -/
def after :Decrement→Label
  | .initial=>.local (.clearGeometry .initial 0) | .next=>.local .row
/-- Exact actual lower binary difference word, including all acquired high zero padding. -/
def difference (xs:List Bool) :List Bool:=(SemiprimeBitDivision.subBits xs [true] false).result.bits
/-- The actual borrow bit is false precisely because this physical source word has positive value. -/
theorem borrow_false (xs:List Bool) (hp:0<SemiprimeBitArithmetic.bitValue xs) :
    (SemiprimeBitDivision.subBits xs [true] false).borrow=false:=by
  apply Bool.eq_false_of_not_eq_true
  intro h
  have he:=(SemiprimeBitDivision.subBits_borrow_iff xs [true] false).mp h
  change SemiprimeBitArithmetic.bitValue xs<1+0 at he
  omega
/-- Physical index decrement value; numeric values occur only in this proved interpretation. -/
theorem difference_value (xs:List Bool) (hp:0<SemiprimeBitArithmetic.bitValue xs) :
    SemiprimeBitArithmetic.bitValue (difference xs)=SemiprimeBitArithmetic.bitValue xs-1:=by
  exact SemiprimeBitDivision.subBits_difference (borrow_false xs hp)
/-- Own exact decrement budget counts copy/one/subtract/borrow, old-q drain, paid result copy and entire result drain. -/
def runBound (xs oldq:List Bool) :Nat:=
  (5*xs.length+4)+1+(3*(max xs.length 1+1)+2*(difference xs).length+3+1)+1+
    (oldq.length+1)+(5*(difference xs).length+4)+((difference xs).length+1)
/-- Actual decrement source, preserving all104 cells except the physically acquired next q and restoring shared ripple. -/
theorem decrement_run (part:Decrement) (w:Words) (xs oldq:List Bool)
    (hx:bank w (copySource (.qOperand part))=xs) (hq:w.auxiliary .q=oldq)
    (hr:∀k,w.rational (SemiprimeD1StackRationalOperation.adderStack k)=[])
    (hs:w.auxiliary .copyScratch=[]) (hp:0<SemiprimeBitArithmetic.bitValue xs) :
    Runs program (runBound xs oldq) (.local (.decrement part)) (bank w) (after part)
      (bank {w with auxiliary:=Function.update w.auxiliary .q (difference xs)}):=by
  let wl:Words:={w with rational:=Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .left) xs}
  have h0:=PTrace.copy_call (.qOperand part) (.local (.decrement part)) (.local (.subtractOne part)) rfl
    (bank w) xs [] hx (hr .left) hs
  change Runs program _ _ _ _ (Function.update (bank w)
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .left)) (xs++[])) at h0
  rw [List.append_nil,update_rational] at h0
  have h1:=PTrace.push_run (.local (.subtractOne part)) (.local (.subtract part)) (rippleStack .right) true (bank wl) rfl
  change Runs program 1 _ _ _ (Function.update (bank wl)
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .right)) (true::w.rational (SemiprimeD1StackRationalOperation.adderStack .right))) at h1
  rw [hr .right,update_rational] at h1
  change Runs program 1 _ _ _ (bank (prepared w xs)) at h1
  have hi:∀k,bank (prepared w xs) (rippleStack k)=SemiprimeD1StackAdder.store xs [true] [] [] k:=by
    intro k;cases k
    · rfl
    · rfl
    · exact hr .scratch
    · exact hr .output
  have h2:=Ripple.subtract_call part (prepared w xs) xs [true] hi
  rw [result_prepared,borrow_false xs hp] at h2
  have h3:=PTrace.pop_run (.local (.borrow part)) (.local .abort) (.local (.clearQ part)) (.local .abort)
    (rippleStack .output) (bank (Ripple.result w (false::difference xs))) (false::difference xs) rfl rfl
  rw [update_output] at h3
  change Runs program 1 _ _ (.local (.clearQ part)) _ at h3
  have h4:=PTrace.drain_loop (.local (.clearQ part)) (.local (.qResult part)) (aux .q) rfl
    (bank (Ripple.result w (difference xs))) oldq hq
  rw [update_q] at h4
  let wc:Words:={w with auxiliary:=Function.update w.auxiliary .q []}
  have h5:=PTrace.copy_call .qResult (.local (.qResult part)) (.local (.clearDifference part)) rfl
    (bank (Ripple.result wc (difference xs))) (difference xs) [] rfl rfl hs
  change Runs program _ _ _ _ (Function.update _ (aux .q) (difference xs++[])) at h5
  rw [List.append_nil,update_q] at h5
  dsimp only [wc] at h5
  rw [Function.update_idem] at h5
  let wf:Words:={w with auxiliary:=Function.update w.auxiliary .q (difference xs)}
  have hc:program (.local (.clearDifference part))=.base (.pop (rippleStack .output) (after part)
      (.local (.clearDifference part)) (.local (.clearDifference part))):=by cases part <;> rfl
  have h6:=PTrace.drain_loop (.local (.clearDifference part)) (after part) (rippleStack .output) hc
    (bank (Ripple.result wf (difference xs))) (difference xs) rfl
  rw [update_output,result_clean wf hr] at h6
  have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4) h5) h6
  exact h
/-- Original binary bytes alone pay every actual decrement instruction. -/
theorem runBound_le (xs oldq:List Bool) :runBound xs oldq≤100*(xs.length+oldq.length+1):=by
  have hl:=(SemiprimeBitDivision.subBits_counts xs [true] false).2.2.2.2
  change (difference xs).length=max xs.length 1 at hl
  have hm:max xs.length 1≤xs.length+1:=max_le (by omega) (by omega)
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridDecrement
