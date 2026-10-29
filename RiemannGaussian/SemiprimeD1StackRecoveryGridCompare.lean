/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridDecrement
/-! # Actual original-node equality branch with complete shared-ripple cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridCompare
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
namespace Ripple
export SemiprimeD1StackRecoveryGridRipple (result equal_call)
end Ripple
/-- Actual input copies for the literal numeric equality comparison. -/
def prepared (w:Words) (xs ys:List Bool) :Words:=
  {w with rational:=Function.update (Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .left) xs) (SemiprimeD1StackRationalOperation.adderStack .right) ys}
/-- Both operand copies are physically consumed before the actual equality flag is read. -/
theorem result_prepared (w:Words) (xs ys out:List Bool) :Ripple.result (prepared w xs ys) out=Ripple.result w out:=by
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
/-- Actual finite equality result chooses skip-node or work-row, without any supplied comparison answer. -/
def after (xs ys:List Bool) :Label:=
  if SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys then .local (.clearTransient false 0) else .local .index
/-- Own complete comparison budget includes both preserving copies, real comparison/return and physical flag consumption. -/
def runBound (xs ys:List Bool) :Nat:=
  (5*xs.length+4)+(5*ys.length+4)+(SemiprimeD1StackWordEqualExecution.executionTime xs ys+1)+1
/-- The exact numeric-node test executes on actual copied q/t bytes and restores all104 original physical words. -/
theorem compare_run (w:Words) (xs ys:List Bool)
    (hx:w.auxiliary .q=xs) (hy:w.auxiliary .originalT=ys)
    (hr:∀k,w.rational (SemiprimeD1StackRationalOperation.adderStack k)=[])
    (hs:w.auxiliary .copyScratch=[]) :
    Runs program (runBound xs ys) (.local .equalQ) (bank w) (after xs ys) (bank w):=by
  let wl:Words:={w with rational:=Function.update w.rational (SemiprimeD1StackRationalOperation.adderStack .left) xs}
  have h0:=PTrace.copy_call .equalQ (.local .equalQ) (.local .equalT) rfl (bank w) xs [] hx (hr .left) hs
  change Runs program _ _ _ _ (Function.update (bank w)
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .left)) (xs++[])) at h0
  rw [List.append_nil,update_rational] at h0
  have h1:=PTrace.copy_call .equalT (.local .equalT) (.local .equal) rfl (bank wl) ys [] hy (hr .right) hs
  change Runs program _ _ _ _ (Function.update (bank wl)
    (rationalStack (SemiprimeD1StackRationalOperation.adderStack .right)) (ys++[])) at h1
  rw [List.append_nil,update_rational] at h1
  change Runs program _ _ _ _ (bank (prepared w xs ys)) at h1
  have hi:∀k,bank (prepared w xs ys) (rippleStack k)=SemiprimeD1StackAdder.store xs ys [] [] k:=by
    intro k;cases k
    · rfl
    · rfl
    · exact hr .scratch
    · exact hr .output
  have h2:=Ripple.equal_call (prepared w xs ys) xs ys hi
  rw [result_prepared] at h2
  have h3:=PTrace.pop_run (.local .equalRead) (.local .abort) (.local .index) (.local (.clearTransient false 0))
    (rippleStack .output)
    (bank (Ripple.result w [decide (SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys)]))
    [decide (SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys)] rfl rfl
  rw [SemiprimeD1StackRecoveryGridDecrement.update_output] at h3
  simp only [List.tail_cons] at h3
  rw [SemiprimeD1StackRecoveryGridDecrement.result_clean w hr] at h3
  have he:SemiprimeD1StackBytecode.choose (.local .abort) (.local .index) (.local (.clearTransient false 0))
      [decide (SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys)].head?=after xs ys:=by
    unfold after
    by_cases hv:SemiprimeBitArithmetic.bitValue xs=SemiprimeBitArithmetic.bitValue ys <;> simp [hv,SemiprimeD1StackBytecode.choose]
  rw [he] at h3
  exact PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
/-- Every physical input and mismatch-cleanup byte is charged in the same actual comparison run. -/
theorem runBound_le (xs ys:List Bool) :runBound xs ys≤100*(xs.length+ys.length+1):=by
  have h:=SemiprimeD1StackWordEqualExecution.executionTime_le xs ys
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridCompare
