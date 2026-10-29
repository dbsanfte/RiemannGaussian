/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
/-! # Real matching terminator/EOF checks, final reverse and true status
Four actual source instructions verify both vector terminators and both EOFs.
Only after every operation finishes is the idle cleared scratch used as status.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankFinish
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackCachePhaseBankPrimitives SemiprimeD1StackProcedureTrace
/-- Four physical terminator/EOF checks, a real reversal/call-return, then one true push. -/
def finishTime (history:List Bool):Nat:=4+(2*history.length+3)+1
/-- Complete successful finish reaches the real final-halt label, retaining the original four operand words. -/
theorem finish_run (bank:P.Stack→List Bool) (hs:bank P.copyScratch=[])
    (refs children history out:List Bool):
    Runs program (finishTime history) (.local .header)
      (data bank (words {references:=refs,children:=children,referenceReader:=[false],childReader:=[false],history:=history,output:=out})) (.local .done)
      (Function.update (data bank (words {references:=refs,children:=children,output:=history.reverse++out})) status [true]):=by
  let v:Words:={references:=refs,children:=children,referenceReader:=[false],childReader:=[false],history:=history,output:=out}
  let noRef:Words:={v with referenceReader:=[]}
  let ready:Words:={noRef with childReader:=[]}
  let doneWords:Words:={references:=refs,children:=children,output:=history.reverse++out}
  have h0:=pop_run .header (.local .abort) (.local .referenceEOF) (.local .referenceField) (aux .referenceReader)
    (data bank (words v)) [false] rfl rfl
  change Runs program 1 _ _ (.local .referenceEOF) (Function.update (data bank (words v)) (aux .referenceReader) []) at h0
  rw [←data_update_aux,words_update] at h0
  have h1:=peek_run .referenceEOF (.local .childTail) (.local .abort) (.local .abort) (aux .referenceReader)
    (data bank (words noRef)) [] rfl rfl
  change Runs program 1 _ _ (.local .childTail) _ at h1
  have h2:=pop_run .childTail (.local .abort) (.local .childEOF) (.local .abort) (aux .childReader)
    (data bank (words noRef)) [false] rfl rfl
  change Runs program 1 _ _ (.local .childEOF) (Function.update (data bank (words noRef)) (aux .childReader) []) at h2
  rw [←data_update_aux,words_update] at h2
  have h3:=peek_run .childEOF (.local .finish) (.local .abort) (.local .abort) (aux .childReader)
    (data bank (words ready)) [] rfl rfl
  change Runs program 1 _ _ (.local .finish) _ at h3
  have h4:=reverse_call true .finish .accept rfl (data bank (words ready)) history out rfl rfl
  change Runs program (2*history.length+3) _ _ _
    (Function.update (Function.update (data bank (words ready)) (aux .history) []) (aux .output) (history.reverse++out)) at h4
  rw [←data_update_aux,←data_update_aux,words_update,words_update] at h4
  have h5:=push_run .accept (.local .done) status true (data bank (words doneWords)) rfl
  change Runs program 1 _ _ _ (Function.update (data bank (words doneWords)) status (true::bank P.copyScratch)) at h5
  rw [hs] at h5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  exact h
end RiemannGaussian.SemiprimeD1StackCachePhaseBankFinish
