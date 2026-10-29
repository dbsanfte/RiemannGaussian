/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndices
/-! # Actual paid unary subtraction derives q-j before any coefficient read
Only the caller's copies of originalq and its physically remaining j are
consumed. Neither q-j nor a decoded count is a source or instruction operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsSubtract
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
/-- Exact proof view of two physically copied marker words. -/
def buffers (w:Words) (terms todo:Nat):Words:=
  {w with auxiliary:=Function.update (Function.update w.auxiliary .terms (unary terms)) .readTodo (unary todo)}
/-- One real copied-j pop changes only its actual physical word. -/
theorem update_todo (w:Words) (terms todo next:Nat):
    Function.update (bank (buffers w terms todo)) (aux .readTodo) (unary next)=bank (buffers w terms next):=by
  rw [update_aux]
  change bank {w with auxiliary:=Function.update (Function.update (Function.update w.auxiliary .terms (unary terms)) .readTodo (unary todo)) .readTodo (unary next)}=_
  rw [Function.update_idem]
  rfl
/-- One real q-marker pop changes only its actual physically remaining count. -/
theorem update_terms (w:Words) (terms todo next:Nat):
    Function.update (bank (buffers w terms todo)) (aux .terms) (unary next)=bank (buffers w next todo):=by
  rw [update_aux]
  apply congrArg (fun f:I.Aux→List Bool=>bank {w with auxiliary:=f})
  funext k
  cases k <;> simp [buffers]
/-- Actual paired TRUE pops acquire the difference, paying the final real j-EOF branch. -/
theorem subtract_run (w:Words) (remaining j:Nat):
    Runs program (2*j+1) (.local .subtract) (bank (buffers w (remaining+j) j)) (.local .copyA)
      (bank (buffers w remaining 0)):=by
  induction j with
  | zero=>
    have h:=P.pop_run (.local .subtract) (.local .copyA) abort (.local .removeTerm) (aux .readTodo)
      (bank (buffers w (remaining+0) 0)) [] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank (buffers w (remaining+0) 0)) (aux .readTodo) (unary 0)) at h
    rw [update_todo] at h
    exact h
  | succ j ih=>
    have h0:=P.pop_run (.local .subtract) (.local .copyA) abort (.local .removeTerm) (aux .readTodo)
      (bank (buffers w (remaining+(j+1)) (j+1))) (true::unary j) rfl (by
        change Function.update (Function.update w.auxiliary .terms (unary (remaining+(j+1)))) .readTodo (unary (j+1)) .readTodo=_
        simp [unary,List.replicate_succ])
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_todo] at h0
    have h1:=P.pop_run (.local .removeTerm) abort abort (.local .subtract) (aux .terms)
      (bank (buffers w (remaining+(j+1)) j)) (true::unary (remaining+j)) rfl (by
        change Function.update (Function.update w.auxiliary .terms (unary (remaining+(j+1)))) .readTodo (unary j) .terms=_
        rw [Function.update_of_ne (by decide),Function.update_self]
        change List.replicate (remaining+(j+1)) true=true::List.replicate (remaining+j) true
        rw [show remaining+(j+1)=(remaining+j)+1 by omega,List.replicate_succ])
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
    rw [update_terms] at h1
    have h:=P.join (P.join h0 h1) ih
    convert h using 1
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsSubtract
