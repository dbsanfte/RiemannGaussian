/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersEncoding
/-! # Complete physical cached-power loop and exact chronological history invariant -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersLoop
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed row next suffix)
open SemiprimeD1StackRecoveryPowersEncoding
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- The final current word is physically drained on both tapes, including the two EOF branches. -/
theorem clear_run (w:Words):
    Runs program ((w.added .currentSigned).length+1+(w.added .currentDen).length+1)
      (.local (.finishCurrent false)) (bank w) (.local .terminal)
      (bank (SemiprimeD1StackRecoveryPowersOperationOutput.emptyCurrent w)):=by
  let w1:=put w .currentSigned []
  have h0:=PTrace.drain_loop (.local (.finishCurrent false)) (.local (.finishCurrent true)) (aux .currentSigned) rfl
    (bank w) (w.added .currentSigned) rfl
  rw [update_added] at h0
  have h1:=PTrace.drain_loop (.local (.finishCurrent true)) (.local .terminal) (aux .currentDen) rfl
    (bank w1) (w.added .currentDen) rfl
  rw [update_added] at h1
  simpa only [Nat.add_assoc,w1,put,SemiprimeD1StackRecoveryPowersOperationOutput.emptyCurrent] using PTrace.join h0 h1
/-- Literal cleanup endpoint agrees with the complete47-word stopped invariant. -/
theorem clear_loop (argument:RationalWord) (q:Nat) (width:List Bool) (current:RationalWord) (hist:List Bool):
    SemiprimeD1StackRecoveryPowersOperationOutput.emptyCurrent (loopWords argument q width current 0 hist)=
      stoppedWords argument q width hist:=by
  unfold SemiprimeD1StackRecoveryPowersOperationOutput.emptyCurrent loopWords stoppedWords put originals
  congr 1
  funext k
  cases k <;> rfl
/-- One sequential recurrence acquires ALL requested rows and no unused final product.
History is reverse payload, retaining the complete old tail byte for byte. -/
theorem loop_run (argument:RationalWord) (q:Nat) (width:List Bool) (remaining:Nat) (current:RationalWord) (hist:List Bool):
    ∃time≤loopBound argument q width current hist remaining,
      Runs program time (.local (.frame true)) (bank (loopWords argument q width current remaining hist)) (.local .terminal)
        (bank (stoppedWords argument q width ((payload (suffix width argument current (remaining+1))).reverse++hist))):=by
  induction remaining generalizing current hist with
  | zero=>
    let logged:Words:=loopWords argument q width current 0 ((row current).reverse++hist)
    have h0:=SemiprimeD1StackRecoveryPowersRow.row_run (loopWords argument q width current 0 hist) current rfl rfl rfl rfl
    rw [loop_history] at h0
    have h1:=PTrace.pop_run (.local .next) (.local (.finishCurrent false)) (.local .abort) (.local (.input false false))
      (aux .remaining) (bank logged) [] rfl rfl
    have he:Function.update (bank logged) (aux .remaining) []=bank logged:=by
      exact Function.update_eq_self (aux .remaining) (bank logged)
    change Runs program 1 _ _ (.local (.finishCurrent false)) (Function.update (bank logged) (aux .remaining) []) at h1
    rw [he] at h1
    have h2:=clear_run logged
    rw [clear_loop] at h2
    have hh:=PTrace.join (PTrace.join h0 h1) h2
    refine ⟨_,le_rfl,?_⟩
    simpa only [loopBound,logged,loopWords,suffix,payload,List.flatMap_cons,List.flatMap_nil,List.append_nil,Nat.add_assoc] using hh
  | succ n ih=>
    let logged:Words:=loopWords argument q width current (n+1) ((row current).reverse++hist)
    let prepared:Words:=loopWords argument q width current n ((row current).reverse++hist)
    have h0:=SemiprimeD1StackRecoveryPowersRow.row_run (loopWords argument q width current (n+1) hist) current rfl rfl rfl rfl
    rw [loop_history] at h0
    have h1:=PTrace.pop_run (.local .next) (.local (.finishCurrent false)) (.local .abort) (.local (.input false false))
      (aux .remaining) (bank logged) (true::List.replicate n true) rfl (by change List.replicate (n+1) true=true::List.replicate n true; rw [List.replicate_succ])
    change Runs program 1 _ _ (.local (.input false false))
      (Function.update (bank logged) (aux .remaining) (List.replicate n true)) at h1
    rw [update_added] at h1
    change Runs program 1 _ _ _ (bank (put logged .remaining (List.replicate n true))) at h1
    rw [loop_remaining] at h1
    obtain ⟨m,hm,h2⟩:=SemiprimeD1StackRecoveryPowersOperation.operation_run prepared
      current.numerator.negative current.numerator.magnitude current.denominator
      argument.numerator.negative argument.numerator.magnitude argument.denominator width rfl rfl rfl rfl rfl rfl
    rw [SemiprimeD1StackRecoveryPowersOperationOutput.word_legacy] at h2
    change Runs program m _ _ _ (bank (SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent prepared (next width argument current))) at h2
    rw [loop_current] at h2
    obtain ⟨s,hs,h3⟩:=ih (next width argument current) ((row current).reverse++hist)
    have hh:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
    refine ⟨SemiprimeD1StackRecoveryPowersRow.timeBound current+1+m+s,?_,?_⟩
    · dsimp only [loopBound]
      dsimp only [prepared] at hm
      omega
    · simpa only [suffix,payload,List.flatMap_cons,List.reverse_append,List.append_assoc] using hh
end RiemannGaussian.SemiprimeD1StackRecoveryPowersLoop
