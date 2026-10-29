/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersEncoding
/-! # Paid q acquisition, literal ONE seed and single final history reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersStages
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed)
open SemiprimeD1StackRecoveryPowersEncoding
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Literal seed does not pass through a fit, preserving native ONE even W0. -/
theorem seed_run (w:Words) (hn:w.added .currentSigned=[]) (hd:w.added .currentDen=[]):
    Runs program 3 (.local .seedMagnitude) (bank w) (.local (.frame true))
      (bank (SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent w SemiprimeJetBits.oneWord)):=by
  let w1:=put w .currentSigned [true]
  let w2:=put w1 .currentSigned [false,true]
  have h0:=PTrace.push_run (.local .seedMagnitude) (.local .seedSign) (aux .currentSigned) true (bank w) rfl
  rw [update_added] at h0
  change Runs program 1 _ _ _ (bank (put w .currentSigned (true::w.added .currentSigned))) at h0
  rw [hn] at h0
  have h1:=PTrace.push_run (.local .seedSign) (.local .seedDen) (aux .currentSigned) false (bank w1) rfl
  rw [update_added] at h1
  have h2:=PTrace.push_run (.local .seedDen) (.local (.frame true)) (aux .currentDen) true (bank w2) rfl
  rw [update_added] at h2
  change Runs program 1 _ _ _ (bank (put w2 .currentDen (true::w2.added .currentDen))) at h2
  have he:w2.added .currentDen=[]:=by simpa only [w2,w1,put,Function.update_of_ne (by decide:Aux.currentDen≠.currentSigned)] using hd
  rw [he] at h2
  have hend:put w2 .currentDen [true]=SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent w SemiprimeJetBits.oneWord:=by
    dsimp only [w2,w1,put,SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent]
    congr 1
    funext k
    cases k <;> simp [SemiprimeD1StackRecoveryPowersSpec.signed,SemiprimeJetBits.oneWord]
  rw [hend] at h2
  exact PTrace.join (PTrace.join h0 h1) h2
/-- Actual count-copy and EOF test take the zero case directly to the empty-vector finish. -/
theorem initialize_zero (argument:RationalWord) (width:List Bool):
    Runs program 5 (.local .start) (input (signed argument) argument.denominator [] width)
      (.local .terminal) (bank (stoppedWords argument 0 width [])):=by
  let w:=originals (signed argument) argument.denominator [] width
  have h0:=PTrace.copy_call .count (.local .start) (.local .first) rfl (bank w) [] [] rfl rfl rfl
  change Runs program 4 _ _ _ (Function.update (bank w) (aux .remaining) []) at h0
  have hu:Function.update (bank w) (aux .remaining) []=bank w:=Function.update_eq_self _ _
  rw [hu] at h0
  have h1:=PTrace.pop_run (.local .first) (.local .terminal) (.local .abort) (.local .seedMagnitude)
    (aux .remaining) (bank w) [] rfl rfl
  change Runs program 1 _ _ (.local .terminal) (Function.update (bank w) (aux .remaining) []) at h1
  rw [hu] at h1
  have he:bank w=bank (stoppedWords argument 0 width []):=by
    unfold stoppedWords put
    rw [←update_added]
    exact (Function.update_eq_self _ _).symm
  rw [←he]
  exact PTrace.join h0 h1
/-- Positive q acquires its own marker countdown and literal ONE with no extra arithmetic. -/
theorem initialize_succ (argument:RationalWord) (q:Nat) (width:List Bool):
    Runs program (5*(q+1)+8) (.local .start)
      (input (signed argument) argument.denominator (List.replicate (q+1) true) width)
      (.local (.frame true)) (bank (loopWords argument (q+1) width SemiprimeJetBits.oneWord q [])):=by
  let w:=originals (signed argument) argument.denominator (List.replicate (q+1) true) width
  let w1:=put w .remaining (List.replicate (q+1) true)
  let w2:=put w .remaining (List.replicate q true)
  have h0:=PTrace.copy_call .count (.local .start) (.local .first) rfl (bank w) (List.replicate (q+1) true) [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank w) (aux .remaining) (List.replicate (q+1) true++[])) at h0
  rw [List.append_nil,update_added,List.length_replicate] at h0
  have h1:=PTrace.pop_run (.local .first) (.local .terminal) (.local .abort) (.local .seedMagnitude)
    (aux .remaining) (bank w1) (true::List.replicate q true) rfl (by change Function.update w.added .remaining (List.replicate (q+1) true) .remaining=_;simp [List.replicate_succ])
  change Runs program 1 _ _ (.local .seedMagnitude) (Function.update (bank w1) (aux .remaining) (List.replicate q true)) at h1
  rw [update_added] at h1
  have he:put w1 .remaining (List.replicate q true)=w2:=by simp only [w1,w2,put,Function.update_idem]
  change Runs program 1 _ _ _ (bank (put w1 .remaining (List.replicate q true))) at h1
  rw [he] at h1
  have h2:=seed_run w2 rfl rfl
  have hout:SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent w2 SemiprimeJetBits.oneWord=
      loopWords argument (q+1) width SemiprimeJetBits.oneWord q []:=by
    unfold w2 w put originals SemiprimeD1StackRecoveryPowersOperationOutput.putCurrent loopWords
    congr 1
    funext k
    cases k <;> rfl
  rw [hout] at h2
  have hh:=PTrace.join (PTrace.join h0 h1) h2
  change Runs program (5*(q+1)+4+1+3) (.local .start)
    (input (signed argument) argument.denominator (List.replicate (q+1) true) width)
    (.local (.frame true)) (bank (loopWords argument (q+1) width SemiprimeJetBits.oneWord q [])) at hh
  simpa only [Nat.add_assoc] using hh
/-- The actual FALSE terminal is pushed only once; consuming reverse preserves exact chronological payload. -/
theorem finish_run (argument:RationalWord) (q:Nat) (width hist:List Bool):
    Runs program (2*hist.length+4) (.local .terminal) (bank (stoppedWords argument q width hist)) (.local .done)
      (Function.update (input (signed argument) argument.denominator (List.replicate q true) width)
        (aux .output) (hist.reverse++[false])):=by
  let w:=stoppedWords argument q width hist
  let w1:=put w .output [false]
  have h0:=PTrace.push_run (.local .terminal) (.local .reverse) (aux .output) false (bank w) rfl
  rw [update_added] at h0
  have h1:=PTrace.reverse_call true (.local .reverse) (.local .done) rfl (bank w1) hist [false] rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank w1) (aux .history) []) (aux .output) (hist.reverse++[false])) at h1
  rw [update_added,update_added] at h1
  have he:put (put w1 .history []) .output (hist.reverse++[false])=
      put (originals (signed argument) argument.denominator (List.replicate q true) width) .output (hist.reverse++[false]):=by
    dsimp only [w1,w,stoppedWords,put]
    congr 1
    funext k
    cases k <;> simp [originals]
  change Runs program _ _ _ _ (bank (put (put w1 .history []) .output (hist.reverse++[false]))) at h1
  rw [he] at h1
  change Runs program _ _ _ _ (bank {originals (signed argument) argument.denominator (List.replicate q true) width with
    added:=Function.update (originals (signed argument) argument.denominator (List.replicate q true) width).added .output (hist.reverse++[false])}) at h1
  rw [←update_added,originals_bank] at h1
  convert PTrace.join h0 h1 using 1
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryPowersStages
