/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerStep
import RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolution
/-! # Complete actual descending-k convolution, with physical marker pops and all real source calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerLoop
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCache (counter put_counter update_counter)
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
open SemiprimeD1StackRecoveryAffinePairMeaning (step)
/-- Whole-loop proof clock is the sum of the same source iterations and actual marker pops. -/
def runBound (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord)
    (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (n:Nat) (suffix:SemiprimeRationalBits.RationalWord):Nat:=
  SemiprimeD1StackRecoveryAffineInnerStep.runBound part (counter w n) xs n c suffix width+1+
    match n with
    | 0=>0
    | n+1=>runBound (nextPart part) w xs c width n
      (step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs (n+1))
        (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix)
/-- Every k through zero is read and evaluated by the SAME fixed actual program; no zero terms are skipped. -/
theorem source_run (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c suffix:SemiprimeRationalBits.RationalWord) (width:List Bool)
    (ha:w.added .array=vector xs) (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width)
    (hs:w.registers (.slope,false)=signed c) (hd:w.registers (.slope,true)=c.denominator):
    ∃q≤runBound part w xs c width n suffix,
      Runs program q (.local (.inner part)) (bank (putReg (counter w n) .denPower suffix))
        (.local (.frame (.coefficient true)))
        (bank (putReg (counter w 0) .denPower
          (SemiprimeD1StackRecoveryAffineConvolution.descend width xs c part n suffix))):=by
  induction n generalizing part suffix with
  | zero=>
    obtain ⟨t,htime,h0⟩:=SemiprimeD1StackRecoveryAffineInnerStep.source_run part (counter w 0) xs 0 c suffix width
      ha (by simp only [counter,Function.update_self]) hrd ht hx hy hp hc hf hv hr hs hd
    let answer:=step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs 0)
      (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix
    have h1:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local (.innerNext part))
      (.local (.frame (.coefficient true))) (.local .abort) (.local (.inner (nextPart part))) (aux .k)
      (bank (counter (putReg w .denPower answer) 0)) [] rfl rfl
    change Runs program 1 _ _ (.local (.frame (.coefficient true)))
      (Function.update (bank (counter (putReg w .denPower answer) 0)) (aux .k) (unary 0)) at h1
    rw [update_counter] at h1
    rw [←put_counter] at h1
    refine ⟨t+1,?_,SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1⟩
    change t+1≤SemiprimeD1StackRecoveryAffineInnerStep.runBound part (counter w 0) xs 0 c suffix width+1+0
    omega
  | succ n ih=>
    obtain ⟨t,htime,h0⟩:=SemiprimeD1StackRecoveryAffineInnerStep.source_run part (counter w (n+1)) xs (n+1) c suffix width
      ha (by simp only [counter,Function.update_self]) hrd ht hx hy hp hc hf hv hr hs hd
    let answer:=step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs (n+1))
      (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix
    have h1:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local (.innerNext part))
      (.local (.frame (.coefficient true))) (.local .abort) (.local (.inner (nextPart part))) (aux .k)
      (bank (counter (putReg w .denPower answer) (n+1))) (true::unary n) rfl
      (by simp [bank,counter,aux,unary,List.replicate_succ])
    change Runs program 1 _ _ (.local (.inner (nextPart part)))
      (Function.update (bank (counter (putReg w .denPower answer) (n+1))) (aux .k) (unary n)) at h1
    rw [update_counter] at h1
    rw [←put_counter,←put_counter] at h1
    obtain ⟨s,hstime,h2⟩:=ih (nextPart part) answer
    refine ⟨t+1+s,?_,SemiprimeD1StackRecoveryAffinePrimitives.join
      (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2⟩
    change t+1+s≤SemiprimeD1StackRecoveryAffineInnerStep.runBound part (counter w (n+1)) xs (n+1) c suffix width+1+
      runBound (nextPart part) w xs c width n answer
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerLoop
