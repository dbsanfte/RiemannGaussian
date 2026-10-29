/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationCalls
/-! # Actual temporary drains, normalization and two exact physical width fits -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationFinish
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackProcedureTrace
/-- Every retained acquired magnitude/cross-product is physically erased before GCD18 is entered. -/
def clean (w:Words) :Words:={w with leftMagnitude:=[],rightMagnitude:=[],originalLeft:=[],output:=[]}
/-- Four actual byte drains and four physical empty branches. -/
def cleanupTime (w:Words) :Nat:=
  (w.leftMagnitude.length+1)+(w.rightMagnitude.length+1)+(w.originalLeft.length+1)+(w.output.length+1)
/-- No live cross-product aliases either actual GCD input or output on entry to real Normalize22. -/
theorem cleanup_run (op:Op) (sx sy:Bool) (w:Words) :
    Runs program (cleanupTime w) (localLabel .clearMagnitudeLeft op sx sy) (bank w)
      (localLabel .normalize op sx sy) (bank (clean w)):=by
  have h0:=P.drain_loop (localLabel .clearMagnitudeLeft op sx sy) (localLabel .clearMagnitudeRight op sx sy)
    (aux .leftMagnitude) rfl (bank w) w.leftMagnitude rfl
  rw [update_leftMagnitude] at h0
  have h1:=P.drain_loop (localLabel .clearMagnitudeRight op sx sy) (localLabel .clearCrossLeft op sx sy)
    (aux .rightMagnitude) rfl (bank {w with leftMagnitude:=[]}) w.rightMagnitude rfl
  rw [update_rightMagnitude] at h1
  have h2:=P.drain_loop (localLabel .clearCrossLeft op sx sy) (localLabel .clearCrossRight op sx sy)
    crossLeft rfl (bank {w with leftMagnitude:=[],rightMagnitude:=[]}) w.originalLeft rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack SemiprimeD1StackRationalNormalize.numerator) []) at h2
  rw [update_originalLeft] at h2
  have h3:=P.drain_loop (localLabel .clearCrossRight op sx sy) (localLabel .normalize op sx sy)
    crossRight rfl (bank {w with leftMagnitude:=[],rightMagnitude:=[],originalLeft:=[]}) w.output rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack SemiprimeD1StackRationalNormalize.gcdOutput) []) at h3
  rw [update_output] at h3
  exact P.join (P.join (P.join h0 h1) h2) h3
/-- Exact proof-side normalized raw word from the already acquired actual two-word bank. -/
def normalized (negative:Bool) (num den:List Bool) :SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRationalNormalizeSpec.word negative num den
/-- Full stopped bank after both magnitude fits and raw-input erasure; normalized sign is retained verbatim. -/
def finishResult (w:Words) (negative:Bool) (num den:List Bool) :Words:=
  {normalizeReady w [] [] with signOutput:=[(normalized negative num den).numerator.negative],finalNumerator:=(SemiprimeBitDivision.fitBits (normalized negative num den).numerator.magnitude w.templateInput).bits,finalDenominator:=(SemiprimeBitDivision.fitBits (normalized negative num den).denominator w.templateInput).bits}
/-- Own elapsed clock pays real canonical normalization, two entire fits, both retained raw-input drains and returns. -/
def finishTime (num den template:List Bool) :Nat:=
  (SemiprimeD1StackRationalNormalizeExecution.runBound num den+1)+
    (SemiprimeD1StackWordFitExecution.totalTime (normalized false num den).numerator.magnitude template+1)+
    (SemiprimeD1StackWordFitExecution.totalTime (normalized false num den).denominator template+1)+
    ((num.length+1)+1)+(den.length+1)
/-- Normalized magnitude/denominator bytes do not depend on the parsed sign, including negative zero. -/
theorem normalized_magnitudes (negative:Bool) (num den:List Bool) :
    (normalized negative num den).numerator.magnitude=(normalized false num den).numerator.magnitude ∧
    (normalized negative num den).denominator=(normalized false num den).denominator:=by
  unfold normalized SemiprimeD1StackRationalNormalizeSpec.word
  split <;> exact ⟨rfl,rfl⟩
/-- The exact legacy reduced sign is preserved, and both magnitude byte strings are physically fitted. -/
theorem finish_run (op:Op) (sx sy:Bool) (w:Words) (negative:Bool) (num den:List Bool)
    (hn:w.finalNumerator=[]) (hd:w.finalDenominator=[]) :
    Runs program (finishTime num den w.templateInput) (localLabel .normalize op sx sy)
      (bank (normalizeReady w (negative::num) den)) (localLabel .done op sx sy)
      (bank (finishResult w negative num den)):=by
  let n:=normalized negative num den
  let w0:=normalizeDone w negative num den
  let w1:=fitDone w0 false n.numerator.magnitude w.templateInput
  let w2:=fitDone w1 true n.denominator w.templateInput
  have h0:=normalize_call w negative num den (localLabel .normalize op sx sy) (localLabel (.fit false) op sx sy) rfl
  have h1:=fit_call w0 false n.numerator.magnitude w.templateInput
    (localLabel (.fit false) op sx sy) (localLabel (.fit true) op sx sy) rfl
  have he1:fitReady w0 false n.numerator.magnitude w.templateInput=w0:=by
    simp only [fitReady,w0,normalizeDone,normalizeReady,n,normalized,Bool.false_eq_true,ite_false]
    rw [hn]
  rw [he1] at h1
  have h2:=fit_call w1 true n.denominator w.templateInput
    (localLabel (.fit true) op sx sy) (localLabel .clearRawSigned op sx sy) rfl
  have he2:fitReady w1 true n.denominator w.templateInput=w1:=by
    simp only [fitReady,w1,w0,normalizeDone,normalizeReady,fitDone,n,normalized,Bool.false_eq_true,ite_false,ite_true]
    rw [hd]
  rw [he2] at h2
  have h3:=P.drain_loop (localLabel .clearRawSigned op sx sy) (localLabel .clearRawDen op sx sy)
    rawSigned rfl (bank w2) (negative::num) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) []) at h3
  rw [update_originalSigned] at h3
  have h4:=P.drain_loop (localLabel .clearRawDen op sx sy) (localLabel .done op sx sy)
    rawDen rfl (bank {w2 with originalSigned:=[]}) den rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (normalizeStack SemiprimeD1StackRationalNormalize.denominator) []) at h4
  rw [update_originalRight] at h4
  have h:=P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
  have hm:=normalized_magnitudes negative num den
  dsimp only [normalized] at hm
  simpa only [finishTime,finishResult,hm.1,hm.2,List.length_cons,n,w2,w1,w0,fitDone,normalizeDone,normalizeReady,normalized,Bool.false_eq_true,ite_false,ite_true] using h
end RiemannGaussian.SemiprimeD1StackRationalOperationFinish
