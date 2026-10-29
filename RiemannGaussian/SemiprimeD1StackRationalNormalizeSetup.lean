/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeCalls
/-! # Paid two-word sign acquisition and actual total denominator guard -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalNormalizeSetup
open SemiprimeD1StackRationalNormalize SemiprimeD1StackRationalNormalizeEncoding SemiprimeD1StackRationalNormalizeCalls
open SemiprimeD1StackProcedureTrace
/-- The actual OR scan consumes every copied denominator byte, including high-zero padding. -/
theorem scan_run (seen:Bool) (w:Words) (xs:List Bool) :
    Runs program (xs.length+1) (.scan seen) (bank {w with scan:=xs})
      (if seen||(SemiprimeBitDivision.nonzeroBits xs).nonzero then .gcdCall else .zeroClearSign)
      (bank {w with scan:=[]}) :=by
  induction xs generalizing seen with
  | nil=>
    have h:=P.pop_run (.scan seen) (if seen then .gcdCall else .zeroClearSign) (.scan seen) (.scan true)
      scan (bank {w with scan:=[]}) [] rfl rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .scan)) []) at h
    rw [update_scan] at h
    change Runs program 1 (.scan seen) (bank {w with scan:=[]})
      (if seen then .gcdCall else .zeroClearSign) (bank {w with scan:=[]}) at h
    simpa only [SemiprimeBitDivision.nonzeroBits,Bool.or_false,List.length_nil,Nat.zero_add] using h
  | cons b xs ih=>
    have h0:=P.pop_run (.scan seen) (if seen then .gcdCall else .zeroClearSign) (.scan seen) (.scan true)
      scan (bank {w with scan:=b::xs}) (b::xs) rfl rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .scan)) xs) at h0
    rw [update_scan] at h0
    cases b with
    | false=>
      have h:=P.join h0 (ih seen)
      simpa only [List.length_cons,SemiprimeBitDivision.nonzeroBits,Bool.false_or,Nat.add_comm] using h
    | true=>
      have h:=P.join h0 (ih true)
      simpa only [List.length_cons,SemiprimeBitDivision.nonzeroBits,Bool.true_or,Bool.or_true,Nat.add_comm] using h
/-- Exact actual clock for preserving-copy/sign-pop/sign-push plus preserving-copy/full denominator scan. -/
def setupTime (num den:List Bool) :Nat:=(5*(num.length+1)+4)+1+1+(5*den.length+4)+(den.length+1)
/-- Original signed word and denominator are the ONLY two initialized operands; magnitude/sign are acquired by real instructions. -/
theorem setup_run (negative:Bool) (num den:List Bool) :
    Runs program (setupTime num den) .start (input (negative::num) den)
      (if (SemiprimeBitDivision.nonzeroBits den).nonzero then .gcdCall else .zeroClearSign)
      (bank (parsed negative num den)) :=by
  rw [initial_bank]
  have h0:=P.copy_call .signedInput .start .parseSign rfl
    (bank {originalSigned:=negative::num,originalRight:=den}) (negative::num) [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .left)) ((negative::num)++[])) at h0
  rw [List.append_nil,update_originalLeft] at h0
  have h1:=P.pop_run .parseSign .abort (.initializeSign false) (.initializeSign true) numerator
    (bank {originalSigned:=negative::num,originalRight:=den,originalLeft:=negative::num}) (negative::num) rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .left)) num) at h1
  rw [update_originalLeft] at h1
  have he:SemiprimeD1StackBytecode.choose Label.abort (.initializeSign false) (.initializeSign true) (negative::num).head?=
      .initializeSign negative:=by cases negative <;> rfl
  rw [he] at h1
  have h2:=P.push_run (.initializeSign negative) .guardDen (aux .signOutput) negative
    (bank {originalSigned:=negative::num,originalRight:=den,originalLeft:=num}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .signOutput) [negative]) at h2
  rw [update_signOutput] at h2
  have h3:=P.copy_call .guard .guardDen (.scan false) rfl (bank (parsed negative num den)) den [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .scan)) (den++[])) at h3
  rw [List.append_nil,update_scan] at h3
  have h4:=scan_run false (parsed negative num den) den
  have h:=P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
  simpa only [setupTime,List.length_cons,Bool.false_or,parsed] using h
/-- A numeric-zero physical denominator takes the literal legacy zero branch, clearing its acquired sign and magnitude. -/
theorem zero_run (negative:Bool) (num den:List Bool) :
    Runs program (2+1+1+(num.length+1)) .zeroClearSign (bank (parsed negative num den)) .done
      (bank {originalSigned:=negative::num,originalRight:=den,signOutput:=[false],denominatorOutput:=[true]}) :=by
  have h0:=P.drain_loop .zeroClearSign .zeroSign (aux .signOutput) rfl (bank (parsed negative num den)) [negative] rfl
  rw [update_signOutput] at h0
  have h1:=P.push_run .zeroSign .zeroDen (aux .signOutput) false
    (bank {originalSigned:=negative::num,originalRight:=den,originalLeft:=num}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .signOutput) [false]) at h1
  rw [update_signOutput] at h1
  have h2:=P.push_run .zeroDen .clearMagnitude (aux .denominatorOutput) true
    (bank {originalSigned:=negative::num,originalRight:=den,originalLeft:=num,signOutput:=[false]}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .denominatorOutput) [true]) at h2
  rw [update_denominatorOutput] at h2
  have h3:=P.drain_loop .clearMagnitude .done numerator rfl
    (bank {originalSigned:=negative::num,originalRight:=den,originalLeft:=num,signOutput:=[false],denominatorOutput:=[true]}) num rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (gcdStack (SemiprimeD1StackEuclidGCD.aux .left)) []) at h3
  rw [update_originalLeft] at h3
  exact P.join (P.join (P.join h0 h1) h2) h3
end RiemannGaussian.SemiprimeD1StackRationalNormalizeSetup
