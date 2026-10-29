/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDBody
/-! # The real acquired-fuel Euclid loop and its own chronological instruction count -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDLoop
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding SemiprimeD1StackEuclidGCDCalls
open SemiprimeD1StackEuclidGCDBody SemiprimeD1StackEuclidGCDSpec
open SemiprimeD1StackProcedureTrace
/-- Sum of actual finite-source fragments, not a legacy report or supplied clock operand. -/
def loopTime :Nat→List Bool→List Bool→Nat
  | 0,_,_=>0
  | n+1,x,y=>if y=[] then finishTime (List.replicate n true) x else
      stepTime x y+loopTime n y (SemiprimeD1StackSourceEnvironmentEncoding.normalize (SemiprimeBitDivision.divideLoop x y).remainder)
/-- Sufficient fuel is a theorem about the original input bytes; every loop step consumes its real marker. -/
theorem loop_run (n:Nat) (left right xs ys:List Bool) (hs:(iterate n xs ys).exhausted=false) :
    Runs program (loopTime n xs ys) .loop
      (bank (loopWords left right (List.replicate n true) xs ys)) .done
      (bank {originalLeft:=left,originalRight:=right,output:=(iterate n xs ys).word}) :=by
  induction n generalizing xs ys with
  | zero=>simp only [iterate,Bool.true_eq_false] at hs
  | succ n ih=>
    by_cases hz:ys=[]
    · subst ys
      simpa only [loopTime,iterate,ite_true,List.replicate_succ] using finish_run left right (List.replicate n true) xs
    · have hstep:=step_run left right (List.replicate n true) xs ys hz
      have hchild:(iterate n ys (SemiprimeD1StackSourceEnvironmentEncoding.normalize
          (SemiprimeBitDivision.divideLoop xs ys).remainder)).exhausted=false:=by
        simpa only [iterate,ite_eq_right hz] using hs
      have h:=P.join hstep (ih ys _ hchild)
      simpa only [loopTime,iterate,ite_eq_right hz,List.replicate_succ] using h
/-- The actual current word widths never grow across a complete restoring division and physical trim. -/
theorem next_width (xs ys:List Bool) :
    (SemiprimeD1StackSourceEnvironmentEncoding.normalize (SemiprimeBitDivision.divideLoop xs ys).remainder).length≤ ys.length:=by
  exact (SemiprimeD1StackSourceEnvironmentEncoding.normalize_length _).trans_eq
    (SemiprimeBitDivision.divideLoop_widths xs ys).1
/-- A single positive iteration is bounded by its real binary-operand lengths, independently of numeric values. -/
theorem stepTime_le (xs ys:List Bool) (s:Nat) (hs:1≤ s) (hx:xs.length≤ s) (hy:ys.length≤ s) :
    stepTime xs ys≤1000*s^2:=by
  have hd:=SemiprimeD1StackDividerExecution.source_time xs ys
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le (SemiprimeBitDivision.divideLoop xs ys).remainder.reverse
  have hw:=SemiprimeBitDivision.divideLoop_widths xs ys
  simp only [List.length_reverse] at ht
  unfold stepTime SemiprimeD1StackDividerExecution.timeBound at *
  rw [hw.1,hw.2.1] at *
  have hm:xs.length*(ys.length+2)≤ s*(s+2):=Nat.mul_le_mul hx (Nat.add_le_add_right hy 2)
  nlinarith [sq_nonneg (s-1:ℤ)]
/-- The terminal normalization pays remaining acquired fuel erasure as well as every binary byte. -/
theorem finishTime_le (n:Nat) (xs:List Bool) (s:Nat) (hs:1≤ s) (hx:xs.length≤ s) :
    finishTime (List.replicate n true) xs≤ n+20*s:=by
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le xs.reverse
  simp only [List.length_reverse] at ht
  simp only [finishTime,List.length_replicate]
  omega
/-- The source's real recursive budget has a uniform polynomial cap on physically acquired fuel and widths. -/
theorem loopTime_le (n:Nat) (xs ys:List Bool) (s:Nat) (hs:1≤ s) (hx:xs.length≤ s) (hy:ys.length≤ s) :
    loopTime n xs ys≤ n*(1000*s^2+20*s+1):=by
  induction n generalizing xs ys with
  | zero=>simp only [loopTime,Nat.zero_mul,le_refl]
  | succ n ih=>
    by_cases hz:ys=[]
    · rw [loopTime,ite_eq_left hz]
      have hf:=finishTime_le n xs s hs hx
      have hsq:s≤ s^2:=by nlinarith
      nlinarith
    · rw [loopTime,ite_eq_right hz]
      have hi:=ih ys _ hy ((next_width xs ys).trans hy)
      have hb:=stepTime_le xs ys s hs hx hy
      nlinarith
end RiemannGaussian.SemiprimeD1StackEuclidGCDLoop
