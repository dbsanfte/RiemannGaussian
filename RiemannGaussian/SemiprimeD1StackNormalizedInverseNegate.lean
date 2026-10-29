/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficientFrame
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterClear
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterAlgebra
/-! # Actual coefficient negation, frame-before-clear and complete register disposal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseNegate
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseOperationCall
open SemiprimeD1StackNormalizedInverseCoefficientFrame SemiprimeD1StackNormalizedInverseRegisterClear
open SemiprimeD1StackNormalizedInverseRegisterAlgebra SemiprimeD1StackProcedureTrace
open SemiprimeD1StackNormalizedInverseCleanup (mass)
/-- Native byte specification of the actual final normalized/fitted negation. -/
def output (w : Words) (width : List Bool) : SemiprimeRationalBits.RationalWord :=
  (SemiprimeRationalBits.executeOperation .neg (getReg w .acc) SemiprimeRationalBits.zeroWord width).word
/-- Actual acquired negation followed by both executed preserving Frames. -/
def beforeClear (w : Words) (width : List Bool) : Words :=
  framed (after .negate (putReg w .right SemiprimeRationalBits.zeroWord) width) (output w width)
/-- Complete coefficient result, with all eight physical cache fields actually drained. -/
def result (w : Words) (width : List Bool) : Words :=
  {w with registers:=fun _=>[],auxiliary:=Function.update w.auxiliary .prefixReverse (row (output w width) (w.auxiliary .prefixReverse))}
/-- Own sum of literal seed, whole arithmetic call, real framing and eight physical drains. -/
def negateBound (w : Words) (width : List Bool) : ℕ :=
  2+callBound .negate (putReg w .right SemiprimeRationalBits.zeroWord) width+
    (6*((signed (output w width)).length+(output w width).denominator.length)+11)+
    8*(mass (store (beforeClear w width))+1)
/-- The real ZERO right-operand seed is independent of W and does not consult any supplied value. -/
theorem seed_run (w : Words) (hn : w.registers (.right,false)=[]) (hd : w.registers (.right,true)=[]) :
    Runs program 2 (ctl (.seedNeg false)) (store w) (ctl (.operate .negate))
      (store (putReg w .right SemiprimeRationalBits.zeroWord)) := by
  let middle : Words := {w with registers:=Function.update w.registers (.right,false) [false]}
  have h0:=PTrace.push_run (ctl (.seedNeg false)) (ctl (.seedNeg true)) (reg .right false) false (store w) rfl
  change Runs program 1 _ _ _ (Function.update (store w) (reg .right false) (false::w.registers (.right,false))) at h0
  rw [hn,update_register] at h0
  have h1:=PTrace.push_run (ctl (.seedNeg true)) (ctl (.operate .negate)) (reg .right true) true (store middle) rfl
  have he:store middle (reg .right true)=[] := by
    change Function.update w.registers (.right,false) [false] (.right,true)=[]
    simpa only [Function.update_apply,Prod.mk.injEq,eq_self,true_and,Bool.true_eq_false,ite_false] using hd
  rw [he,update_register] at h1
  exact PTrace.join h0 h1
/-- Byte equality uses the literal unary negation site, not a commuted or aggregate operation. -/
theorem acquired_eq (w : Words) (width : List Bool) :
    acquired .negate (putReg w .right SemiprimeRationalBits.zeroWord) width=output w width := by
  change (SemiprimeRationalBits.executeOperation .neg
    (getReg (putReg w .right SemiprimeRationalBits.zeroWord) .acc)
    (getReg (putReg w .right SemiprimeRationalBits.zeroWord) .right) width).word=_
  rw [getReg_other _ .right .acc _ (by decide),getReg_put]
  rfl
/-- Complete real coefficient acquisition reaches bump only after BOTH field frames and ALL eight cache drains. -/
theorem negate_run (w : Words) (width : List Bool) (hr : w.rational=emptyRational width)
    (hc : w.auxiliary .copyScratch=[]) (hv : w.auxiliary .valid=[]) (hs : w.auxiliary .fieldFrameScratch=[])
    (hn : w.registers (.right,false)=[]) (hd : w.registers (.right,true)=[])
    (hacc : w.registers (.acc,false)≠[]) :
    ∃q≤negateBound w width,Runs program q (ctl (.seedNeg false)) (store w) (ctl .bump) (store (result w width)) := by
  let ready:=putReg w .right SemiprimeRationalBits.zeroWord
  let stopped:=after .negate ready width
  have h0:=seed_run w hn hd
  have hca : ready.registers (.acc,false)≠[] := by
    rw [putReg_other _ .right .acc _ false (by decide)]
    exact hacc
  obtain ⟨q1,hq1,h1⟩:=operation_call .negate (ctl (.operate .negate)) (ctl (.operated .negate))
    (ctl (.frameCoefficient true)) (ctl (.abort 0)) rfl rfl ready width hr hc hv hca (putReg_nonempty w .right _)
  have hword : acquired .negate ready width=output w width := acquired_eq w width
  have hsigned : stopped.registers (.acc,false)=signed (output w width) := by
    change (putReg ready .acc (acquired .negate ready width)).registers (.acc,false)=_
    rw [(putReg_fields ready .acc _).1,hword]
  have hden : stopped.registers (.acc,true)=(output w width).denominator := by
    change (putReg ready .acc (acquired .negate ready width)).registers (.acc,true)=_
    rw [(putReg_fields ready .acc _).2,hword]
  have h2:=frame_run stopped (output w width) hsigned hden hs
  obtain ⟨q3,hq3,h3⟩:=registers_run (beforeClear w width)
  have he : ({beforeClear w width with registers:=fun _=>[]}:Words)=result w width := rfl
  rw [he] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  refine ⟨2+q1+(6*((signed (output w width)).length+(output w width).denominator.length)+11)+q3,?_,h⟩
  unfold negateBound
  dsimp only [ready] at hq1
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseNegate
