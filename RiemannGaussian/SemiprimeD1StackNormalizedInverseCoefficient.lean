/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrepare
import RiemannGaussian.SemiprimeD1StackNormalizedInverseInner
import RiemannGaussian.SemiprimeD1StackNormalizedInverseNegate
/-! # Complete actual noninitial inverse coefficient from the retained arrays and built-prefix count -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficient
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInversePrepare SemiprimeD1StackNormalizedInverseInner
open SemiprimeD1StackNormalizedInverseIndices SemiprimeD1StackNormalizedInverseRecurrence
open SemiprimeD1StackNormalizedInverseRegisterAlgebra SemiprimeD1StackProcedureTrace
namespace Neg
export SemiprimeD1StackNormalizedInverseNegate (negateBound negate_run output result)
end Neg
/-- The three actual pair counters are empty again when the complete descending loop ends. -/
theorem counters_empty (w : Words) (ht : w.auxiliary .terms=[]) (ha : w.auxiliary .aIndex=[])
    (hb : w.auxiliary .bIndex=[]) : counters w 0 0 0=w := by
  apply congrArg (fun f=>({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [unary,ht,ha,hb]
/-- Exact raw final coefficient, including every native fit, is a proof specification only. -/
def nextWord (width : List Bool) (a reversed : List SemiprimeRationalBits.RationalWord) (n : ℕ) :
    SemiprimeRationalBits.RationalWord :=
  (SemiprimeRationalBits.executeOperation .neg (dotLoop width a.toArray reversed n SemiprimeRationalBits.zeroWord)
    SemiprimeRationalBits.zeroWord width).word
/-- Exact all-cache-empty endpoint with one actual framed row prepended to the acquired prefix. -/
def result (w : Words) (word : SemiprimeRationalBits.RationalWord) : Words :=
  {w with registers:=fun _=>[],auxiliary:=Function.update w.auxiliary .prefixReverse (row word (w.auxiliary .prefixReverse))}
/-- Sum of this SAME literal source's preparation, inner dot and final negation/framing/cleanup caps. -/
def coefficientBound (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool) (n : ℕ) : ℕ :=
  (15*n+15)+innerBound w a reversed width n SemiprimeRationalBits.zeroWord+
    Neg.negateBound (putReg w .acc (dotLoop width a.toArray reversed n SemiprimeRationalBits.zeroWord)) width
/-- Whole coefficient: all query indices come from paid copies of the ACTUAL built-prefix markers. -/
theorem coefficient_run (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (width : List Bool)
    (n : ℕ) (hn : 0<n) (hr : w.rational=emptyRational width)
    (ha : store w (readSource .denominator)=tape a) (hb : store w (readSource .prefix)=tape reversed)
    (hbuilt : w.auxiliary .built=unary n)
    (hterms : w.auxiliary .terms=[]) (hai : w.auxiliary .aIndex=[]) (hbi : w.auxiliary .bIndex=[])
    (hreader : w.auxiliary .reader=[]) (htodo : w.auxiliary .readTodo=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) (hc : w.auxiliary .copyScratch=[])
    (hregs : w.registers=fun _=>[]) :
    ∃q≤coefficientBound w a reversed width n,
      Runs program q (ctl .copyTerms) (store w) (ctl .bump) (store (result w (nextWord width a reversed n))) := by
  have h0:=prepare_run w n hn hbuilt hterms hai hbi hc (congrFun hregs (.acc,false)) (congrFun hregs (.acc,true))
  obtain ⟨q1,hq1,h1⟩:=inner_run w a reversed width n SemiprimeRationalBits.zeroWord hr ha hb
    hreader htodo hs hv hc (fun r _ den=>congrFun hregs (r,den))
  let dot:=dotLoop width a.toArray reversed n SemiprimeRationalBits.zeroWord
  have hempty : indexed w 0 0 0 dot=putReg w .acc dot := by
    rw [indexed,counters_empty w hterms hai hbi]
  rw [hempty] at h1
  have hright (den : Bool) : (putReg w .acc dot).registers (.right,den)=[] := by
    rw [putReg_other _ .acc .right dot den (by decide)]
    exact congrFun hregs (.right,den)
  obtain ⟨q2,hq2,h2⟩:=Neg.negate_run (putReg w .acc dot) width hr hc hv hs
    (hright false) (hright true) (putReg_nonempty w .acc dot)
  have hout : Neg.output (putReg w .acc dot) width=nextWord width a reversed n := by
    rw [Neg.output,getReg_put]
    rfl
  have he : Neg.result (putReg w .acc dot) width=result w (nextWord width a reversed n) := by
    unfold Neg.result
    rw [hout]
    rfl
  rw [he] at h2
  have h:=PTrace.join (PTrace.join h0 h1) h2
  refine ⟨15*n+15+q1+q2,?_,h⟩
  unfold coefficientBound
  dsimp only [dot] at hq2
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseCoefficient
