/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperation
/-! # Real arithmetic helper calls with acquired cache operands and exact caller pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseOperation
open SemiprimeD1StackNormalizedInverseOperationOutput SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackProcedureTrace
/-- Exact native operation used to specify bytes acquired by the literal fixed site. -/
def acquired (site : Site) (w : Words) (width : List Bool) : SemiprimeRationalBits.RationalWord :=
  (SemiprimeRationalBits.executeOperation (SemiprimeD1StackRationalOperation.operation (operation site))
    (getReg w (operand site false)) (getReg w (operand site true)) width).word
/-- Exact proof-side cache update; no executable instruction evaluates this function. -/
def after (site : Site) (w : Words) (width : List Bool) : Words := putReg w (destination site) (acquired site w width)
/-- Actual full helper cap, including literal caller/return and the actual TRUE pop. -/
def callBound (site : Site) (w : Words) (width : List Bool) : ℕ :=
  let x:=getReg w (operand site false)
  let y:=getReg w (operand site true)
  timeBound site w x.numerator.negative x.numerator.magnitude x.denominator
    y.numerator.negative y.numerator.magnitude y.denominator width+3
/-- Every actual normalization, two fits, sign pop/push,35 drains and caller return are paid. -/
theorem operation_call (site : Site) (pc checked finish failure : Label)
    (hcall : program pc=.call (.operation site (.copyInput false false)) checked)
    (hpop : program checked=.base (.pop (aux .valid) failure failure finish))
    (w : Words) (width : List Bool) (hr : w.rational=emptyRational width)
    (hs : w.auxiliary .copyScratch=[]) (hv : w.auxiliary .valid=[])
    (hx : w.registers (operand site false,false)≠[]) (hy : w.registers (operand site true,false)≠[]) :
    ∃q≤callBound site w width,Runs program q pc (store w) finish (store (after site w width)) := by
  let x:=getReg w (operand site false)
  let y:=getReg w (operand site true)
  have hls:=signed_getReg w (operand site false) hx
  have hrs:=signed_getReg w (operand site true) hy
  obtain ⟨q,hq,hh⟩:=operation_run site w x.numerator.negative x.numerator.magnitude x.denominator
    y.numerator.negative y.numerator.magnitude y.denominator width hr hs hv hls rfl hrs rfl
  let result:=putReg w (destination site)
    (word (operation site) x.numerator.negative x.numerator.magnitude x.denominator
      y.numerator.negative y.numerator.magnitude y.denominator width)
  have h0:=PTrace.local_call pc (.operation site (.copyInput false false)) (.operation site .return)
    checked hcall rfl q (store w) (store (success result)) hh
  have h1:=PTrace.pop_run checked failure failure finish (aux .valid) (store (success result)) [true]
    hpop (by change Function.update w.auxiliary .valid [true] .valid=[true];exact Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update (store (success result)) (aux .valid) []=store result := by
    rw [update_aux]
    change store {result with auxiliary:=Function.update (Function.update result.auxiliary .valid [true]) .valid []}=store result
    rw [Function.update_idem,←hv]
    change store {result with auxiliary:=Function.update result.auxiliary .valid (result.auxiliary .valid)}=store result
    rw [Function.update_eq_self]
  rw [he] at h1
  have h:=PTrace.join h0 h1
  have hw:result=after site w width := by
    dsimp only [result,after,acquired]
    rw [word_legacy]
  rw [hw] at h
  refine ⟨q+2+1,?_,h⟩
  change q+2+1≤timeBound site w x.numerator.negative x.numerator.magnitude x.denominator
    y.numerator.negative y.numerator.magnitude y.denominator width+3
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationCall
