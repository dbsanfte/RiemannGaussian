/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePairSpec
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadCall
/-! # Actual two array reads, product-first addition and full six-field disposal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInversePair
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverseOperationCall SemiprimeD1StackNormalizedInverseRegisterAlgebra
open SemiprimeD1StackNormalizedInverseRegisterClear SemiprimeD1StackNormalizedInversePairSpec
open SemiprimeD1StackNormalizedInverseReadCall SemiprimeD1StackNormalizedInverseSpec
open SemiprimeD1StackNormalizedInverseCleanup (mass)
open SemiprimeD1StackProcedureTrace
/-- Sum of this pair's actual parser/copy/call/cleanup caps; proof-only cached words are never operands. -/
def pairBound (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (i : ℕ) (width : List Bool) : ℕ :=
  let x:=readWord a (i+1)
  let y:=readWord reversed i
  (helperTime a (i+1)+3)+(helperTime reversed i+3)+
    callBound .product (readPair w x y) width+callBound .sum (multiplied w x y width) width+
    6*(mass (store (added w x y width))+1)
/-- All inputs are the actually retained array, built prefix and physically acquired unary indices. -/
theorem pair_run (w : Words) (a reversed : List SemiprimeRationalBits.RationalWord) (i : ℕ) (width : List Bool)
    (hr : w.rational=emptyRational width)
    (ha : store w (readSource .denominator)=tape a) (hb : store w (readSource .prefix)=tape reversed)
    (hai : store w (readIndex .denominator)=unary (i+1)) (hbi : store w (readIndex .prefix)=unary i)
    (hreader : w.auxiliary .reader=[]) (htodo : w.auxiliary .readTodo=[])
    (hs : w.auxiliary .fieldFrameScratch=[]) (hv : w.auxiliary .valid=[]) (hc : w.auxiliary .copyScratch=[])
    (he : ∀r≠Reg.acc,∀den,w.registers (r,den)=[]) (hacc : w.registers (.acc,false)≠[]) :
    ∃q≤pairBound w a reversed i width,
      Runs program q (ctl .readA) (store w) (ctl .decrementA)
        (store (putReg w .acc (combine width (readWord a (i+1),readWord reversed i) (getReg w .acc)))) := by
  let x:=readWord a (i+1)
  let y:=readWord reversed i
  let left:=putReg w .left x
  let both:=readPair w x y
  let prod:=multiplied w x y width
  let sum:=added w x y width
  have h0:=read_call .denominator (ctl .readA) (ctl .checkedA) (ctl .readB) (ctl (.abort 0))
    rfl rfl w a (i+1) ha hai hreader htodo (he .left (by decide) false) (he .left (by decide) true) hs hv hc
  have hlr : left.registers (.right,false)=[] := by
    rw [show left=putReg w .left x from rfl,putReg_other _ .left .right x false (by decide)]
    exact he .right (by decide) false
  have hld : left.registers (.right,true)=[] := by
    rw [show left=putReg w .left x from rfl,putReg_other _ .left .right x true (by decide)]
    exact he .right (by decide) true
  have h1:=read_call .prefix (ctl .readB) (ctl .checkedB) (ctl (.operate .product)) (ctl (.abort 0))
    rfl rfl left reversed i hb hbi hreader htodo hlr hld hs hv hc
  have hbothL : both.registers (.left,false)≠[] := by
    change (putReg (putReg w .left x) .right y).registers (.left,false)≠[]
    rw [putReg_other _ .right .left y false (by decide)]
    exact putReg_nonempty w .left x
  have hbothR : both.registers (.right,false)≠[] := putReg_nonempty (putReg w .left x) .right y
  obtain ⟨q2,hq2,h2⟩:=operation_call .product (ctl (.operate .product)) (ctl (.operated .product))
    (ctl (.operate .sum)) (ctl (.abort 0)) rfl rfl both width hr hc hv hbothL hbothR
  have hprod : prod.registers (.product,false)≠[] := putReg_nonempty both .product (acquired .product both width)
  have hsuf : prod.registers (.acc,false)≠[] := by
    change (putReg (putReg (putReg w .left x) .right y) .product _).registers (.acc,false)≠[]
    rw [putReg_other _ .product .acc _ false (by decide),putReg_other _ .right .acc y false (by decide),
      putReg_other _ .left .acc x false (by decide)]
    exact hacc
  obtain ⟨q3,hq3,h3⟩:=operation_call .sum (ctl (.operate .sum)) (ctl (.operated .sum))
    (ctl (.clearPair 0)) (ctl (.abort 0)) rfl rfl prod width hr hc hv hprod hsuf
  obtain ⟨q4,hq4,h4⟩:=SemiprimeD1StackNormalizedInverseRegisterClear.pair_run sum
  rw [show sum=added w x y width from rfl,pair_clear_bytes w x y width he] at h4
  have h:=PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4
  refine ⟨_,?_,h⟩
  change helperTime a (i+1)+3+(helperTime reversed i+3)+q2+q3+q4≤
    (helperTime a (i+1)+3)+(helperTime reversed i+3)+callBound .product both width+callBound .sum prod width+
      6*(mass (store sum)+1)
  omega
end RiemannGaussian.SemiprimeD1StackNormalizedInversePair
