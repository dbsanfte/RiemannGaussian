/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayRead
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePairMeaning
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCache
/-! # One complete actual coefficient-read/factor/product/sum/cleanup iteration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerStep
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineRegisters SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
/-- The actual loader writes suffix, reached coefficient, then finite-class factor into distinct physical roles. -/
def acquired (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord):Words:=
  putReg (putReg (putReg w .denPower suffix) .numBase x) .denBase y
/-- All actual loader writes commute only because their physical role pairs are disjoint. -/
theorem acquired_eq (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord):
    acquired w x y suffix=SemiprimeD1StackRecoveryAffinePairMeaning.loaded w x y suffix:=by
  unfold acquired SemiprimeD1StackRecoveryAffinePairMeaning.loaded
  rw [SemiprimeD1StackRecoveryAffineCache.putReg_comm w .denPower .numBase suffix x (by decide),
    SemiprimeD1StackRecoveryAffineCache.putReg_comm (putReg w .numBase x) .denPower .denBase suffix y (by decide)]
/-- Own clocks of both real source acquisitions and the complete actual scalar pair. -/
def runBound (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c suffix:SemiprimeRationalBits.RationalWord) (width:List Bool):Nat:=
  SemiprimeD1StackRecoveryAffineArrayRead.runBound xs n+
    SemiprimeD1StackRecoveryAffineFactor.runBound part c+
    SemiprimeD1StackRecoveryAffinePair.runBound
      (acquired w (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs n) (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix) width
/-- Whole actual iteration executes all zero terms and restores every transient field before its real k pop. -/
theorem source_run (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c suffix:SemiprimeRationalBits.RationalWord) (width:List Bool)
    (ha:w.added .array=vector xs) (hk:w.added .k=unary n)
    (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width)
    (hs:w.registers (.slope,false)=signed c) (hd:w.registers (.slope,true)=c.denominator):
    ∃q≤runBound part w xs n c suffix width,Runs program q (.local (.inner part)) (bank (putReg w .denPower suffix))
      (.local (.innerNext part))
      (bank (putReg w .denPower (SemiprimeD1StackRecoveryAffinePairMeaning.step width
        (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs n) (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix))):=by
  let x:=SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs n
  let y:=SemiprimeD1StackRecoveryAffineFactor.value part c
  let base:=putReg w .denPower suffix
  let first:=putReg base .numBase x
  let second:=putReg first .denBase y
  have hbase:∀b,base.registers (.numBase,b)=[]:=by
    intro b
    rw [putReg_other w .denPower .numBase suffix b (by decide)]
    exact hx b
  have h0:=SemiprimeD1StackRecoveryAffineArrayRead.source_run part base xs n ha hk hrd ht (hbase false) (hbase true) hc hf hv
  have hden:∀b,first.registers (.denBase,b)=[]:=by
    intro b
    rw [putReg_other base .numBase .denBase x b (by decide),putReg_other w .denPower .denBase suffix b (by decide)]
    exact hy b
  have hs':first.registers (.slope,false)=signed c:=by
    rw [putReg_other base .numBase .slope x false (by decide),putReg_other w .denPower .slope suffix false (by decide)]
    exact hs
  have hd':first.registers (.slope,true)=c.denominator:=by
    rw [putReg_other base .numBase .slope x true (by decide),putReg_other w .denPower .slope suffix true (by decide)]
    exact hd
  have h1:=SemiprimeD1StackRecoveryAffineFactor.factor_run part first c (hden false) (hden true) hc hs' hd'
  have hxn:second.registers (.numBase,false)≠[]:=by
    rw [putReg_other first .denBase .numBase y false (by decide),(putReg_fields base .numBase x).1]
    exact List.cons_ne_nil _ _
  have hyn:second.registers (.denBase,false)≠[]:=by
    rw [(putReg_fields first .denBase y).1]
    exact List.cons_ne_nil _ _
  have han:second.registers (.denPower,false)≠[]:=by
    rw [putReg_other first .denBase .denPower y false (by decide),putReg_other base .numBase .denPower x false (by decide),
      (putReg_fields w .denPower suffix).1]
    exact List.cons_ne_nil _ _
  obtain ⟨q,hq,h2⟩:=SemiprimeD1StackRecoveryAffinePair.source_run part second width hr hc hxn hyn han
  have he:second=SemiprimeD1StackRecoveryAffinePairMeaning.loaded w x y suffix:=acquired_eq w x y suffix
  rw [he,SemiprimeD1StackRecoveryAffinePairMeaning.result_exact w x y suffix width hx hy hp] at h2
  rw [←he] at h2
  refine ⟨SemiprimeD1StackRecoveryAffineArrayRead.runBound xs n+SemiprimeD1StackRecoveryAffineFactor.runBound part c+q,
    ?_,SemiprimeD1StackRecoveryAffinePrimitives.join (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2⟩
  exact Nat.add_le_add_left hq _
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerStep
