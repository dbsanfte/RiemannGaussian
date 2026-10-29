/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientSetup
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientFrame
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerLoop
/-! # Whole actual coefficient acquisition and exact chronological two-field framing -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficient
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCoefficientBuffers
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
/-- Exact legacy coefficient raw word after every original ordered product/add has executed. -/
def answer (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (n:Nat):SemiprimeRationalBits.RationalWord:=
  SemiprimeD1StackRecoveryAffineConvolution.descend width xs c .unit n SemiprimeRationalBits.zeroWord
/-- Own index-copy, same inner-loop, actual row framing and both cache-drain clocks. -/
def runBound (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (n:Nat) (next:List Bool):Nat:=
  (5*n+6)+SemiprimeD1StackRecoveryAffineInnerLoop.runBound .unit (buffers w (unary n) next) xs c width n SemiprimeRationalBits.zeroWord+
    7*((signed (answer xs c width n)).length+(answer xs c width n).denominator.length)+13
/-- Whole actual coefficient from its physical remaining-index word, restoring every original cache. -/
theorem source_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c:SemiprimeRationalBits.RationalWord) (width next:List Bool)
    (ha:w.added .array=vector xs) (hk:w.added .k=[]) (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hz:∀b,w.registers (.denPower,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width)
    (hs:w.registers (.slope,false)=signed c) (hd:w.registers (.slope,true)=c.denominator):
    ∃q≤runBound w xs c width n next,
      Runs program q (.local .index) (bank (buffers w (unary n) next))
        (.local .coefficientLoop)
        (bank (buffers w (unary n) (SemiprimeD1StackRecoveryGridView.slopeRow (answer xs c width n) next))):=by
  let base:=buffers w (unary n) next
  have h0:=SemiprimeD1StackRecoveryAffineCoefficientSetup.source_run base n rfl hk hc (hz false) (hz true)
  obtain ⟨t,htime,h1⟩:=SemiprimeD1StackRecoveryAffineInnerLoop.source_run .unit base xs n c SemiprimeRationalBits.zeroWord width
    ha hrd ht hx hy hp hc hf hv hr hs hd
  have he:SemiprimeD1StackRecoveryAffineCache.counter base 0=base:=by
    unfold SemiprimeD1StackRecoveryAffineCache.counter
    congr 1
    funext slot
    cases slot <;> simp [base,buffers,unary,hk]
  rw [he] at h1
  have h2:=SemiprimeD1StackRecoveryAffineCoefficientFrame.frame_run w (answer xs c width n) (unary n) next hf
  have h3:=SemiprimeD1StackRecoveryAffineCoefficientFrame.clear_run w (answer xs c width n) (unary n)
    (SemiprimeD1StackRecoveryGridView.slopeRow (answer xs c width n) next) (hz false) (hz true)
  refine ⟨(5*n+6)+t+((6*(answer xs c width n).denominator.length+5)+(6*(signed (answer xs c width n)).length+5)+1)+
      ((signed (answer xs c width n)).length+1+(answer xs c width n).denominator.length+1),?_,
    SemiprimeD1StackRecoveryAffinePrimitives.join
      (SemiprimeD1StackRecoveryAffinePrimitives.join (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2) h3⟩
  dsimp only [base] at htime
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficient
