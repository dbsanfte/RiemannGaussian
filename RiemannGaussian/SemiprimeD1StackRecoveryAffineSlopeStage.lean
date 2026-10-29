/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayMove
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeDrain
/-! # Whole physical affine-array stage for one actually parsed original slope -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeStage
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCoefficientBuffers
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join push_run copy_call)
end T
/-- All actual original coefficient rows, with their paid physical vector terminator. -/
def bytes (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (q:Nat):List Bool:=
  SemiprimeD1StackRecoveryAffineCoefficients.rows xs c width q [false]
/-- Exact bank after real array replacement and actual current-slope drains. -/
def result (w:Words) (output:List Bool):Words:=
  SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg
    (SemiprimeD1StackRecoveryAffineArrayMove.result (buffers w [] output) output) .slope
/-- SAME stage's literal seed/copy, full coefficient loop, physical old-array I/O and slope drains. -/
def runBound (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (q:Nat):Nat:=
  1+(5*q+4)+SemiprimeD1StackRecoveryAffineCoefficients.runBound w xs c width q [false]+
    SemiprimeD1StackRecoveryAffineArrayMove.runBound (vector xs) (bytes xs c width q)+
      ((signed c).length+1+c.denominator.length+1)
/-- Every coefficient and zero extension is actually acquired/evaluated, including q0/W0; no array is supplied. -/
theorem source_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (q:Nat)
    (c:SemiprimeRationalBits.RationalWord) (width:List Bool)
    (ha:w.added .array=vector xs) (hq:w.added .retainedQ=unary q)
    (hk:w.added .k=[]) (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hm:w.added .remaining=[]) (hn:w.added .nextArray=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hz:∀b,w.registers (.denPower,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width)
    (hs:w.registers (.slope,false)=signed c) (hd:w.registers (.slope,true)=c.denominator):
    ∃t≤runBound w xs c width q,Runs program t (.local .seedNext) (bank w)
      (.local .slopeLoop) (bank (result w (bytes xs c width q))):=by
  have hself:buffers w [] []=w:=by simpa only [hm,hn] using buffers_self w
  have h0:=T.push_run (.local .seedNext) (.local .count) (aux .nextArray) false (bank (buffers w [] [])) rfl
  change Runs program 1 _ _ _ (Function.update (bank (buffers w [] [])) (aux .nextArray) [false]) at h0
  rw [update_next,hself] at h0
  have h1:=T.copy_call .count (.local .count) (.local .coefficientLoop) rfl
    (bank (buffers w [] [false])) (unary q) [] hq rfl hc
  change Runs program _ _ _ _ (Function.update (bank (buffers w [] [false])) (aux .remaining) (unary q++[])) at h1
  rw [List.append_nil,update_remaining] at h1
  obtain ⟨t,htime,h2⟩:=SemiprimeD1StackRecoveryAffineCoefficients.source_run w xs q c width [false]
    ha hk hrd ht hx hy hp hz hc hf hv hr hs hd
  let output:=bytes xs c width q
  let middle:=buffers w [] output
  have h3:=SemiprimeD1StackRecoveryAffineArrayMove.source_run middle (vector xs) output ha rfl hc
  have h4:=SemiprimeD1StackRecoveryAffineSlopeDrain.source_run
    (SemiprimeD1StackRecoveryAffineArrayMove.result middle output)
  change Runs program ((w.registers (.slope,false)).length+1+(w.registers (.slope,true)).length+1) _ _ _ _ at h4
  rw [hs,hd] at h4
  refine ⟨1+(5*(unary q).length+4)+t+
      SemiprimeD1StackRecoveryAffineArrayMove.runBound (vector xs) output+((signed c).length+1+c.denominator.length+1),?_,
    T.join (T.join (T.join (T.join h0 h1) h2) h3) h4⟩
  dsimp only [output]
  unfold runBound
  simp only [unary,List.length_replicate]
  omega
/-- The complete actual stage's output is the exact authoritative native multiply array tape. -/
theorem bytes_original (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (q:Nat):
    bytes xs c width q=vector (SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] q).words.toList:=
  SemiprimeD1StackRecoveryAffineCoefficientsOriginal.rows_original xs c width q
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeStage
