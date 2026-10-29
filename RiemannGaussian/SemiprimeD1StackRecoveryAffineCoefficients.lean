/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficient
/-! # Complete physical q countdown constructs every affine coefficient in original order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficients
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineCoefficientBuffers
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
/-- Only a proof interpretation of the rows physically prepended while i descends. -/
def rows (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool):Nat→List Bool→List Bool
  | 0,next=>next
  | n+1,next=>rows xs c width n
    (SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n) next)
/-- Sum of the SAME actual coefficient source clocks and physical remaining-marker pops. -/
def runBound (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool):Nat→List Bool→Nat
  | 0,_=>1
  | n+1,next=>1+SemiprimeD1StackRecoveryAffineCoefficient.runBound w xs c width n next+
    runBound w xs c width n
      (SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n) next)
/-- No coefficient array or q answer is supplied: actual copied q markers drive every source call and EOF. -/
theorem source_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c:SemiprimeRationalBits.RationalWord) (width next:List Bool)
    (ha:w.added .array=vector xs) (hk:w.added .k=[]) (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hz:∀b,w.registers (.denPower,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width)
    (hs:w.registers (.slope,false)=signed c) (hd:w.registers (.slope,true)=c.denominator):
    ∃q≤runBound w xs c width n next,
      Runs program q (.local .coefficientLoop) (bank (buffers w (unary n) next))
        (.local .clearArray) (bank (buffers w [] (rows xs c width n next))):=by
  induction n generalizing next with
  | zero=>
    have h:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local .coefficientLoop)
      (.local .clearArray) (.local .abort) (.local .index) (aux .remaining)
      (bank (buffers w [] next)) [] rfl rfl
    change Runs program 1 _ _ (.local .clearArray)
      (Function.update (bank (buffers w [] next)) (aux .remaining) []) at h
    rw [update_remaining] at h
    exact ⟨1,le_rfl,h⟩
  | succ n ih=>
    have h0:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local .coefficientLoop)
      (.local .clearArray) (.local .abort) (.local .index) (aux .remaining)
      (bank (buffers w (unary (n+1)) next)) (true::unary n) rfl
      (by simp [bank,buffers,aux,unary,List.replicate_succ])
    change Runs program 1 _ _ (.local .index)
      (Function.update (bank (buffers w (unary (n+1)) next)) (aux .remaining) (unary n)) at h0
    rw [update_remaining] at h0
    obtain ⟨t,htime,h1⟩:=SemiprimeD1StackRecoveryAffineCoefficient.source_run w xs n c width next
      ha hk hrd ht hx hy hp hz hc hf hv hr hs hd
    let emitted:=SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n) next
    obtain ⟨s,hstime,h2⟩:=ih emitted
    refine ⟨1+t+s,?_,SemiprimeD1StackRecoveryAffinePrimitives.join
      (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2⟩
    change 1+t+s≤1+SemiprimeD1StackRecoveryAffineCoefficient.runBound w xs c width n next+
      runBound w xs c width n emitted
    omega
/-- Descending physical framing restores the exact original ascending coefficient order. -/
theorem rows_fold (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (n:Nat) (next:List Bool):
    rows xs c width n next=(List.range n).foldr
      (fun i tail=>SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width i) tail) next:=by
  induction n generalizing next with
  | zero=>rfl
  | succ n ih=>
    rw [rows,ih,List.range_succ,List.foldr_append]
    rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficients
