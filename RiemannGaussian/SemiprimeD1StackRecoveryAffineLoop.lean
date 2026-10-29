/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopView
/-! # Whole actual affine source over every physically acquired reversed original slope -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoop
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineLoopView
open SemiprimeD1StackRecoveryAffineReadCount (unary)
open SemiprimeD1StackRecoveryAffineOperationInput (emptyRational)
open SemiprimeRationalBits (RationalWord)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run peek_run)
end T
/-- Exact proof interpretation of the same physical reverse-row traversal and full convolution stages. -/
def fold (width:List Bool) (q:Nat):List RationalWord→List RationalWord→List RationalWord
  | [],xs=>xs
  | c::cs,xs=>fold width q cs (multiply width xs c q)
/-- SAME actual reversed-row parse, full actual coefficient stage and following physical-row source budgets. -/
def runBound (w:Words) (width:List Bool) (q:Nat):List RationalWord→List RationalWord→Nat
  | [],_=>2
  | c::cs,xs=>(1+(8*(signed c).length+8+(8*c.denominator.length+8)))+
    SemiprimeD1StackRecoveryAffineSlopeStage.runBound (putReg (state w xs cs) .slope c) xs c width q+
    runBound w width q cs (multiply width xs c q)
/-- Entire source loop restores every original104 word, with all arrays/slopes acquired from physical tapes. -/
theorem source_run (w:Words) (xs slopes:List RationalWord) (q:Nat) (width:List Bool)
    (hq:w.added .retainedQ=unary q) (hk:w.added .k=[]) (hrd:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hm:w.added .remaining=[]) (hn:w.added .nextArray=[])
    (hx:∀b,w.registers (.numBase,b)=[]) (hy:∀b,w.registers (.denBase,b)=[]) (hp:∀b,w.registers (.numPower,b)=[])
    (hz:∀b,w.registers (.denPower,b)=[]) (hsl:∀b,w.registers (.slope,b)=[])
    (hc:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[])
    (hr:w.rational=emptyRational width):
    ∃t≤runBound w width q slopes xs,Runs program t (.local .slopeLoop) (bank (state w xs slopes))
      (.local .done) (bank (finished w (fold width q slopes xs))):=by
  induction slopes generalizing xs with
  | nil=>
    have h0:=T.pop_run (.local .slopeLoop) (.local .abort) (.local .slopeEOF)
      (.local (.field (.slope true false))) (aux .reverseSlopes) (bank (state w xs [])) [false] rfl rfl
    change Runs program 1 _ _ (.local .slopeEOF)
      (Function.update (bank (SemiprimeD1StackRecoveryAffineSlopeRead.tape (array w xs) (vector []))) (aux .reverseSlopes) []) at h0
    rw [SemiprimeD1StackRecoveryAffineSlopeRead.update_tape] at h0
    have h1:=T.peek_run (.local .slopeEOF) (.local .done) (.local .abort) (.local .abort)
      (aux .reverseSlopes) (bank (finished w xs)) [] rfl rfl
    exact ⟨2,le_rfl,T.join h0 h1⟩
  | cons c cs ih=>
    have h0:=SemiprimeD1StackRecoveryAffineSlopeRead.source_run (array w xs) c (vector cs)
      (hsl false) (hsl true) hf hv
    have hother (r:SemiprimeD1StackRecoveryGrid.Reg) (b:Bool) (he:r≠.slope):
        (putReg (state w xs cs) .slope c).registers (r,b)=w.registers (r,b):=
      SemiprimeD1StackRecoveryAffineRegisters.putReg_other (state w xs cs) .slope r c b he
    obtain ⟨t,htime,h1⟩:=SemiprimeD1StackRecoveryAffineSlopeStage.source_run
      (putReg (state w xs cs) .slope c) xs q c width rfl hq hk hrd ht hm hn
      (fun b=>(hother .numBase b (by decide)).trans (hx b))
      (fun b=>(hother .denBase b (by decide)).trans (hy b))
      (fun b=>(hother .numPower b (by decide)).trans (hp b))
      (fun b=>(hother .denPower b (by decide)).trans (hz b)) hc hf hv hr
      (putReg_fields (state w xs cs) .slope c).1 (putReg_fields (state w xs cs) .slope c).2
    rw [stage_result w xs cs c width q (hsl false) (hsl true) hm hn] at h1
    obtain ⟨s,hstime,h2⟩:=ih (multiply width xs c q)
    refine ⟨(1+(8*(signed c).length+8+(8*c.denominator.length+8)))+t+s,?_,T.join (T.join h0 h1) h2⟩
    change (1+(8*(signed c).length+8+(8*c.denominator.length+8)))+t+s≤
      (1+(8*(signed c).length+8+(8*c.denominator.length+8)))+
      SemiprimeD1StackRecoveryAffineSlopeStage.runBound (putReg (state w xs cs) .slope c) xs c width q+
      runBound w width q cs (multiply width xs c q)
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoop
