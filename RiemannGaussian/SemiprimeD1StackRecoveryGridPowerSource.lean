/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridPower
/-! # Actual grid power-source calls from physically acquired a/m marker tapes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSource
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput SemiprimeD1StackRecoveryGridRegisters
open SemiprimeD1StackProcedureTrace
namespace Power
export SemiprimeD1StackRecoveryGridPower (power_run runBound)
export SemiprimeD1StackRecoveryGridPowerLoop (finish)
end Power
/-- Only alpha has one physically pushed extra exponent marker. -/
def exponent (part:PowerSite) (n:Nat) :Nat:=n+if part=.alpha then 1 else 0
/-- Actual acquired power-input bank, without an exponent or answer operand in finite control. -/
def ready (part:PowerSite) (w:Words) (n:Nat) :Words:=
  {w with auxiliary:=Function.update w.auxiliary .powerTodo (List.replicate (exponent part n) true)}
/-- The actual caller continuation of each fixed original-grid power use. -/
def after :PowerSite→Label
  | .center=>.local (.powerCount .alpha) | .alpha=>.local .row
  | .numerator=>.local (.powerCount .denominator) | .denominator=>.local .reciprocal
/-- Actual source copy continuation, followed by the literal alpha marker only at that fixed site. -/
def copyNext (part:PowerSite) :Label:=if part=.alpha then .local .alphaMarker else .local (.powerCall part)
/-- Own clock includes original exponent-marker copy, literal alpha marker, whole actual power and real call/return. -/
def runBound (part:PowerSite) (w:Words) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat) :Nat:=
  (5*n+4)+(if part=.alpha then 1 else 0)+Power.runBound part width x (exponent part n) (ready part w n)+2
/-- Every power count is physically acquired from original a or the actual multiplicity result. -/
theorem prepare_run (part:PowerSite) (w:Words) (n:Nat)
    (hx:bank w (powerCount part)=List.replicate n true)
    (hz:w.auxiliary .powerTodo=[]) (hs:w.auxiliary .copyScratch=[]) :
    Runs program ((5*n+4)+(if part=.alpha then 1 else 0)) (.local (.powerCount part)) (bank w)
      (.local (.powerCall part)) (bank (ready part w n)):=by
  have h0:=PTrace.copy_call (.power part) (.local (.powerCount part)) (copyNext part) rfl
    (bank w) (List.replicate n true) [] hx hz hs
  change Runs program _ _ _ _ (Function.update (bank w) (aux .powerTodo) (List.replicate n true++[])) at h0
  rw [List.append_nil,update_auxiliary] at h0
  by_cases ha:part=.alpha
  · subst part
    let copied:Words:={w with auxiliary:=Function.update w.auxiliary .powerTodo (List.replicate n true)}
    have h1:=PTrace.push_run (.local .alphaMarker) (.local (.powerCall .alpha)) (aux .powerTodo) true (bank copied) rfl
    change Runs program 1 _ _ _ (Function.update (bank copied) (aux .powerTodo) (true::List.replicate n true)) at h1
    rw [update_auxiliary] at h1
    dsimp only [copied] at h1
    rw [Function.update_idem,←List.replicate_succ] at h1
    have h:=PTrace.join h0 h1
    simpa only [copyNext,ready,exponent,ite_true,List.length_replicate] using h
  · have h:exponent part n=n:=by simp only [exponent,ha,ite_false,Nat.add_zero]
    simpa only [copyNext,ha,ite_false,Nat.add_zero,List.length_replicate,ready,h] using h0
/-- All helper count bytes are genuinely consumed; the actual originally empty count word is restored. -/
theorem finish_ready (part:PowerSite) (w:Words) (n:Nat) (out:SemiprimeRationalBits.RationalWord)
    (hz:w.auxiliary .powerTodo=[]) :Power.finish (ready part w n) part out=putReg w (powerDestination part) out:=by
  dsimp only [Power.finish,SemiprimeD1StackRecoveryGridPowerLoop.finish,ready,putReg]
  rw [Function.update_idem]
  congr 1
  exact Function.update_eq_self_iff.mpr hz.symm
/-- Whole actual power use, including count acquisition, literal n0 one, every real R36 operation and actual caller returns. -/
theorem power_source_run (part:PowerSite) (w:Words) (width:List Bool) (x:SemiprimeRationalBits.RationalWord) (n:Nat)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hz:w.auxiliary .powerTodo=[]) (hc:bank w (powerCount part)=List.replicate n true)
    (hx:w.registers (powerBase part,false)=signed x) (hd:w.registers (powerBase part,true)=x.denominator) :
    ∃q≤runBound part w width x n,Runs program q (.local (.powerCount part)) (bank w) (after part)
      (bank (putReg w (powerDestination part) (SemiprimeD1RecoveryPowerBits.power width x (exponent part n)).word)):=by
  have h0:=prepare_run part w n hc hz hs
  obtain ⟨q,hq,h1⟩:=Power.power_run part width x (exponent part n) (ready part w n) hr hs
    rfl hx hd
  rw [finish_ready part w n _ hz] at h1
  have hcode:program (.local (.powerCall part))=.call (.power part .clearSigned) (after part):=by cases part <;> rfl
  have h2:=PTrace.local_call (.local (.powerCall part)) (.power part .clearSigned) (.power part .done) (after part)
    hcode rfl q (bank (ready part w n)) _ h1
  refine ⟨((5*n+4)+(if part=.alpha then 1 else 0))+(q+2),?_,PTrace.join h0 h2⟩
  unfold runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridPowerSource
