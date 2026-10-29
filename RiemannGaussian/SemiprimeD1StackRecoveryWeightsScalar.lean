/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarInput
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsFrame
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCleanup
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterAlgebra
/-! # Complete actual Ezero-FIRST total-SECOND final multiplication and row acquisition
No result or operation stream is an operand. The acquired full sum is copied,
the realR36 call executes, its exact product is framed, and all8 caches drain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalar
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsScalarInput
open SemiprimeD1StackRecoveryWeightsFrame SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Exact mathematical byte specification of the actual final normalized/twice-fitted product. -/
def output (scalar total:RationalWord) (width:List Bool):RationalWord:=
  (SemiprimeRationalBits.executeOperation .mul scalar total width).word
/-- Actual bank after all real inputs/arithmetic/framing and before all8 cache drains. -/
def beforeClear (w:Words) (scalar total:RationalWord) (width:List Bool):Words:=
  framed (afterOperation .product (filled w scalar total) width) (output scalar total width)
/-- Final full caller bank retains all six sources and extends only the chronological output. -/
def result (w:Words) (scalar total:RationalWord) (width:List Bool):Words:=
  {w with registers:=fun _=>[],auxiliary:=Function.update w.auxiliary .output (SemiprimeD1StackNormalizedInverse.row (output scalar total width) (w.auxiliary .output))}
/-- Every real input copy/call/frame/drain is part of this SAME-source budget. -/
def timeBound (w:Words) (scalar total:RationalWord) (width:List Bool):Nat:=
  SemiprimeD1StackRecoveryWeightsScalarInput.timeBound scalar total+
    SemiprimeD1StackNormalizedInverseOperationCall.callBound .product (filled w scalar total).toWords width+
    (6*((SemiprimeD1StackNormalizedInverse.signed (output scalar total width)).length+(output scalar total width).denominator.length)+11)+
    8*(SemiprimeD1StackNormalizedInverseCleanup.mass (Old.store (beforeClear w scalar total width).toWords)+1)
/-- Exact native operand order, independent of Valid/Fits and all raw input padding. -/
theorem acquired_eq (w:Words) (scalar total:RationalWord) (width:List Bool):
    SemiprimeD1StackNormalizedInverseOperationCall.acquired .product (filled w scalar total).toWords width=output scalar total width:=by
  change (SemiprimeRationalBits.executeOperation .mul
    (Old.getReg (Old.putReg (Old.putReg w.toWords .left scalar) .right total) .left)
    (Old.getReg (Old.putReg (Old.putReg w.toWords .left scalar) .right total) .right) width).word=_
  rw [SemiprimeD1StackNormalizedInverseRegisterAlgebra.getReg_other _ .right .left total (by decide),
    SemiprimeD1StackNormalizedInverseView.getReg_put,SemiprimeD1StackNormalizedInverseView.getReg_put]
  rfl
/-- Complete final scalar/row acquisition reaches the next outer counter only after ALL8 cache fields drain. -/
theorem scalar_run (w:Words) (scalar total:RationalWord) (width:List Bool)
    (hss:w.scalarInputs .signed=SemiprimeD1StackNormalizedInverse.signed scalar) (hsd:w.scalarInputs .den=scalar.denominator)
    (hts:w.registers (.acc,false)=SemiprimeD1StackNormalizedInverse.signed total) (htd:w.registers (.acc,true)=total.denominator)
    (he:∀r≠SemiprimeD1StackNormalizedInverse.Reg.acc,∀den,w.registers (r,den)=[])
    (hr:w.rational=Old.emptyRational width) (hc:w.auxiliary .copyScratch=[])
    (hv:w.auxiliary .valid=[]) (hs:w.auxiliary .fieldFrameScratch=[]):
    ∃time ≤ timeBound w scalar total width,Runs program time (.local (.scalar false)) (bank w) (.local .outer)
      (bank (result w scalar total width)):=by
  let ready:=filled w scalar total
  let stopped:=afterOperation .product ready width
  have h0:=inputs_run w scalar total hss hsd hts htd he hc
  have hx:ready.registers (.left,false)≠[]:=by
    change (Old.putReg (Old.putReg w.toWords .left scalar) .right total).registers (.left,false)≠[]
    rw [SemiprimeD1StackNormalizedInverseView.putReg_other _ .right .left total false (by decide)]
    exact SemiprimeD1StackNormalizedInverseRegisterAlgebra.putReg_nonempty _ .left scalar
  have hy:ready.registers (.right,false)≠[]:=SemiprimeD1StackNormalizedInverseRegisterAlgebra.putReg_nonempty _ .right total
  obtain ⟨m,hm,h1⟩:=operation_call .product (.local .finalProduct) (.local .checkedFinalProduct) (.local (.frame true)) rfl rfl ready width hr hc hv hx hy
  have hword:=acquired_eq w scalar total width
  have hnum:stopped.registers (.product,false)=SemiprimeD1StackNormalizedInverse.signed (output scalar total width):=by
    change (Old.putReg ready.toWords .product (SemiprimeD1StackNormalizedInverseOperationCall.acquired .product ready.toWords width)).registers (.product,false)=_
    rw [(SemiprimeD1StackNormalizedInverseView.putReg_fields ready.toWords .product _).1,hword]
  have hden:stopped.registers (.product,true)=(output scalar total width).denominator:=by
    change (Old.putReg ready.toWords .product (SemiprimeD1StackNormalizedInverseOperationCall.acquired .product ready.toWords width)).registers (.product,true)=_
    rw [(SemiprimeD1StackNormalizedInverseView.putReg_fields ready.toWords .product _).2,hword]
  have h2:=frame_run stopped (output scalar total width) hnum hden hs
  obtain ⟨z,hz,h3⟩:=SemiprimeD1StackRecoveryWeightsCleanup.registers_run (beforeClear w scalar total width)
  have hend:({beforeClear w scalar total width with registers:=fun _=>[]}:Words)=result w scalar total width:=rfl
  rw [hend] at h3
  have hh:=P.join (P.join (P.join h0 h1) h2) h3
  refine ⟨SemiprimeD1StackRecoveryWeightsScalarInput.timeBound scalar total+m+
    (6*((SemiprimeD1StackNormalizedInverse.signed (output scalar total width)).length+(output scalar total width).denominator.length)+11)+z,?_,hh⟩
  dsimp only [timeBound]
  dsimp only [ready] at hm
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalar
