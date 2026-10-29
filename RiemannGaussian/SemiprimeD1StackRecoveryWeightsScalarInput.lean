/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
/-! # Four paid actual copies initialize scalar-FIRST total-SECOND final multiplication
Both original Ezero words and the acquired complete sum remain present until
all inputs are copied. No scalar, sum or raw operation answer is an instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarInput
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
namespace H
export SemiprimeD1StackNormalizedInverse (signed)
end H
/-- Actual input copies place scalar in LEFT and the full sum in RIGHT. -/
def filled (w:Words) (scalar total:RationalWord):Words:=replace w (Old.putReg (Old.putReg w.toWords .left scalar) .right total)
/-- Every source bit, restoration loop and actual return of all four copies is included. -/
def timeBound (scalar total:RationalWord):Nat:=
  5*((H.signed scalar).length+scalar.denominator.length+(H.signed total).length+total.denominator.length)+16
/-- Entire final-multiply input acquisition, preserving actual original scalar tapes and the old full accumulator. -/
theorem inputs_run (w:Words) (scalar total:RationalWord)
    (hss:w.scalarInputs .signed=H.signed scalar) (hsd:w.scalarInputs .den=scalar.denominator)
    (hts:w.registers (.acc,false)=H.signed total) (htd:w.registers (.acc,true)=total.denominator)
    (he:∀r≠SemiprimeD1StackNormalizedInverse.Reg.acc,∀den,w.registers (r,den)=[])
    (hc:w.auxiliary .copyScratch=[]):
    Runs program (timeBound scalar total) (.local (.scalar false)) (bank w) (.local .finalProduct) (bank (filled w scalar total)):=by
  let w1:Words:={w with registers:=Function.update w.registers (.left,false) (H.signed scalar)}
  let w2:Words:={w1 with registers:=Function.update w1.registers (.left,true) scalar.denominator}
  let w3:Words:={w2 with registers:=Function.update w2.registers (.right,false) (H.signed total)}
  let w4:Words:={w3 with registers:=Function.update w3.registers (.right,true) total.denominator}
  have h0:=P.copy_call (.scalar false) (.local (.scalar false)) (.local (.scalar true)) rfl
    (bank w) (H.signed scalar) [] hss (he .left (by decide) false) hc
  change Runs program _ _ _ _ (Function.update (bank w) (reg .left false) (H.signed scalar++[])) at h0
  rw [List.append_nil,update_register] at h0
  have hz1:bank w1 (copyTarget (.scalar true))=[]:=by
    change Function.update w.registers (.left,false) (H.signed scalar) (.left,true)=[]
    rw [Function.update_of_ne (by decide)]
    exact he .left (by decide) true
  have h1:=P.copy_call (.scalar true) (.local (.scalar true)) (.local (.total false)) rfl
    (bank w1) scalar.denominator [] hsd hz1 hc
  change Runs program _ _ _ _ (Function.update (bank w1) (reg .left true) (scalar.denominator++[])) at h1
  rw [List.append_nil,update_register] at h1
  have ht0:bank w2 (copySource (.total false))=H.signed total:=by
    change Function.update (Function.update w.registers (.left,false) (H.signed scalar)) (.left,true) scalar.denominator (.acc,false)=_
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
    exact hts
  have hz2:bank w2 (copyTarget (.total false))=[]:=by
    change Function.update (Function.update w.registers (.left,false) (H.signed scalar)) (.left,true) scalar.denominator (.right,false)=[]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
    exact he .right (by decide) false
  have h2:=P.copy_call (.total false) (.local (.total false)) (.local (.total true)) rfl
    (bank w2) (H.signed total) [] ht0 hz2 hc
  change Runs program _ _ _ _ (Function.update (bank w2) (reg .right false) (H.signed total++[])) at h2
  rw [List.append_nil,update_register] at h2
  have ht1:bank w3 (copySource (.total true))=total.denominator:=by
    change Function.update (Function.update (Function.update w.registers (.left,false) (H.signed scalar)) (.left,true) scalar.denominator) (.right,false) (H.signed total) (.acc,true)=_
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
    exact htd
  have hz3:bank w3 (copyTarget (.total true))=[]:=by
    change Function.update (Function.update (Function.update w.registers (.left,false) (H.signed scalar)) (.left,true) scalar.denominator) (.right,false) (H.signed total) (.right,true)=[]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
    exact he .right (by decide) true
  have h3:=P.copy_call (.total true) (.local (.total true)) (.local .finalProduct) rfl
    (bank w3) total.denominator [] ht1 hz3 hc
  change Runs program _ _ _ _ (Function.update (bank w3) (reg .right true) (total.denominator++[])) at h3
  rw [List.append_nil,update_register] at h3
  have heq:w4=filled w scalar total:=rfl
  have hh:=P.join (P.join (P.join h0 h1) h2) h3
  change Runs program _ _ _ _ (bank w4) at hh
  rw [heq] at hh
  convert hh using 1
  unfold timeBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalarInput
