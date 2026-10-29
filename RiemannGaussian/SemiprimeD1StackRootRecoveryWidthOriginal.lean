/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthStorage
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthMonomial
/-! # Whole binary-N-only exact recovery-template acquisition
No metadata, grid size or template is supplied at entry. Real original-input
acquisition, two copies and actual width generation all belong to this source.
Canonical rational weights and the recursive factorer remain separate work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootRecoveryWidthOriginal
open SemiprimeD1StackRootRecoveryWidth SemiprimeD1StackRootRecoveryWidthEncoding
open SemiprimeD1StackRootRecoveryWidthExecution SemiprimeD1StackRootRecoveryWidthBounds
open SemiprimeD1StackRootRecoveryWidthMonomial
open SemiprimeBitArithmetic (bitValue)
/-- One real original-input run computes exactly the authoritative false template. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits):
    ∃q ≤ runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=List.replicate
        (SemiprimeD1RecoveryNodeBits.width (O.originalA bits) (O.originalM bits)) false:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded bits hc hN
  exact ⟨q,hq,hr,output_original bits hN⟩
/-- SAME literal binary-input program has fixed family-wide coefficients and the retained original scope rate. -/
theorem uniform_original:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits),
    ∃q ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=List.replicate
        (SemiprimeD1RecoveryNodeBits.width (O.originalA bits) (O.originalM bits)) false:=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr,ho⟩:=source_original bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  have hb:runBound bits ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
    simpa only [Arity.arityCapacity,hw] using hbound bits
  exact ⟨q,hq.trans hb,hr,ho⟩
/-- A fixed original-input scope envelope pays ALL2211 actual words and genuine return cells. -/
theorem cells_cap_monomial:∃coef degree:Nat,∀bits:List Bool,
    2212*(bits.length+runBound bits) ≤ coef*(bits.length+1)^degree*2^(28500*Arity.arityCapacity bits):=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨2212*(coef+1),degree+1,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+1)
  let E:Nat:=2^(28500*Arity.arityCapacity bits)
  have hpos:1 ≤ bits.length+1:=by omega
  have he:1 ≤ E:=Nat.pow_pos (by decide)
  have hd:(bits.length+1)^degree ≤ H:=Nat.pow_le_pow_right hpos (by omega)
  have hb0:bits.length+1 ≤ H:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by omega:1 ≤ degree+1)
  have hpay:bits.length ≤ bits.length*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left bits.length he
  have hb:bits.length ≤ H*E:=hpay.trans (Nat.mul_le_mul_right E (by omega))
  have ht:runBound bits ≤ coef*H*E:=
    (hbound bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  change 2212*(bits.length+runBound bits) ≤ (2212*(coef+1))*H*E
  nlinarith only [hb,ht]
/-- Every genuine original-input compiled prefix has the same fixed whole-family scope cap. -/
theorem uniform_prefix_cells:∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits) (fuel:Nat) (cfg:machine.Cfg),
    (fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg→
      (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
          2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
  obtain ⟨coef,degree,hbound⟩:=cells_cap_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=(SemiprimeD1StackRootRecoveryWidthStorage.machine_prefix_cells bits hc hN fuel cfg hr).trans (hbound bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [Arity.arityCapacity,hw] using h
end RiemannGaussian.SemiprimeD1StackRootRecoveryWidthOriginal
