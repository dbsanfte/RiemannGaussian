/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingStorage
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingMonomial
/-! # Complete original-binary-input frequency and packet-padding acquisition
The actual whole source acquires every upstream selected key/dimension, executes
its own real frequency/rounding source and returns the exact original padding.
Full packet inventory/recursive children/coefficients/counter and factor search
remain separate obligations; no old native report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingOriginal
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingEncoding
open SemiprimeD1StackRootPacketPaddingBounds SemiprimeD1StackRootPacketPaddingInputBounds
open SemiprimeD1StackRootPacketPaddingMonomial
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire SemiprimeD1PacketPadding.acquire
/-- Original packet-padding bytes are a proof-side specification, never an input to the fixed program. -/
def originalPadding (bits:List Bool) (hN:0 < bitValue bits) :List Bool :=
  (SemiprimeD1PacketPadding.acquire (A.net bits hN).leftCount (A.net bits hN).rows.length 64 (A.dimension bits)
    (SemiprimeD1TensorNetwork.arity (A.net bits hN).rows) (SemiprimeD1TensorNetwork.owner (A.net bits hN).rows)).padding
/-- Whole actual original-input run and the exact old compact binary padding hold together. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃q ≤runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=originalPadding bits hN :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded bits hc hN
  exact ⟨q,hq,hr,SemiprimeD1StackRootPacketPaddingExecution.output_original bits hN⟩
/-- Fixed coefficient and degree precede every canonical original N for the SAME literal source. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits),
    ∃q ≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
        (done bits hN).data output=originalPadding bits hN :=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr,ho⟩:=source_original bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  have hb:runBound bits ≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
    simpa only [Arity.arityCapacity,hw] using hbound bits
  exact ⟨q,hq.trans hb,hr,ho⟩
/-- Every2139-tape/real-return cap has fixed polynomial witnesses and the same scope exponential. -/
theorem cells_cap_monomial :∃coef degree:Nat,∀bits:List Bool,
    2140*(bits.length+runBound bits) ≤coef*(bits.length+1)^degree*2^(28500*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨2140*(coef+1),degree+1,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+1)
  let E:Nat:=2^(28500*Arity.arityCapacity bits)
  have hpos:1 ≤bits.length+1:=by omega
  have he:1 ≤E:=Nat.pow_pos (by decide)
  have hd:(bits.length+1)^degree ≤H:=Nat.pow_le_pow_right hpos (by omega)
  have hb0:bits.length+1 ≤H:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (by omega:1 ≤degree+1)
  have hpay:bits.length ≤bits.length*E:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left bits.length he
  have hb:bits.length ≤H*E:=hpay.trans (Nat.mul_le_mul_right E (by omega))
  have ht:runBound bits ≤coef*H*E:=
    (hbound bits).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left coef hd))
  change 2140*(bits.length+runBound bits) ≤(2140*(coef+1))*H*E
  nlinarith only [hb,ht]
/-- All actual genuine compiled prefixes are charged from Turing.initList of binary N alone. -/
theorem uniform_prefix_cells :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits) (fuel:Nat) (cfg:machine.Cfg),
    (fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg →
      (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
          2^(28500*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))) :=by
  obtain ⟨coef,degree,hbound⟩:=cells_cap_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=(SemiprimeD1StackRootPacketPaddingStorage.machine_prefix_cells bits hc hN fuel cfg hr).trans (hbound bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [Arity.arityCapacity,hw] using h
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingOriginal
