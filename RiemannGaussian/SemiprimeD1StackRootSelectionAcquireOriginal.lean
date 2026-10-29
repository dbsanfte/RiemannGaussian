/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireStorage
import RiemannGaussian.SemiprimeD1StackRootSelectionAcquireMonomial
/-! # Whole original-binary-input selected-key acquisition at a fixed scope rate
One literal program acquires its original rows, counts, dimension, alphabet,
selection cache and complete selected-key vector. This is an acquisition
theorem; recursive child/coefficient acquisition and factoring remain upstream
and downstream obligations of the full counter/public search.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootSelectionAcquireOriginal
open SemiprimeD1StackRootSelectionAcquire SemiprimeD1StackRootSelectionAcquireEncoding
open SemiprimeD1StackRootSelectionAcquireBounds SemiprimeD1StackRootSelectionAcquireInputBounds
open SemiprimeD1StackRootSelectionAcquireMonomial
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- Original selected-key bytes are a proof-side specification, never an input to the fixed program. -/
def originalKeys (bits:List Bool) (hN:0 < bitValue bits) :List Bool :=
  SemiprimeD1TensorTapeCodec.vectorBits
    (SemiprimeD1IncidenceAcquisition.acquire (net bits hN).leftCount (net bits hN).rows.length 64 (dimension bits)
      (SemiprimeD1TensorNetwork.arity (net bits hN).rows) (SemiprimeD1TensorNetwork.owner (net bits hN).rows)).keys
/-- Whole actual original-input run and the exact entire old key vector hold together. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    ∃q ≤runBound bits,SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
      (done bits hN).data output=originalKeys bits hN :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded bits hc hN
  exact ⟨q,hq,hr,SemiprimeD1StackRootSelectionAcquireExecution.output_original bits hN⟩
/-- Fixed coefficient and degree precede every canonical original N for the SAME literal source. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits),
    ∃q ≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(5700*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN) ∧
        (done bits hN).data output=originalKeys bits hN :=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr,ho⟩:=source_original bits hc hN
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  have hb:runBound bits ≤coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(5700*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))):=by
    simpa only [Arity.arityCapacity,hw] using hbound bits
  exact ⟨q,hq.trans hb,hr,ho⟩
/-- Every2114-tape/real-return cap has fixed polynomial witnesses and the same scope exponential. -/
theorem cells_cap_monomial :∃coef degree:Nat,∀bits:List Bool,
    2115*(bits.length+runBound bits) ≤coef*(bits.length+1)^degree*2^(5700*Arity.arityCapacity bits) :=by
  obtain ⟨coef,degree,hbound⟩:=runBound_monomial
  refine ⟨2115*(coef+1),degree+1,?_⟩
  intro bits
  let H:Nat:=(bits.length+1)^(degree+1)
  let E:Nat:=2^(5700*Arity.arityCapacity bits)
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
  change 2115*(bits.length+runBound bits) ≤(2115*(coef+1))*H*E
  nlinarith only [hb,ht]
/-- All actual genuine compiled prefixes are charged from Turing.initList of binary N alone. -/
theorem uniform_prefix_cells :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (_hN:0 < bitValue bits) (fuel:Nat) (cfg:machine.Cfg),
    (fun c=>c.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg →
      (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
        coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
          2^(5700*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))) :=by
  obtain ⟨coef,degree,hbound⟩:=cells_cap_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN fuel cfg hr
  have h:=(SemiprimeD1StackRootSelectionAcquireStorage.machine_prefix_cells bits hc hN fuel cfg hr).trans (hbound bits)
  have hw:=SemiprimeD1StackRootScheduleOriginal.width_original bits hc
  simpa only [Arity.arityCapacity,hw] using h
end RiemannGaussian.SemiprimeD1StackRootSelectionAcquireOriginal
