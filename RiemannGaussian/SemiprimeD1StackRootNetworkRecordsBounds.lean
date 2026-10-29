/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsExecution
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueResources
/-! # Whole actual root-record source clock from the two actual source traces
Output byte lengths follow from successful component runs. No native table,
output-size answer, count supplier or old mixed report clock enters the bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsBounds
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsExecution
open SemiprimeD1StackRootNetworkRecordsAcquisition
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
namespace FB
export SemiprimeD1StackFullFactorCatalogueBounds (runPolynomial timeBound_le)
export SemiprimeD1StackFullFactorCatalogueResources (polynomial_monomial)
end FB
namespace OB
export SemiprimeD1StackOwnerRecordsBounds (polynomial runCap budget_le polynomial_monomial)
end OB
namespace A
export SemiprimeD1StackAllDescriptorRecordRootBounds (arityCapacity)
end A
attribute [local irreducible] factorTape ownerBytes
/-- Every actual factor-source input word is bounded by the physically copied N bytes. -/
theorem factor_initial_length (bits:List Bool) (k:F.Stack) :((F.initial bits).data k).length ≤ bits.length:=by
  rw [factor_input]
  by_cases hk:k=F.originalInput
  · subst k;simp
  · simp [Function.update,hk]
/-- The acquired factor output length is paid by its SAME actual N-only execution trace. -/
theorem factor_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (factorTape bits).length ≤ bits.length+F.timeBound bits:=by
  unfold factorTape
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackFullFactorCatalogueExecution.source_run bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound F.program t bits.length _ _ (factor_initial_length bits) hr
  have ho:=h F.output
  exact ho.trans (Nat.add_le_add_left ht bits.length)
/-- The real owner source pays every acquired payload byte, including arbitrary retained prefix/tail input. -/
theorem owner_payload_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (ownerBytes bits hN fixed).length ≤
      bits.length+(prescription bits fixed tail).length+O.budget bits hN fixed tail:=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerRecordsExecution.source_run_prefix bits hc hN fixed tail
  have hi:=SemiprimeD1StackOwnerRecordsPrefixResources.initial_length bits (prescription bits fixed tail)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound O.program t
    (bits.length+(prescription bits fixed tail).length) _ _ hi hr
  have ho:=hd O.output
  rw [owner_output,List.length_append,List.length_singleton] at ho
  omega
/-- The SAME composed caller clock charges every component, copy, reversal, marker and halt. -/
theorem timeBound_components (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    timeBound bits hN fixed tail+1 ≤64*(bits.length+(prescription bits fixed tail).length+
      F.timeBound bits+O.budget bits hN fixed tail+1):=by
  have hf:=factor_length bits hc hN
  have ho:=owner_payload_length bits hc hN fixed tail
  unfold timeBound
  omega
/-- The old actual owner-source width polynomial scales linearly in actual physical prefix bytes. -/
theorem owner_prefix_scale (n P:Nat) :OB.runCap n P ≤ OB.polynomial n*(P+1):=by
  let X:=SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial n+
    5*SemiprimeD1StackOwnerRecordsBounds.baseCap n+100
  let Y:=3*SemiprimeD1StackOwnerRecordsBounds.baseCap n*
    (10000*(2*SemiprimeD1StackOwnerRecordsBounds.baseCap n+1))
  have hl:OB.runCap n P=X+Y*(P+1):=by
    unfold OB.runCap SemiprimeD1StackOwnerRecordsNumeric.rowCap
    dsimp only [X,Y]
    ring
  have hr:OB.polynomial n=X+2*Y:=by
    unfold OB.polynomial OB.runCap SemiprimeD1StackOwnerRecordsNumeric.rowCap
    dsimp only [X,Y]
    ring
  have hx:X ≤ X*(P+1):=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left X (by omega:1 ≤ P+1)
  have hy:Y*(P+1) ≤ (2*Y)*(P+1):=Nat.mul_le_mul_right (P+1) (by omega)
  rw [hl,hr]
  calc
    _ ≤ X*(P+1)+(2*Y)*(P+1):=Nat.add_le_add hx hy
    _= _:=by ring
/-- One fixed width/prefix polynomial before N and every actual prefix input. -/
def prefixPolynomial (n P:Nat) :Nat:=
  128*(n+P+FB.runPolynomial n+OB.polynomial n*(P+1)+1)
/-- The original table exponent, now with every real root-source operation included. -/
def runBoundPrefix (bits:List Bool) (P:Nat) :Nat:=prefixPolynomial bits.length P*2^(19*A.arityCapacity bits)
/-- Actual N-only source clock; its single prefix marker is physically pushed by the program. -/
def runBound (bits:List Bool) :Nat:=runBoundPrefix bits 1
/-- The whole actual caller-prefix clock fits the same fixed scope-rate envelope. -/
theorem timeBound_le_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    timeBound bits hN fixed tail+1 ≤ runBoundPrefix bits (prescription bits fixed tail).length:=by
  have ht:=timeBound_components bits hc hN fixed tail
  have hf:=FB.timeBound_le bits hc hN
  change F.timeBound bits ≤ FB.runPolynomial bits.length*2^(19*A.arityCapacity bits) at hf
  have ho:=OB.budget_le bits hc hN fixed tail
  change O.budget bits hN fixed tail+1 ≤ OB.runCap bits.length (prescription bits fixed tail).length at ho
  have hs:=owner_prefix_scale bits.length (prescription bits fixed tail).length
  have he:1 ≤ (2:Nat)^(19*A.arityCapacity bits):=Nat.pow_pos (by decide)
  have hp:=Nat.mul_le_mul_left
    (bits.length+(prescription bits fixed tail).length+
      OB.polynomial bits.length*((prescription bits fixed tail).length+1)+1) he
  unfold runBoundPrefix prefixPolynomial
  nlinarith only [ht,hf,ho,hs,hp]
/-- SAME original-N source clock, including its physical prefix seed. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    timeBound bits hN [] []+1 ≤ runBound bits:=by
  have h:=timeBound_le_prefix bits hc hN [] []
  simpa only [prescription_empty,List.length_singleton,runBound] using h
/-- Actual complete caller-prefix source trace with the same whole acquired-source bound. -/
theorem source_run_prefix_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃t ≤ runBoundPrefix bits (prescription bits fixed tail).length,
      SemiprimeD1StackCalls.run program t (initialPrefix bits (prescription bits fixed tail))=
        some (done bits hN fixed tail):=by
  obtain ⟨t,ht,hr⟩:=source_run_prefix bits hc hN fixed tail
  exact ⟨t,ht.trans ((Nat.le_succ _).trans (timeBound_le_prefix bits hc hN fixed tail)),hr⟩
/-- Complete real1804-role N-only source with its own fixed original scope-rate bound. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits hN [] []):=by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsBounds
