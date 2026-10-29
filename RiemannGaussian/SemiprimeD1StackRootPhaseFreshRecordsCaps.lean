/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsValues
/-! # Closed original-N envelopes for actual rank/precision VALUE expansions -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
set_option exponentiation.threshold 4096
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCaps
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsBinding SemiprimeD1StackRootPhaseFreshRecordsValues
open SemiprimeD1StackRootPhaseFreshRecordsSource SemiprimeD1StackRootPhaseFreshRecordsRows
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1StackRootPhaseParametersEncoding.result
namespace C
export SemiprimeD1StackRootPhaseParametersCaps (input_size_le phase_count_le)
end C
/-- Uniform numeric envelope separately pays the dyadic VALUE factor in the actual shifted precision. -/
theorem resource_uniform (a u edges:Nat) (t:List Bool) (B D:Nat)
    (hi:edges+a+u+t.length+3 ≤ B) (hD:2^a ≤ D) (hB:1 ≤ B) :
    SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t [false,true] [] ≤
      10^16*(B^4+B*D) :=by
  have h:=resource_le a u edges t
  have he:edges ≤ B:=by omega
  have hu:u ≤ B:=by omega
  have ha:a+1 ≤ B:=by omega
  have hh:3*edges+u ≤ 4*B:=by omega
  have hq:(3*edges+u)*u ≤ 4*B^2:=by
    have hm:=Nat.mul_le_mul hh hu
    nlinarith only [hm]
  have hp:(3*edges+u)*2^a ≤ 4*(B*D):=by
    have hm:=Nat.mul_le_mul hh hD
    nlinarith only [hm]
  have hr:edges*(a+1) ≤ B^2:=by
    have hm:=Nat.mul_le_mul he ha
    nlinarith only [hm]
  have hi4:(edges+a+u+t.length+3)^4 ≤ B^4:=Nat.pow_le_pow_left hi 4
  have h1:B ≤ B^4:=Nat.le_pow (by decide)
  have h2:B^2 ≤ B^4:=Nat.pow_le_pow_right hB (by decide)
  omega
/-- Original actual per-phase context resource is polynomial in binary N width,
including actual P VALUE and child rank; binary P byte length alone is insufficient. -/
theorem fresh_resource (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (t:List Bool) (ht:t∈O.phases bits) :
    SemiprimeD1StackPhaseChildContextFreshBounds.resource
      (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) t [false,true] [] ≤
        10^56*(bits.length+1)^5 :=by
  let L:=bits.length+1
  have hi:=C.input_size_le bits hc hN t ht
  have hpow0:2^(O.exponentValue bits+1) ≤ 10^30*L^4:=
    (SemiprimeD1StackRootPhaseGridBounds.numeric_bounds bits.length (O.exponentValue bits)
      (SemiprimeD1StackRootPhaseGridBounds.exponent_le bits hc)).2
  have hpow:2^(O.exponentValue bits) ≤ 10^30*L^4:=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hpow0
  have h:=resource_uniform (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) t
    (10^9*L) (10^30*L^4) hi hpow (by
      have h:0<10^9*L:=by dsimp [L];positivity
      omega)
  calc
    _ ≤ 10^16*((10^9*L)^4+(10^9*L)*(10^30*L^4)):=h
    _=10^52*L^4+10^55*L^5:=by ring
    _ ≤ 10^56*L^5:=by
      have h45:L^4 ≤ L^5:=Nat.pow_le_pow_right (by dsimp [L];omega) (by decide)
      exact (Nat.add_le_add (Nat.mul_le_mul_left _ h45) (Nat.le_refl _)).trans
        (by rw [←Nat.add_mul];exact Nat.mul_le_mul_right _ (by norm_num))
/-- Every actual retained188-cell source word is bounded by its OWN complete N-only run. -/
theorem root_word (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) (k:R.Stack) :
    (O.result bits k).length ≤ 10^153*(bits.length+1)^20 :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootPhaseParametersExecution.source_run bits hc hN
  have hd:=SemiprimeD1StackReturnLink.run_data_bound R.program q bits.length _ _
    (SemiprimeD1StackRootPhaseParametersBounds.initial_role_bound bits) hr
  have hk:=hd k
  change (O.result bits k).length ≤ bits.length+q at hk
  have ht:=SemiprimeD1StackRootPhaseParametersBounds.runBound_le bits hc hN
  have hn:bits.length+1 ≤ (bits.length+1)^20:=Nat.le_pow (by decide)
  omega
/-- Actual heap/ordinal input plus the derived VALUE inventory has one closed original-N cap. -/
theorem client_resource (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (i:Fin (banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)).length)
    (t:List Bool) (ht:t∈O.phases bits) :
    SemiprimeD1StackPhaseCacheFreshBounds.resource
      (banks (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) (O.phases bits)) i
      (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) t [false,true] [] ≤
        10^154*(bits.length+1)^20 :=by
  have hh:=root_word bits hc hN R.heap
  rw [source_heap] at hh
  have hn:=root_word bits hc hN (R.aux .counter)
  rw [source_counter,List.length_replicate] at hn
  have hi:i.val ≤ 10^153*(bits.length+1)^20:=by omega
  have hf:=fresh_resource bits hc hN t ht
  have h5:(bits.length+1)^5 ≤ (bits.length+1)^20:=Nat.pow_le_pow_right (by omega) (by decide)
  have hf':SemiprimeD1StackPhaseChildContextFreshBounds.resource
      (O.exponentValue bits) (O.levelsValue bits) (O.edgeValue bits) t [false,true] [] ≤
        10^56*(bits.length+1)^20:=hf.trans (Nat.mul_le_mul_left _ h5)
  change (E.heap _).length+_+_+1+1+_+1 ≤ _
  simp only [List.length_replicate]
  have hp:1 ≤ (bits.length+1)^20:=one_le_pow₀ (by omega)
  omega
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsCaps
