/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsBinding
/-! # Precision VALUE and context-rank bounds derived from the original N-only source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsValues
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackRootPhaseFreshRecordsBinding
namespace H
export SemiprimeD1StackPhaseChildContextPrimitives (precision count)
end H
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (aux program)
export SemiprimeD1StackPhaseWorkingPrecisionComponents (accepted product delta)
end P
namespace W
export SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic (height height_le blocks)
end W
/-- Real child rank is bounded by the original bounded height and level tally. -/
theorem count_le (a u edges:Nat) (t:List Bool) :H.count a u edges t ≤ (3*edges+u)*u :=by
  exact Nat.mul_le_mul (W.height_le edges u) (Nat.sub_le _ _)
/-- The binary precision VALUE is derived from the actual shifted additions,
including actual rejected outputs; no logarithmic input-size assumption is used. -/
theorem precision_value (a u edges:Nat) (t:List Bool) :
    bitValue (H.precision a u edges t [false,true]) ≤ 2+8*(3*edges+u)*2^a+8*edges*(a+1) :=by
  change bitValue (if P.accepted a u t then
    SemiprimeD1StackPhaseWorkingPrecisionArithmetic.precisionWord (W.height edges u)
      (P.product a edges) (P.delta a t) [false,true] else []) ≤ _
  split
  · rw [SemiprimeD1StackPhaseWorkingPrecisionArithmetic.precisionWord_value]
    have hh:=W.height_le edges u
    have hd:2^(P.delta a t) ≤ 2^a:=Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have hm:W.height edges u*2^(P.delta a t) ≤ (3*edges+u)*2^a:=Nat.mul_le_mul hh hd
    change 2+8*W.height edges u*2^(P.delta a t)+8*(edges*(a+1)) ≤ _
    nlinarith only [hm]
  · exact Nat.zero_le _
/-- Actual precision BYTE length is bounded from its OWN successful P48 source,
separately from the value bound required for the physical context expansion. -/
theorem precision_bytes (a u edges:Nat) (t:List Bool) :
    (H.precision a u edges t [false,true]).length ≤
      edges+a+u+t.length+2+10^12*(edges+a+u+t.length+3)^4 :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackPhaseWorkingPrecisionExecution.source_run a u edges t [false,true]
  have hd:=SemiprimeD1StackReturnLink.run_data_bound P.program q
    (edges+a+u+t.length+2) _ _
    (SemiprimeD1StackPhaseWorkingPrecisionBounds.initial_bound a u edges t [false,true]) hr
  have h:=hd (P.aux .output)
  change (H.precision a u edges t [false,true]).length ≤ edges+a+u+t.length+2+q at h
  change q ≤ 10^12*(edges+a+u+t.length+3)^4 at hq
  omega
/-- Exact root old rank is ONE and the child rank is actual q; every actual
unary-header byte and binary precision value is present in this resource. -/
theorem resource_eq (a u edges:Nat) (t:List Bool) :
    SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t [false,true] []=
      edges+a+u+t.length+3+4*H.count a u edges t+
        (H.precision a u edges t [false,true]).length+bitValue (H.precision a u edges t [false,true])+22 :=by
  simp only [SemiprimeD1StackPhaseChildContextFreshBounds.resource,
    SemiprimeD1StackPhaseChildContextBounds.resource,SemiprimeD1StackJetContextBounds.resource,
    SemiprimeD1TensorTapeCodec.vectorBits,List.map_cons,List.map_nil,
    List.length_cons,List.length_nil,List.prod_cons,List.prod_nil,Nat.mul_one,
    SemiprimeSourceHistogramKeyBits.frame_length,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  have hp:bitValue [false,true]=2:=rfl
  rw [hp]
  omega
/-- Coarse honest VALUE-charged inventory for each actual phase, including both context ranks. -/
theorem resource_le (a u edges:Nat) (t:List Bool) :
    SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t [false,true] [] ≤
      100*(edges+a+u+t.length+3+10^12*(edges+a+u+t.length+3)^4+
        (3*edges+u)*u+(3*edges+u)*2^a+edges*(a+1)+1) :=by
  rw [resource_eq]
  have hq:=count_le a u edges t
  have hv:=precision_value a u edges t
  have hb:=precision_bytes a u edges t
  simp only [Nat.mul_assoc] at hv ⊢
  omega
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsValues
