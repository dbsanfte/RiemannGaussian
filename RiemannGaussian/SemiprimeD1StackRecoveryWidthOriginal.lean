/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthStorage
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingOriginal
import RiemannGaussian.SemiprimeD1StackRootPhaseGridBounds
/-! # Actual original root metadata supplies the width source, with a fixed global bit-size cap
The program here still has its honest two acquired-unary-word front door. These
lemmas bind that boundary to ACTUAL retained Root2139 words and derive a fixed
polynomial in original bit length. A future literal caller must execute/alias the
two complete sources; no N-only width-composite or Hermite arithmetic is claimed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthOriginal
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthExecution SemiprimeD1StackRecoveryWidthBounds
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Meta
export SemiprimeD1StackRootControllerMetadata (result edges exponent program initial done)
end Meta
namespace RP
export SemiprimeD1StackRootPacketPadding (Stack rootStack)
export SemiprimeD1StackRootPacketPaddingEncoding (done)
end RP
namespace RS
export SemiprimeD1StackRootSelectionAcquire (parameterStack)
end RS
namespace Param
export SemiprimeD1StackRootParameters (edges exponent)
end Param
/-- Original exponent of the actual acquired root grid, not a supplied width or parameter. -/
def originalA (bits:List Bool) :Nat:=SemiprimeD1StackRootPhaseGridEncoding.exponentValue bits
/-- Original occurrence count is the number ACTUALLY acquired by the literal scope source. -/
def originalM (bits:List Bool) :Nat:=SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits
/-- Original exponent field retained through the sealed entire binary-N selected-key/frequency/padding source. -/
def exponentRole :RP.Stack:=RP.rootStack (RS.parameterStack Param.exponent)
/-- Separate actual incidence-count field; this is M, not the Boolean-wire count. -/
def edgesRole :RP.Stack:=RP.rootStack (RS.parameterStack Param.edges)
attribute [local irreducible] originalM
  SemiprimeD1StackRootScopeBankExecution.occurrenceCount
  SemiprimeD1StackRootScopeBankExecution.wireValue
  SemiprimeD1StackRootScopeBankExecution.records
  SemiprimeD1StackRootScopeBankExecution.result
  SemiprimeD1StackRootControllerMetadata.result
  SemiprimeD1StackRootParametersExecution.result
/-- Actual metadata98 acquired the exact physical original M word. -/
theorem metadata_edges (bits:List Bool) :Meta.result bits Meta.edges=unary (originalM bits):=by
  have h:=SemiprimeD1StackRootControllerMetadataOriginal.source_preserved bits SemiprimeD1StackRootScopeBank.count
  unfold originalM
  exact h.trans (SemiprimeD1StackRootScopeBankExecution.result_counts bits).1
/-- Actual complete Root2139 retained the physical exponent word required by this source. -/
theorem root_exponent (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (RP.done bits hN).data exponentRole=unary (originalA bits):=by
  have h0:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN (RS.parameterStack Param.exponent)
  have h1:=SemiprimeD1StackRootSelectionAcquireExecution.parameters_retained bits hN Param.exponent
  have h2:=SemiprimeD1StackRootParametersOriginal.exponent_original bits hc
  exact h0.trans (h1.trans h2)
/-- Actual complete Root2139 retained M as a physically paid unary count. -/
theorem root_edges (bits:List Bool) (hN:0<bitValue bits) :(RP.done bits hN).data edgesRole=unary (originalM bits):=by
  have h0:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN (RS.parameterStack Param.edges)
  have h1:=SemiprimeD1StackRootSelectionAcquireExecution.parameters_retained bits hN Param.edges
  have h2:=SemiprimeD1StackRootParametersOriginal.metadata_preserved bits Meta.edges
  exact h0.trans (h1.trans (h2.trans (metadata_edges bits)))
/-- The original incidence count bound comes from the SAME actual metadata-source run and its physical output word. -/
theorem originalM_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    originalM bits≤ bits.length+10^50*(bits.length+1)^10:=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootControllerMetadataBounds.source_run_polynomial bits hc hN
  have h:=SemiprimeD1StackReturnLink.run_data_bound Meta.program q bits.length _ _
    (SemiprimeD1StackRootControllerMetadataBounds.initial_role_bound bits) hr Meta.edges
  change (Meta.result bits Meta.edges).length≤ bits.length+q at h
  rw [metadata_edges] at h
  simp only [unary,List.length_replicate] at h
  omega
/-- Every original fixed-prefix root graph has exactly the M value physically acquired by the source. -/
theorem originalM_graph (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    originalM bits=SemiprimeD1TensorNetwork.edgeCount (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed):=by
  have h:=SemiprimeD1StackRootControllerMetadataOriginal.edges_original bits hN fixed
  rw [metadata_edges] at h
  have hl:=congrArg List.length h
  simpa only [unary,List.length_replicate] using hl
/-- A fixed original bit-size coefficient, before all original N and metadata values. -/
def sizingCoefficient :Nat:=10^51
/-- Actual a/M and the generated grid cardinality N are all paid by a fixed polynomial in original bit length. -/
theorem original_envelope (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    inputEnvelope (originalA bits) (originalM bits)≤ sizingCoefficient*(bits.length+1)^10:=by
  have ha:=SemiprimeD1StackRootPhaseGridBounds.exponent_le bits hc
  have hnumeric:=SemiprimeD1StackRootPhaseGridBounds.numeric_bounds bits.length (originalA bits) ha
  have hm:=originalM_bound bits hc hN
  have h1:(bits.length+1)≤(bits.length+1)^10:=Nat.le_pow (by decide:0<(10:Nat))
  have h4:(bits.length+1)^4≤(bits.length+1)^10:=Nat.pow_le_pow_right (by omega) (by decide:4≤10)
  have hpos:1≤(bits.length+1)^10:=Nat.one_le_pow _ _ (by omega)
  unfold inputEnvelope V.envelope gridSize sizingCoefficient
  nlinarith only [hnumeric.1,hnumeric.2,hm,h1,h4,hpos]
/-- Fixed own whole-width-clock coefficient in original bit-size; N and W have already been paid by VALUE. -/
def globalClockCoefficient :Nat:=100000000000000000000*sizingCoefficient^12
/-- Actual72-role template acquisition has a fixed global original-bitlength clock, with no old native report transport. -/
theorem original_clock (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    polynomial (originalA bits) (originalM bits)≤ globalClockCoefficient*(bits.length+1)^120:=by
  have h:=Nat.mul_le_mul_left 100000000000000000000 (Nat.pow_le_pow_left (original_envelope bits hc hN) 12)
  simpa only [polynomial,globalClockCoefficient,mul_pow,←pow_mul,Nat.mul_assoc] using h
/-- Complete width source can consume the ACTUAL retained Root2139 words without any supplied N/W/template. -/
theorem retained_source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q≤ globalClockCoefficient*(bits.length+1)^120,SemiprimeD1StackCalls.run program q
      (initial ((RP.done bits hN).data exponentRole) ((RP.done bits hN).data edgesRole))=
        some (done (originalA bits) (originalM bits)):=by
  rw [root_exponent bits hc hN,root_edges bits hN]
  obtain ⟨q,hq,hr⟩:=source_run_bounded (originalA bits) (originalM bits)
  exact ⟨q,hq.trans (original_clock bits hc hN),hr⟩
/-- Original bit-size FALSE-template bytes are acquired exactly, not supplied as a polynomial evaluator answer. -/
theorem retained_template (bits:List Bool) :
    (done (originalA bits) (originalM bits)).data (aux .output)=
      List.replicate (SemiprimeD1RecoveryNodeBits.width (originalA bits) (originalM bits)) false:=rfl
/-- Fixed all72/return coefficient for every actual original-metadata prefix. -/
def globalSpaceCoefficient :Nat:=100000000000000000000000*sizingCoefficient^12
/-- The complete generic storage cap likewise gives a fixed original-size polynomial for ALL72 roles and real returns. -/
theorem original_space (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    100000000000000000000000*(inputEnvelope (originalA bits) (originalM bits))^12≤
      globalSpaceCoefficient*(bits.length+1)^120:=by
  have h:=Nat.mul_le_mul_left 100000000000000000000000 (Nat.pow_le_pow_left (original_envelope bits hc hN) 12)
  simpa only [globalSpaceCoefficient,mul_pow,←pow_mul,Nat.mul_assoc] using h
/-- Every actual compiled72-role prefix from the two retained Root2139 fields has the same fixed original-size cell cap. -/
theorem retained_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial ((RP.done bits hN).data exponentRole) ((RP.done bits hN).data edgesRole))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      globalSpaceCoefficient*(bits.length+1)^120:=by
  rw [root_exponent bits hc hN,root_edges bits hN] at hr
  exact (SemiprimeD1StackRecoveryWidthStorage.machine_prefix_cells (originalA bits) (originalM bits) fuel cfg hr).trans
    (original_space bits hc hN)
end RiemannGaussian.SemiprimeD1StackRecoveryWidthOriginal
