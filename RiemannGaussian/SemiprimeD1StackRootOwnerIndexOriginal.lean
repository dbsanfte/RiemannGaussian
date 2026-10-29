/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexResources
/-! # Whole original-N owner-index output and one fixed original-input clock
The complete root table/record and count acquisition occurs on the actual path.
Both actual alias words and the entire original1804-role bank are retained.
Uniform coefficients/degrees precede ALL N and all physical caller prefixes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexOriginal
open SemiprimeD1StackRootOwnerIndex SemiprimeD1StackRootOwnerIndexComponents
open SemiprimeD1StackRootOwnerIndexExecution
open SemiprimeBitArithmetic (bitValue)
namespace Enc
export SemiprimeD1StackNetworkOwnerIndexEncoding (ownerPairs ownerWord original_fibre)
end Enc
/-- Both shared inputs and every real private source role have their exact actual final index values. -/
theorem index_preserved (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) (k:I.Stack) :
    (done bits hN fixed tail).data (indexStack k)=(indexDone bits hN fixed).data k :=by
  apply data_index
  · exact ((root_output bits hc hN fixed tail).trans (indexSource_vertices bits hN fixed)).trans
      (E.original_retained (rootowners bits hN fixed) (rootSuffix bits hN fixed)).symm
  · exact ((root_left bits hN fixed tail).trans (indexSource_leftCount bits hN fixed)).trans
      (E.count_retained (rootowners bits hN fixed) (rootSuffix bits hN fixed)).symm
/-- Entire original root catalogue, in actual original owner/local-port order, is acquired from N alone. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (done bits hN fixed tail).data output=SemiprimeD1StackOwnerLookup.records
      (Enc.ownerPairs (net bits hN fixed).leftCount 0 (net bits hN fixed).left.toList) [] :=by
  rw [show output=indexStack .output from rfl,index_preserved bits hc hN fixed tail]
  exact SemiprimeD1StackNetworkOwnerIndexOriginal.output_original (net bits hN fixed)
/-- Original root well-formedness derives from its actual old compiler, never from supplied runtime graph advice. -/
theorem original_wellFormed (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    SemiprimeD1TensorNetwork.WellFormed (net bits hN fixed) :=
  SemiprimeD1RootNetwork.acquirePositive_wellFormed (bitValue bits) hN fixed
/-- Every original occurrence has exactly its unique original root owner in the actual acquired catalogue. -/
theorem original_owner_fibre (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (p:Fin (SemiprimeD1TensorNetwork.scope (net bits hN fixed).rows)) :
    SemiprimeD1StackOwnerFibre.values (SemiprimeD1StackUnaryDivmod.unary p.val)
      (Enc.ownerPairs (net bits hN fixed).leftCount 0 (net bits hN fixed).left.toList)=
        [Enc.ownerWord (net bits hN fixed).leftCount
          (SemiprimeD1TensorNetworkLayout.leftGroup (net bits hN fixed).rows p).val] :=
  Enc.original_fibre (net bits hN fixed) (original_wellFormed bits hN fixed) p
/-- One SAME original-binary-N execution and exact original catalogue, with its full acquisition clock. -/
theorem source_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃q ≤ SemiprimeD1StackRootOwnerIndexBounds.runBound bits,
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=SemiprimeD1StackOwnerLookup.records
        (Enc.ownerPairs (net bits hN []).leftCount 0 (net bits hN []).left.toList) [] :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackRootOwnerIndexBounds.source_run_bounded bits hc hN
  exact ⟨q,hq,hr,output_original bits hc hN [] []⟩
/-- Fixed coefficient and degree before ALL canonical N; the exponent pays both actual acquisitions. -/
theorem uniform_original :∃coef degree:Nat,∀(bits:List Bool)
    (_hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits),
    ∃q ≤ coef*(SemiprimeMacroParameters.bitLength (bitValue bits)+1)^degree*
      2^(38*SemiprimeMacroParameters.scopeBound (SemiprimeMacroParameters.bitLength (bitValue bits))),
      SemiprimeD1StackCalls.run program q (initial bits)=some (done bits hN [] []) ∧
      (done bits hN [] []).data output=SemiprimeD1StackOwnerLookup.records
        (Enc.ownerPairs (net bits hN []).leftCount 0 (net bits hN []).left.toList) [] :=by
  obtain ⟨coef,degree,hs⟩:=SemiprimeD1StackRootOwnerIndexResources.source_run_monomial
  refine ⟨coef,degree,?_⟩
  intro bits hc hN
  obtain ⟨q,hq,hr⟩:=hs bits hc hN
  have hw:=SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc
  refine ⟨q,?_,hr,output_original bits hc hN [] []⟩
  simpa only [SemiprimeD1StackAllDescriptorRecordRootBounds.arityCapacity,hw] using hq
/-- The actual finite machine really starts at binary-N-only Turing.initList. -/
noncomputable def machineOriginal (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits hN [] [])))
      (SemiprimeD1StackRootOwnerIndexBounds.runBound bits) :=
  SemiprimeD1StackRootOwnerIndexResources.ownerIndexInTime bits hc hN
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexOriginal
