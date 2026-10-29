/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingCalls
import RiemannGaussian.SemiprimeD1StackRootPacketPaddingInput
/-! # Exact original interpretation of the physically acquired packet-padding operands
The original network/key functions below describe the actual stopped words;
neither they nor a count/maximum/rounding answer are runtime operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketPaddingEncoding
open SemiprimeD1StackRootPacketPadding SemiprimeD1StackRootPacketPaddingInput
open SemiprimeBitArithmetic (bitValue)
namespace A
export SemiprimeD1StackRootSelectionAcquireEncoding (net dimension)
end A
namespace E
export SemiprimeD1StackSourcePacketPaddingEncoding (source done)
export SemiprimeD1StackSourcePacketPaddingBounds (polynomial)
end E
attribute [local irreducible] SemiprimeD1IncidenceAcquisition.acquire SemiprimeD1IncidenceSearch.run
/-- Exact original selected keys, used only as the meaning of an actually acquired physical word. -/
def keys (bits:List Bool) (hN:0 < bitValue bits) :List (List Bool) :=
  (SemiprimeD1IncidenceAcquisition.acquire (A.net bits hN).leftCount (A.net bits hN).rows.length 64 (A.dimension bits)
    (SemiprimeD1TensorNetwork.arity (A.net bits hN).rows) (SemiprimeD1TensorNetwork.owner (A.net bits hN).rows)).keys
/-- Actual whole original selected-key source halt, including all2114 retained physical words. -/
def rootDone (bits:List Bool) (hN:0 < bitValue bits) :C.State R.Stack R.Label :=
  SemiprimeD1StackRootSelectionAcquireEncoding.done bits hN
/-- Actual whole padding-source halt from those two physically copied original inputs. -/
def paddingDone (bits:List Bool) (hN:0 < bitValue bits) :C.State Q.Stack Q.Label :=
  E.done (keys bits hN) (A.dimension bits)
/-- All original producers, selected caches, frequency history and rounding output remain physically present. -/
def result (bits:List Bool) (hN:0 < bitValue bits) :Stack→List Bool :=
  data (rootDone bits hN).data (paddingDone bits hN).data
/-- Exact complete halt, after all real calls and paid transfers. -/
def done (bits:List Bool) (hN:0 < bitValue bits) :C.State Stack Label :=⟨none,none,none,result bits hN,[]⟩
/-- Generic stopped-source scratch projection is proved before original-N instantiation. -/
theorem acquired_scratch (root:SemiprimeD1StackRootNetworkRows.Stack→List Bool)
    (parameters:SemiprimeD1StackRootParameters.Stack→List Bool) (network:SemiprimeD1TensorNetwork.Network) (a:Nat) :
    SemiprimeD1StackRootSelectionAcquire.data root parameters
      (SemiprimeD1StackSourceSelectionAcquireEncoding.done network a).data R.copyScratch=[] :=rfl
/-- The reused actual producer scratch is genuinely empty, rather than an advised workspace premise. -/
theorem root_scratch (bits:List Bool) (hN:0 < bitValue bits) :(rootDone bits hN).data R.copyScratch=[] :=by
  have h:=acquired_scratch
    (SemiprimeD1StackRootSelectionAcquireEncoding.rootDone bits hN).data
    (SemiprimeD1StackRootSelectionAcquireEncoding.parameterDone bits).data (A.net bits hN) (A.dimension bits)
  simpa only [rootDone,SemiprimeD1StackRootSelectionAcquireEncoding.done,
    SemiprimeD1StackRootSelectionAcquireEncoding.result,SemiprimeD1StackRootSelectionAcquireEncoding.acquisitionDone] using h
/-- The actual complete key vector has been computed by the upstream same original-input source. -/
theorem root_keys (bits:List Bool) (hN:0 < bitValue bits) :
    (rootDone bits hN).data R.output=SemiprimeD1TensorTapeCodec.vectorBits (keys bits hN) :=
  SemiprimeD1StackRootSelectionAcquireExecution.output_original bits hN
/-- The actual copied unary dimension is the exact original schedule exponent. -/
theorem root_dimension (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    (rootDone bits hN).data (R.parameterStack SemiprimeD1StackRootParameters.exponent)=
      List.replicate (A.dimension bits) true :=by
  have h:=SemiprimeD1StackRootSelectionAcquireExecution.parameters_retained bits hN SemiprimeD1StackRootParameters.exponent
  exact h.trans (SemiprimeD1StackRootParametersOriginal.exponent_original bits hc)
/-- Both actual stopped-producer handoffs form the honest original padding-source input bank. -/
theorem paddingReady_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0 < bitValue bits) :
    paddingReady (rootDone bits hN).data=(E.source (keys bits hN) (A.dimension bits)).data :=by
  rw [paddingReady_input]
  change SemiprimeD1StackSourcePacketPadding.input ((rootDone bits hN).data R.output)
    ((rootDone bits hN).data (R.parameterStack SemiprimeD1StackRootParameters.exponent))=_
  rw [root_keys bits hN,root_dimension bits hc hN]
  rfl
/-- SAME whole-program cap includes both actual source clocks, both actual copies, both real calls and halt. -/
def timeBound (bits:List Bool) (hN:0 < bitValue bits) :Nat :=
  SemiprimeD1StackRootSelectionAcquireBounds.runBound bits+paddingCopyTime (rootDone bits hN).data+
    E.polynomial (keys bits hN) (A.dimension bits)+3
end RiemannGaussian.SemiprimeD1StackRootPacketPaddingEncoding
