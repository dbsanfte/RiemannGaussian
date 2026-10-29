/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecoveryWidthOriginal
import RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
/-! # Actual retained packet-vector/catalogue sources after ONE binary-input root
Only already sealed sources are imported. These word projections describe the
literal outputs of Root2211; no inventory input/count/result is assumed here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventorySources
open SemiprimeBitArithmetic (bitValue)
namespace R
export SemiprimeD1StackRootRecoveryWidth (Stack rootStack copyScratch output)
export SemiprimeD1StackRootRecoveryWidthEncoding (done)
end R
namespace P
export SemiprimeD1StackRootPacketPadding (rootStack)
end P
namespace S
export SemiprimeD1StackRootSelectionAcquire (output acquisitionStack)
end S
namespace A
export SemiprimeD1StackSourceSelectionAcquire (alphabetStack)
end A
namespace Alpha
export SemiprimeD1StackSourceAlphabet64 (aux)
end Alpha
/-- Actual acquired complete selected-key vector retained by the SAME whole N-only source. -/
def keysRole:R.Stack:=R.rootStack (P.rootStack S.output)
/-- Actual acquired original alphabet catalogue retained by that same whole source. -/
def catalogueRole:R.Stack:=R.rootStack (P.rootStack (S.acquisitionStack (A.alphabetStack (Alpha.aux .output))))
/-- Original selected-key interpretation, never an executing semantic getter. -/
def keys (bits:List Bool) (hN:0 < bitValue bits):List (List Bool):=
  SemiprimeD1StackRootPacketPaddingEncoding.keys bits hN
/-- The source's actual original schedule dimension, already physically acquired upstream. -/
def dimension (bits:List Bool):Nat:=SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits
/-- Generic alphabet projection is proved before substituting the original N/network. -/
theorem generic_catalogue (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    (SemiprimeD1StackSourceSelectionAcquireEncoding.done net a).data
      (A.alphabetStack (Alpha.aux .output))=SemiprimeD1StackPacketRowsOriginal.catalogue a:=rfl
/-- Every actual selected key comes from the same original-input producer, with no key advice. -/
theorem keys_acquired (bits:List Bool) (hN:0 < bitValue bits):
    (R.done bits hN).data keysRole=SemiprimeD1TensorTapeCodec.vectorBits (keys bits hN):=by
  have h0:=SemiprimeD1StackRootRecoveryWidthExecution.root_retained bits hN (P.rootStack S.output)
  have h1:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN S.output
  exact h0.trans (h1.trans (SemiprimeD1StackRootPacketPaddingEncoding.root_keys bits hN))
/-- The actual complete alphabet word is retained through selection, padding AND physical width acquisition. -/
theorem catalogue_acquired (bits:List Bool) (hN:0 < bitValue bits):
    (R.done bits hN).data catalogueRole=SemiprimeD1StackPacketRowsOriginal.catalogue (dimension bits):=by
  let k:=S.acquisitionStack (A.alphabetStack (Alpha.aux .output))
  have h0:=SemiprimeD1StackRootRecoveryWidthExecution.root_retained bits hN (P.rootStack k)
  have h1:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN k
  have h2:=SemiprimeD1StackRootSelectionAcquireExecution.acquisition_retained bits hN
    (A.alphabetStack (Alpha.aux .output))
  have h3:=generic_catalogue (SemiprimeD1StackRootSelectionAcquireEncoding.net bits hN) (dimension bits)
  exact h0.trans (h1.trans (h2.trans h3))
/-- The exact reused original source scratch is physically empty after all real root/width calls. -/
theorem scratch_empty (bits:List Bool) (hN:0 < bitValue bits):(R.done bits hN).data R.copyScratch=[]:=by
  have h0:=SemiprimeD1StackRootRecoveryWidthExecution.root_retained bits hN
    SemiprimeD1StackRootPacketPadding.copyScratch
  have h1:=SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN
    SemiprimeD1StackRootSelectionAcquire.copyScratch
  exact h0.trans (h1.trans (SemiprimeD1StackRootPacketPaddingEncoding.root_scratch bits hN))
end RiemannGaussian.SemiprimeD1StackRootPacketInventorySources
