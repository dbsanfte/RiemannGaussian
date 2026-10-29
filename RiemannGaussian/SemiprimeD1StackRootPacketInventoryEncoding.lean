/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryCalls
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryInput
/-! # Actual shared root words supply the exact original inventory operands
Original key/catalogue lineage is derived internally, never supplied as runtime
data or a promise about decoded rows. The old frequency dictionary stays foreign.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryEncoding
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryInput
open SemiprimeD1StackRootPacketInventoryCalls
open SemiprimeBitArithmetic (bitValue)
namespace A
export SemiprimeD1StackRootPacketInventorySources (keys dimension)
end A
namespace N
export SemiprimeD1StackRootSelectionAcquireEncoding (net)
end N
/-- Actual same complete stopped original-input root, including the width72 bank. -/
def rootDone (bits:List Bool) (hN:0 < bitValue bits):C.State R.Stack R.Label:=
  SemiprimeD1StackRootRecoveryWidthEncoding.done bits hN
/-- Actual entire stopped inventory acquired from those exact two original source words. -/
def inventoryDone (bits:List Bool) (hN:0 < bitValue bits):C.State I.Stack I.Label:=
  E.done (SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)) (E.alphabet (A.dimension bits))
    (E.acquire (A.dimension bits) (A.keys bits hN))
/-- Both complete real banks survive the enclosing halt. -/
def result (bits:List Bool) (hN:0 < bitValue bits):Stack→List Bool:=
  data (rootDone bits hN).data (inventoryDone bits hN).data
/-- Exact all2270-word true halt, with every actual return and both transient flags cleared. -/
def done (bits:List Bool) (hN:0 < bitValue bits):C.State Stack Label:=⟨none,none,none,result bits hN,[]⟩
/-- Actual stopped-producer scratch, derived empty without an extra workspace premise. -/
theorem root_scratch (bits:List Bool) (hN:0 < bitValue bits):(rootDone bits hN).data R.copyScratch=[]:=
  SemiprimeD1StackRootPacketInventorySources.scratch_empty bits hN
/-- Both source words are actually acquired before the real inventory call. -/
theorem inventoryReady_original (bits:List Bool) (hN:0 < bitValue bits):
    inventoryReady (rootDone bits hN).data=
      (I.initial (SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)) (E.alphabet (A.dimension bits))).data:=by
  rw [inventoryReady_input]
  change (I.initial ((SemiprimeD1StackRootRecoveryWidthEncoding.done bits hN).data Source.keysRole)
    ((SemiprimeD1StackRootRecoveryWidthEncoding.done bits hN).data Source.catalogueRole)).data=_
  rw [SemiprimeD1StackRootPacketInventorySources.keys_acquired bits hN,
    SemiprimeD1StackRootPacketInventorySources.catalogue_acquired bits hN]
  rfl
/-- Generic original ID-lineage statement is proved before instantiating a large original network. -/
theorem generic_valid (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    B.ValidKeys a (SemiprimeD1IncidenceAcquisition.acquire net.leftCount net.rows.length 64 a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).keys:=
  SemiprimeD1StackPacketInventoryOriginal.original_valid net.leftCount net.rows.length a
    (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
/-- Every original actual key contains two acquired menu IDs; this is derived from the SAME source family. -/
theorem keys_valid (bits:List Bool) (hN:0 < bitValue bits):B.ValidKeys (A.dimension bits) (A.keys bits hN):=by
  have h:=generic_valid (N.net bits hN) (A.dimension bits)
  simpa only [A.keys,A.dimension,SemiprimeD1StackRootPacketPaddingEncoding.keys] using h
/-- SAME whole-source cap charges the shared root ONCE, both actual byte copies, real59 source and final halt. -/
def timeBound (bits:List Bool) (hN:0 < bitValue bits):Nat:=
  SemiprimeD1StackRootRecoveryWidthBounds.runBound bits+inventoryCopyTime (rootDone bits hN).data+
    B.byteBound (SemiprimeD1TensorTapeCodec.vectorBits (A.keys bits hN)) (E.alphabet (A.dimension bits))+3
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryEncoding
