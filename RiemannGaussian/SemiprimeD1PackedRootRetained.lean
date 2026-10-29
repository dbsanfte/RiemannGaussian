/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryOriginal
/-! # Exact retained source subbank for original-input marked continuation
This identifies literal physical words of the same acquired2270-role source.
It neither re-executes the original1804 source nor transports any report clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1PackedRootRetained
/-- Static1804-source inclusion through all six retained original-input banks. -/
def embed (k : SemiprimeD1StackRootNetworkRecords.Stack) : SemiprimeD1StackRootPacketInventory.Stack :=
  .inl (.inl (.inl (.inl (.inl (.inl k)))))
/-- Every actual stopped original-source word is still present byte for byte. -/
theorem source_projection (bits : List Bool) (hN : 0<SemiprimeBitArithmetic.bitValue bits)
    (k : SemiprimeD1StackRootNetworkRecords.Stack) :
    (SemiprimeD1StackRootPacketInventoryEncoding.done bits hN).data (embed k)=
      (SemiprimeD1StackRootNetworkRecordsExecution.done bits hN [] []).data k := by
  let k1:=SemiprimeD1StackRootOwnerIndex.rootStack k
  let k2:=SemiprimeD1StackRootNetworkRows.rootStack k1
  let k3:=SemiprimeD1StackRootSelectionAcquire.rootStack k2
  let k4:=SemiprimeD1StackRootPacketPadding.rootStack k3
  let k5:=SemiprimeD1StackRootRecoveryWidth.rootStack k4
  exact (SemiprimeD1StackRootPacketInventoryExecution.root_retained bits hN k5).trans
    ((SemiprimeD1StackRootRecoveryWidthExecution.root_retained bits hN k4).trans
    ((SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN k3).trans
    ((SemiprimeD1StackRootSelectionAcquireExecution.root_retained bits hN k2).trans
    ((SemiprimeD1StackRootNetworkRowsExecution.root_retained bits hN [] [] k1).trans
      (SemiprimeD1StackRootOwnerIndexExecution.root_retained bits hN [] [] k)))))
/-- Actual original N is shared with the same retained source input. -/
theorem original_input : embed SemiprimeD1StackRootNetworkRecords.originalInput=
    SemiprimeD1StackRootPacketInventory.originalInput := rfl
/-- Actual stopped2270 input still contains precisely its original binary word. -/
theorem retained_N (bits : List Bool) (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    (SemiprimeD1StackRootPacketInventoryEncoding.done bits hN).data
      SemiprimeD1StackRootPacketInventory.originalInput=bits := by
  rw [←original_input,source_projection]
  exact SemiprimeD1StackRootNetworkRecordsExecution.input_preserved bits hN [] []
/-- The actual retained restoring scratch is empty, ready for another real copy. -/
theorem scratch_empty (bits : List Bool) (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    (SemiprimeD1StackRootPacketInventoryEncoding.done bits hN).data
      SemiprimeD1StackRootPacketInventory.copyScratch=[] :=
  SemiprimeD1StackRootPacketInventoryEncoding.root_scratch bits hN
end RiemannGaussian.SemiprimeD1PackedRootRetained
