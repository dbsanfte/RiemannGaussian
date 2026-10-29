/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedNetworkTopology
/-! # Actual marked-root structural caches, without another acquisition
The stopped original-input machine already holds the complete structural
source bank and chronological sparse inventory for the NEW marked network.
Only table-free bytes are reused. Its NEW record tape remains the separately
acquired operand, and the physical source retains its own checked clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedRootCaches
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1PacketReplayOriginal.acquire
attribute [local irreducible] SemiprimeD1IncidenceAcquisition.acquire SemiprimeD1IncidenceSearch.run
namespace P
export SemiprimeD1StackPackedRootInput (Stack program initial rootStack output)
export SemiprimeD1StackPackedRootInputEncoding (done)
end P
namespace Q
export SemiprimeD1StackSourceSelectionAcquire (Stack)
export SemiprimeD1StackSourceSelectionAcquireEncoding (result)
end Q
namespace T
export SemiprimeD1PackedNetworkTopology (inventory actual_selection actual_inventory)
end T
namespace A
export SemiprimeD1StackRootSelectionAcquireEncoding (dimension)
end A
/-- Literal finite embedding of every actual154-word structural cache into the full2505 bank. -/
def sourceStack (k : Q.Stack) : P.Stack :=
  P.rootStack (SemiprimeD1StackRootPacketInventory.rootStack
    (SemiprimeD1StackRootRecoveryWidth.rootStack
      (SemiprimeD1StackRootPacketPadding.rootStack
        (SemiprimeD1StackRootSelectionAcquire.acquisitionStack k))))
/-- Exact physically retained whole source bank, before changing its mathematical interpretation. -/
theorem old_source (bits : List Bool) (hN : 0<bitValue bits) (k : Q.Stack) :
    (P.done bits hN).data (sourceStack k)=
      Q.result (SemiprimeD1StackMarkedRootRecordsNetwork.old (bitValue bits) hN) (A.dimension bits) k := by
  have h0 := SemiprimeD1StackPackedRootInputOriginal.all_root_retained bits hN
    (SemiprimeD1StackRootPacketInventory.rootStack
      (SemiprimeD1StackRootRecoveryWidth.rootStack
        (SemiprimeD1StackRootPacketPadding.rootStack
          (SemiprimeD1StackRootSelectionAcquire.acquisitionStack k))))
  have h1 := SemiprimeD1StackRootPacketInventoryExecution.root_retained bits hN
    (SemiprimeD1StackRootRecoveryWidth.rootStack
      (SemiprimeD1StackRootPacketPadding.rootStack
        (SemiprimeD1StackRootSelectionAcquire.acquisitionStack k)))
  have h2 := SemiprimeD1StackRootRecoveryWidthExecution.root_retained bits hN
    (SemiprimeD1StackRootPacketPadding.rootStack
      (SemiprimeD1StackRootSelectionAcquire.acquisitionStack k))
  have h3 := SemiprimeD1StackRootPacketPaddingExecution.root_retained bits hN
    (SemiprimeD1StackRootSelectionAcquire.acquisitionStack k)
  have h4 := SemiprimeD1StackRootSelectionAcquireExecution.acquisition_retained bits hN k
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))
/-- Every literal structural cache byte has its exact NEW marked-network meaning. -/
theorem source_original (bits : List Bool) (hN : 0<bitValue bits) (k : Q.Stack) :
    (P.done bits hN).data (sourceStack k)=
      Q.result (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN) (A.dimension bits) k :=
  (old_source bits hN k).trans
    (congrArg (fun f => f k) (T.actual_selection (bitValue bits) hN (A.dimension bits))).symm
/-- The actual chronological placement tape is retained in the original full bank. -/
def placements : P.Stack := P.rootStack SemiprimeD1StackRootPacketInventory.output
/-- The actual observed-packet tape is retained separately from all tensor coefficients. -/
def packets : P.Stack := P.rootStack SemiprimeD1StackRootPacketInventory.packets
/-- Chronological source/slot/edge/valid bytes for the NEW marked network, without replay. -/
theorem placements_original (bits : List Bool) (hN : 0<bitValue bits) :
    (P.done bits hN).data placements=SemiprimeD1TensorTapeCodec.vectorBits
      ((T.inventory (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (A.dimension bits)).1.map SemiprimeD1StackPacketInventoryEncoding.placementBytes) := by
  have h0 := SemiprimeD1StackPackedRootInputOriginal.all_root_retained bits hN
    SemiprimeD1StackRootPacketInventory.output
  have h1 := SemiprimeD1StackRootPacketInventoryOriginal.output_original bits hN
  have hi := congrArg (fun x : List SemiprimeD1PacketInventory.Placement × List (List Bool) => SemiprimeD1TensorTapeCodec.vectorBits
    (x.1.map SemiprimeD1StackPacketInventoryEncoding.placementBytes))
      (T.actual_inventory (bitValue bits) hN (A.dimension bits))
  exact h0.trans (h1.trans hi.symm)
/-- Every raw packet byte and first-discovery order has its NEW marked-network meaning. -/
theorem packets_original (bits : List Bool) (hN : 0<bitValue bits) :
    (P.done bits hN).data packets=SemiprimeD1TensorTapeCodec.vectorBits
      (T.inventory (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (A.dimension bits)).2 := by
  have h0 := SemiprimeD1StackPackedRootInputOriginal.all_root_retained bits hN
    SemiprimeD1StackRootPacketInventory.packets
  have h1 := SemiprimeD1StackRootPacketInventoryOriginal.packets_original bits hN
  have hi := congrArg (fun x : List SemiprimeD1PacketInventory.Placement × List (List Bool) => SemiprimeD1TensorTapeCodec.vectorBits x.2)
    (T.actual_inventory (bitValue bits) hN (A.dimension bits))
  exact h0.trans (h1.trans hi.symm)
end RiemannGaussian.SemiprimeD1PackedRootCaches
