/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedRootCaches
/-! # Actual original-input operands for the structural child factory
The complete63 selector,21 occurrence and59 inventory allocations already
exist in Root2505. These are fixed address inclusions, not runtime getters.
No coefficient or table payload is among these structural inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedRootFactoryInputs
open SemiprimeBitArithmetic (bitValue)
namespace P
export SemiprimeD1StackPackedRootInput (Stack rootStack output)
export SemiprimeD1StackPackedRootInputEncoding (done)
end P
namespace S
export SemiprimeD1StackSourceIncidenceSelect (Stack environmentStack aux)
end S
namespace O
export SemiprimeD1StackSourceOccurrences (Stack)
end O
namespace I
export SemiprimeD1StackPacketInventory (Stack)
end I
/-- Every selector role is an already allocated literal root address. -/
def selector (k : S.Stack) : P.Stack := SemiprimeD1PackedRootCaches.sourceStack
  (SemiprimeD1StackSourceSelectionAcquire.selectorStack k)
/-- Every occurrence role is an already allocated literal root address. -/
def occurrence (k : O.Stack) : P.Stack := SemiprimeD1PackedRootCaches.sourceStack
  (SemiprimeD1StackSourceSelectionAcquire.occurrenceStack k)
/-- Every inventory role is retained, including unused maps and shadows. -/
def inventory (k : I.Stack) : P.Stack := P.rootStack (SemiprimeD1StackRootPacketInventory.inventoryStack k)
/-- All143 actual retained roles, with no duplicate allocation or discarded shadow. -/
abbrev Cache := S.Stack⊕(O.Stack⊕I.Stack)
/-- The exact static inclusion of the complete three-bank cache into Root2505. -/
def cache : Cache→P.Stack := Sum.elim selector (Sum.elim occurrence inventory)
/-- The actual complete selector bank has its NEW weighted-network interpretation. -/
theorem selector_original (bits : List Bool) (hN : 0<bitValue bits) (k : S.Stack) :
    (P.done bits hN).data (selector k)=
      (SemiprimeD1StackSourceSelectionAcquireEncoding.selectorDone
        (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)
        (SemiprimeD1StackRootSelectionAcquireEncoding.dimension bits)).data k :=
  (SemiprimeD1PackedRootCaches.source_original bits hN
    (SemiprimeD1StackSourceSelectionAcquire.selectorStack k)).trans
      (SemiprimeD1StackSourceSelectionAcquireOriginal.selector_retained _ _ k)
/-- The actual complete occurrence bank has its NEW weighted-network interpretation. -/
theorem occurrence_original (bits : List Bool) (hN : 0<bitValue bits) (k : O.Stack) :
    (P.done bits hN).data (occurrence k)=
      (SemiprimeD1StackSourceSelectionAcquireEncoding.occurrenceDone
        (SemiprimeD1StackMarkedRootRecordsNetwork.network (bitValue bits) hN)).data k :=
  (SemiprimeD1PackedRootCaches.source_original bits hN
    (SemiprimeD1StackSourceSelectionAcquire.occurrenceStack k)).trans
      (SemiprimeD1StackSourceSelectionAcquireOriginal.occurrence_retained _ _ k)
/-- Every actual inventory word remains exactly its own stopped producer word. -/
theorem inventory_retained (bits : List Bool) (hN : 0<bitValue bits) (k : I.Stack) :
    (P.done bits hN).data (inventory k)=
      (SemiprimeD1StackRootPacketInventoryEncoding.inventoryDone bits hN).data k :=
  (SemiprimeD1StackPackedRootInputOriginal.all_root_retained bits hN
    (SemiprimeD1StackRootPacketInventory.inventoryStack k)).trans
      (SemiprimeD1StackRootPacketInventoryExecution.inventory_retained bits hN k)
/-- Physical selected-ID dictionary operand; it contains no table coefficients. -/
def environment : P.Stack := selector (S.environmentStack (SemiprimeD1StackSourceEnvironment.aux .dictionary))
/-- Physical original colour-row catalogue operand. -/
def catalogue : P.Stack := selector (S.aux .catalogue)
/-- Physical owner-marker operand, including isolated owners. -/
def owners : P.Stack := selector (S.aux .owners)
/-- Physical factor-marker operand, including empty factors. -/
def factors : P.Stack := selector (S.aux .factors)
/-- Physical original occurrence pair stream, with repetitions retained. -/
def pairs : P.Stack := occurrence .output
/-- Physical chronological placement operand, distinct from the record table. -/
def placements : P.Stack := inventory SemiprimeD1StackPacketInventory.output
/-- Physical observed-packet operand, in actual first-discovery order. -/
def packets : P.Stack := inventory SemiprimeD1StackPacketInventory.packets
/-- All143 roles really remain distinct after their static inclusion into the original root bank. -/
theorem cache_injective : Function.Injective cache := by
  intro a b h
  rcases a with a|a|a <;> rcases b with b|b|b <;>
    simp only [cache,Sum.elim_inl,Sum.elim_inr,selector,occurrence,inventory,
      SemiprimeD1PackedRootCaches.sourceStack,SemiprimeD1StackPackedRootInput.rootStack,
      SemiprimeD1StackRootPacketInventory.rootStack,SemiprimeD1StackRootPacketInventory.inventoryStack,
      SemiprimeD1StackRootRecoveryWidth.rootStack,SemiprimeD1StackRootPacketPadding.rootStack,
      SemiprimeD1StackRootSelectionAcquire.acquisitionStack,
      SemiprimeD1StackSourceSelectionAcquire.selectorStack,
      SemiprimeD1StackSourceSelectionAcquire.occurrenceStack,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl] at h <;> cases h <;> rfl
end RiemannGaussian.SemiprimeD1PackedRootFactoryInputs
