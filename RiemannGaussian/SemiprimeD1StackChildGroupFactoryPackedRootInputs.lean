/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeInputs
import RiemannGaussian.SemiprimeD1PackedRootFactoryInputs
/-! # Actual original-N reached root cache supplies every child-factory operand
All143 retained words are projected at their actual fixed original root roles.
The marked network's NEW table tape is separate; these cache operands contain
only original topology/ID metadata. This proves the prepared handoff's bytes;
a literal enclosing Root2505-to-factory call/context installation is separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPackedRootInputs
open SemiprimeBitArithmetic (bitValue)
attribute [local irreducible] SemiprimeD1PacketReplayOriginal.acquire SemiprimeD1IncidenceSearch.run
namespace P
export SemiprimeD1StackPackedRootInputEncoding (done)
end P
namespace Root
export SemiprimeD1PackedRootFactoryInputs (selector occurrence inventory selector_original occurrence_original)
end Root
namespace A
export SemiprimeD1StackRootSelectionAcquireEncoding (dimension)
end A
namespace Net
export SemiprimeD1StackMarkedRootRecordsNetwork (network)
end Net
namespace R
export SemiprimeD1StackChildGroupFactoryReady (Header sourceInputs)
end R
namespace Meaning
export SemiprimeD1StackChildGroupFactoryNativeInputs (CacheMeaning valid_original count_original)
end Meaning
/-- Complete actual63-selector physical cache, not a decoded label supplier. -/
def selectorWords (bits:List Bool) (hN:0<bitValue bits) (k:SemiprimeD1StackChildGroupFactoryReady.S.Stack):List Bool:=
  (P.done bits hN).data (Root.selector k)
/-- Complete actual21-occurrence physical cache, preserving original factor/local-port order. -/
def occurrenceWords (bits:List Bool) (hN:0<bitValue bits) (k:SemiprimeD1StackChildGroupFactoryReady.P.Stack):List Bool:=
  (P.done bits hN).data (Root.occurrence k)
/-- Complete actual59-inventory physical cache, including retained stale maps and shadows. -/
def inventoryWords (bits:List Bool) (hN:0<bitValue bits) (k:SemiprimeD1StackChildGroupFactoryReady.I.Stack):List Bool:=
  (P.done bits hN).data (Root.inventory k)
/-- SAME original reached root provides all seven operands, with NEW-network topology lineage internally discharged. -/
theorem cache_original (bits:List Bool) (hN:0<bitValue bits):
    Meaning.CacheMeaning (Net.network (bitValue bits) hN) (A.dimension bits)
      (selectorWords bits hN) (occurrenceWords bits hN) (inventoryWords bits hN):=by
  constructor
  · intro k;exact Root.selector_original bits hN k
  · intro k;exact Root.occurrence_original bits hN k
  · change (P.done bits hN).data SemiprimeD1PackedRootCaches.placements=_
    rw [SemiprimeD1PackedRootCaches.placements_original]
    rfl
  · change (P.done bits hN).data SemiprimeD1PackedRootCaches.packets=_
    rw [SemiprimeD1PackedRootCaches.packets_original]
    rfl
/-- Every parser, palette, count, physical zip/domain obligation follows from actual root bytes. -/
theorem valid_original (bits:List Bool) (hN:0<bitValue bits) (header:R.Header)
    (q:Fin (A.dimension bits)) (hq:header.colourIndex=List.replicate q.val true):
    SemiprimeD1StackChildGroupFactoryTraceBounds.Valid
      (R.sourceInputs (selectorWords bits hN) (occurrenceWords bits hN) (inventoryWords bits hN) header)
      (A.dimension bits) q.val
      (SemiprimeD1StackChildGroupFactoryNativeActivation.originalIDs
        (Net.network (bitValue bits) hN).leftCount (Net.network (bitValue bits) hN).rows.length (A.dimension bits)
        (SemiprimeD1TensorNetwork.arity (Net.network (bitValue bits) hN).rows)
        (SemiprimeD1TensorNetwork.owner (Net.network (bitValue bits) hN).rows))
      (SemiprimeD1StackChildGroupFactoryNativeFields.source
        (Net.network (bitValue bits) hN).leftCount (Net.network (bitValue bits) hN).rows.length (A.dimension bits)
        (SemiprimeD1TensorNetwork.arity (Net.network (bitValue bits) hN).rows)
        (SemiprimeD1TensorNetwork.owner (Net.network (bitValue bits) hN).rows)).state.packets
      (SemiprimeD1StackChildGroupFactoryNativeFields.fields
        (Net.network (bitValue bits) hN).leftCount (Net.network (bitValue bits) hN).rows.length (A.dimension bits)
        (SemiprimeD1TensorNetwork.arity (Net.network (bitValue bits) hN).rows)
        (SemiprimeD1TensorNetwork.owner (Net.network (bitValue bits) hN).rows)):=
  Meaning.valid_original _ _ _ _ _ _ _ (cache_original bits hN) hq
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPackedRootInputs
