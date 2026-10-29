/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPacketInventoryExecution
import RiemannGaussian.SemiprimeD1PacketReplayOriginal
/-! # Exact original padding/replay meaning of the actually acquired inventory
Native report clocks are used only as erased semantic indices. No equality of
reports or runtime clocks is asserted; the real source has its own paid clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPacketInventoryMeaning
open SemiprimeD1StackRootPacketInventory SemiprimeD1StackRootPacketInventoryEncoding
namespace IE
export SemiprimeD1StackPacketInventoryEncoding (acquire placementBytes)
end IE
namespace IM
export SemiprimeD1StackPacketInventoryMeaning (Rel acquire_original)
end IM
namespace IOld
export SemiprimeD1StackPacketInventoryOriginal (originalKeys acquired_dictionary)
end IOld
namespace Native
export SemiprimeD1PacketReplayOriginal (acquire)
end Native
/-- Actual original padding retained exactly the same physically acquired alphabet dictionary. -/
theorem padding_dictionary (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    (SemiprimeD1PacketPadding.acquire net.leftCount net.rows.length 64 a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).source.selection.cache.rows.source.dictionary=
        SemiprimeSourceHistogramRows.acquire 64 a:=by
  exact IOld.acquired_dictionary net.leftCount net.rows.length a
    (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)
/-- Every actual raw map/packet/edge field has exact original padding-then-replay semantics, regardless of the old report clock. -/
theorem generic_state (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    IM.Rel (IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)))
      (Native.acquire net.leftCount net.rows.length 64 a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).state:=by
  unfold SemiprimeD1PacketReplayOriginal.acquire
  dsimp only
  rw [padding_dictionary]
  exact (IM.acquire_original a _ _).2
/-- Exact chronological placements use the same real OLD class indices, byte signs/slots and positive occurrence words. -/
theorem generic_placements (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    (IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows))).placements=
      (Native.acquire net.leftCount net.rows.length 64 a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).placements:=by
  unfold SemiprimeD1PacketReplayOriginal.acquire
  dsimp only
  rw [padding_dictionary]
  exact (IM.acquire_original a _ _).1
/-- Generic whole-bank packet projection precedes original-N instantiation. -/
theorem generic_packets (root:R.Stack→List Bool) (net:SemiprimeD1TensorNetwork.Network) (a:Nat):
    data root (SemiprimeD1StackPacketInventoryEncoding.done
      (SemiprimeD1TensorTapeCodec.vectorBits (IOld.originalKeys net.leftCount net.rows.length a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)))
      (SemiprimeD1StackPacketInventoryEncoding.alphabet a)
      (IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
        (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)))).data packets=
        SemiprimeD1TensorTapeCodec.vectorBits
          (Native.acquire net.leftCount net.rows.length 64 a
            (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows)).state.packets:=by
  change SemiprimeD1TensorTapeCodec.vectorBits
    (IE.acquire a (IOld.originalKeys net.leftCount net.rows.length a
      (SemiprimeD1TensorNetwork.arity net.rows) (SemiprimeD1TensorNetwork.owner net.rows))).packets=_
  rw [(generic_state net a).packets]
end RiemannGaussian.SemiprimeD1StackRootPacketInventoryMeaning
