/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBounds
import RiemannGaussian.SemiprimeD1StackPacketInventoryMeaning
/-! # Entire original sparse packet inventory from actual acquired input bytes
The parent selected-key and alphabet sources supply two stopped words. This
prepared consumer executes no selector, original getter, report or callback.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryOriginal
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryEncoding
open SemiprimeD1StackPacketInventoryBounds SemiprimeD1StackPacketInventoryMeaning
open SemiprimeD1TensorTapeCodec (vectorBits)
attribute [local irreducible] SemiprimeD1IncidenceSearch.run SemiprimeD1IncidenceAcquisition.acquire
/-- Entire original actual selected-key stream, including all repeated occurrences and factor-major order. -/
def originalKeys (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):List (List Bool):=
  (SemiprimeD1IncidenceAcquisition.acquire n F 64 a arity owner).keys
/-- Original key membership is proved from the same selected IDs, with no external row-validity or menu advice. -/
theorem original_valid (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    ValidKeys a (originalKeys n F a arity owner):=by
  intro raw hr
  unfold originalKeys at hr
  rw [SemiprimeD1IncidenceAcquisition.keys_original] at hr
  obtain ⟨p,_,rfl⟩:=List.mem_map.mp hr
  exact SemiprimeD1StackPacketRowsOriginal.selected_key_lineage n F a arity owner p
/-- Generic exact physical output projection precedes instantiation of any large original graph. -/
theorem output_bytes (keys cat:List Bool) (s:Summary):
    (done keys cat s).data output=vectorBits (s.placements.map placementBytes):=rfl
/-- All packet discovery bytes are retained in exact newest-first original order. -/
theorem packet_bytes (keys cat:List Bool) (s:Summary):
    (done keys cat s).data packets=vectorBits s.packets:=rfl
/-- Both actual original input words remain unchanged. -/
theorem inputs_retained (keys cat:List Bool) (s:Summary):
    (done keys cat s).data source=keys ∧ (done keys cat s).data catalogue=cat:=⟨rfl,rfl⟩
/-- The retained original selected acquisition uses the same actual original row dictionary. -/
theorem acquired_dictionary (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    (SemiprimeD1IncidenceAcquisition.acquire n F 64 a arity owner).selection.cache.rows.source.dictionary=
      SemiprimeSourceHistogramRows.acquire 64 a:=by
  unfold SemiprimeD1IncidenceAcquisition.acquire
  rfl
/-- Native original placements are exactly the chronological replay from physically empty classes/seen/slots. -/
theorem placements_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    (acquire a (originalKeys n F a arity owner)).placements=
      (SemiprimeD1PacketInventory.acquire n F 64 a arity owner).placements:=by
  unfold SemiprimeD1PacketInventory.acquire
  dsimp only
  rw [acquired_dictionary]
  exact (acquire_original a (originalKeys n F a arity owner)
    (SemiprimeD1IncidenceAcquisition.acquire n F 64 a arity owner).state.clock).1
/-- Every final class, seen and slot read, packet discovery order and positive edge word has exact old meaning. -/
theorem state_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    Rel (acquire a (originalKeys n F a arity owner))
      (SemiprimeD1PacketInventory.acquire n F 64 a arity owner).state:=by
  unfold SemiprimeD1PacketInventory.acquire
  dsimp only
  rw [acquired_dictionary]
  exact (acquire_original a (originalKeys n F a arity owner)
    (SemiprimeD1IncidenceAcquisition.acquire n F 64 a arity owner).state.clock).2
/-- One actual fixed59-role source for the entire original family, with exact six-field placements and packet discovery vector. -/
theorem source_run_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    ∃t ≤ byteBound (vectorBits (originalKeys n F a arity owner)) (alphabet a),
      SemiprimeD1StackCalls.run program t (initial (vectorBits (originalKeys n F a arity owner)) (alphabet a))=
        some (done (vectorBits (originalKeys n F a arity owner)) (alphabet a)
          (acquire a (originalKeys n F a arity owner))) ∧
      (done (vectorBits (originalKeys n F a arity owner)) (alphabet a)
        (acquire a (originalKeys n F a arity owner))).data output=
        vectorBits ((SemiprimeD1PacketInventory.acquire n F 64 a arity owner).placements.map placementBytes) ∧
      (done (vectorBits (originalKeys n F a arity owner)) (alphabet a)
        (acquire a (originalKeys n F a arity owner))).data packets=
        vectorBits (SemiprimeD1PacketInventory.acquire n F 64 a arity owner).state.packets:=by
  obtain ⟨t,ht,hr⟩:=source_run_keys a (originalKeys n F a arity owner) (original_valid n F a arity owner)
  refine ⟨t,ht,hr,?_,?_⟩
  · rw [output_bytes,placements_original]
  · rw [packet_bytes,(state_original n F a arity owner).packets]
end RiemannGaussian.SemiprimeD1StackPacketInventoryOriginal
