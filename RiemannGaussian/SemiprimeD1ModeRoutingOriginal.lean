/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingTile

/-! # Original acquired packet routing, without mode ownership advice
Runtime callers pass their retained Replay/OriginalModes source to fromReplay.
The original-input theorems below internally derive canonical class fields and
real-row reconstruction from the actual sparse acquisition.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace RiemannGaussian.SemiprimeD1ModeRoutingOriginal
open SemiprimeD1ModeRoutingBits SemiprimeD1ModeRoutingColours SemiprimeD1ModeRoutingWireColours
open SemiprimeD1OrientationInverse SemiprimeD1OrientationComplete SemiprimeD1OrientationPalette
open SemiprimeD1PacketInventory SemiprimeBitArithmetic

/-- Every actual observed packet has its internally derived compact finite class. -/
theorem observed_class (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length) :
    ∃ lows highs : List (List Bool),∃ high : List Bool,
      Canonical lows highs ∧ Allowed r lows ∧ Allowed r highs ∧
      lows.length=a ∧ highs.length=a ∧ SemiprimeSourceCompactBits.Compact high ∧
      (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets[packet.val]=
        packetKey lows highs high := by
  obtain ⟨left,right,j,hl,hr,hla,hra,hj,_,hk⟩ :=
    SemiprimeD1PacketReplayOriginal.observed_generated n F r a inputArity inputOwner _
      (List.getElem_mem packet.isLt)
  obtain ⟨hc,hlo,hhi,hlen⟩ := SemiprimeD1OrientationForward.sorted_properties r left right (hl.trans hr.symm) hla hra
  refine ⟨_,_,_,hc,hlo,hhi,hlen.trans hl,?_,SemiprimeD1OrientationForward.high_compact left right j hj,?_⟩
  · exact (canonical_length hc).symm.trans (hlen.trans hl)
  · exact hk.symm.trans (SemiprimeD1OrientationForward.key_decomposition left right j (hl.trans hr.symm))

/-- Proof-side name of the actual physical original row reader, with no Word getter. -/
def actualRows {n F a : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (out : Placement) :=
  SemiprimeD1PacketRows.read source.padding.source.selection.cache.rows.source.dictionary a out.source

/-- Every real acquired placement reconstructs precisely its actual selected rows. -/
theorem real_roundtrip (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (out : Placement)
    (ho : out∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements) :
    let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
    (recover out.packet out.slot).left=(actualRows source out).left ∧
    (recover out.packet out.slot).right=(actualRows source out).right := by
  have hm : out.source∈(SemiprimeD1IncidenceAcquisition.acquire n F r a inputArity inputOwner).keys := by
    rw [←SemiprimeD1PacketReplayOriginal.sources n F r a inputArity inputOwner]
    exact List.mem_map.mpr ⟨out,ho,rfl⟩
  have hr := SemiprimeD1PacketReplayOriginal.row_properties n F r a inputArity inputOwner out.source hm
  have hc := replay_padding_compact _ _ _ _ SemiprimeSourceHistogramTrie.empty_compact out ho
  have hp := replay_oriented _ _ _ _ out ho
  simp only [SemiprimeD1PacketPadding.acquire_source] at hp
  have ht := roundtrip_value _ _ out.padding (hr.1.trans hr.2.1.symm) hc
  rw [←hp.1,←hp.2.1] at ht
  exact ⟨congrArg Prod.fst ht,congrArg (fun x => x.2.1) ht⟩

/-- Retaining the parent report changes no physical routing tile bit. -/
theorem fromReplay_bit {n F a : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity)
    (packet : Fin source.state.packets.length) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (fromReplay source packet i tile).bit=(SemiprimeD1ModeRoutingBits.acquire source.state.packets[packet.val] a i tile).bit := by
  simp only [fromReplay,SemiprimeSourceCompactBits.copy_bits]

/-- Every real column in the original arithmetic tile belongs to its acquired source. -/
theorem column_source_original (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (out : Placement)
    (ho : out∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements)
    (hk : out.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets[packet.val])
    (ht : bitValue out.slot%2^(i.val+1)=tile.val) :
    let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
    (((actualRows source out).right[i.val]?).getD [])=(fromReplay source packet i tile).source := by
  obtain ⟨lows,highs,high,hc,_,_,hl,hh,_,hkey⟩ := observed_class n F r a inputArity inputOwner packet
  have hs := (SemiprimeD1PacketReplayOriginal.placement_valid n F r a inputArity inputOwner out ho).2
  have hb := SemiprimeD1ModeRoutingTile.tile_bit a i tile out.slot ht
  rw [←SemiprimeD1ModeRoutingTile.acquire_bit (packetKey lows highs high)] at hb
  have hg := column_source a lows highs high hc hl hh i tile out.slot hs hb
  rw [←hkey] at hg
  have hr := (real_roundtrip n F r a inputArity inputOwner out ho).2
  rw [hk] at hr
  rw [hr] at hg
  dsimp only
  rw [(fromReplay_data _ _ _ _).1]
  exact hg

/-- Every crossing real row has exactly the other acquired target colour and the
same ith physical slot bit as the column tile. No mode owner is assumed. -/
theorem row_target_original (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (out : Placement)
    (ho : out∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements)
    (hk : out.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets[packet.val])
    (hx : (((actualRows (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) out).left[i.val]?).getD [])≠
      (fromReplay (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) packet i tile).source) :
    let source := SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner
    (out.slot[i.val]?).getD false=(fromReplay source packet i tile).bit ∧
    (((actualRows source out).left[i.val]?).getD [])=(fromReplay source packet i tile).target := by
  obtain ⟨lows,highs,high,hc,_,_,hl,hh,_,hkey⟩ := observed_class n F r a inputArity inputOwner packet
  have hs := (SemiprimeD1PacketReplayOriginal.placement_valid n F r a inputArity inputOwner out ho).2
  have hr := (real_roundtrip n F r a inputArity inputOwner out ho).1
  rw [hk] at hr
  have hx' : ((recover (packetKey lows highs high) out.slot).left[i.val]?).getD []≠
      (SemiprimeD1ModeRoutingBits.acquire (packetKey lows highs high) a i tile).source := by
    rw [←hkey,hr]
    rw [(fromReplay_data _ _ _ _).1] at hx
    exact hx
  have hg := row_target a lows highs high hc hl hh i tile out.slot hs hx'
  rw [←hkey,hr] at hg
  dsimp only
  rw [fromReplay_bit,(fromReplay_data _ _ _ _).2]
  exact hg

/-- Canonical observed packets make the actual zero-slot parser succeed. -/
theorem route_valid (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (fromReplay (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) packet i tile).valid=true := by
  obtain ⟨lows,highs,high,hc,_,_,hl,_,hh,hkey⟩ := observed_class n F r a inputArity inputOwner packet
  have hv := (all_slots lows highs high (List.replicate a false) hc hh (by simp [hl])).2.1
  simp only [fromReplay,SemiprimeSourceCompactBits.copy_bits,SemiprimeD1ModeRoutingBits.acquire,zeros_bits]
  rw [hkey]
  exact hv

/-- Crossing row arithmetic bits are the actual original tile bits. -/
theorem crossing_testBit (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) (out : Placement)
    (ho : out∈(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).placements)
    (hk : out.packet=(SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets[packet.val])
    (hx : (((actualRows (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) out).left[i.val]?).getD [])≠
      (fromReplay (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) packet i tile).source) :
    (bitValue out.slot).testBit i.val=tile.val.testBit i.val := by
  have h := (row_target_original n F r a inputArity inputOwner packet i tile out ho hk hx).1
  rw [fromReplay_bit] at h
  simp only [SemiprimeD1ModeRoutingBits.acquire] at h
  rw [SemiprimeD1ModeRoutingTile.readBit_testBit] at h
  rw [SemiprimeSourceHistogramPortKeys.encodeKey_value] at h
  rw [←SemiprimeD1ModeRoutingTile.readBit_testBit out.slot i.val]
  rw [readBit_value]
  exact h

/-- Both acquired routing colours are compact members of the original palette. -/
theorem route_palette (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n)
    (packet : Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner).state.packets.length)
    (i : Fin a) (tile : Fin (2^(i.val+1))) :
    let route := fromReplay (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) packet i tile
    SemiprimeSourceCompactBits.Compact route.source ∧ bitValue route.source < r ∧
    SemiprimeSourceCompactBits.Compact route.target ∧ bitValue route.target < r := by
  obtain ⟨lows,highs,high,_,hlo,hhi,hl,hh,_,hkey⟩ := observed_class n F r a inputArity inputOwner packet
  have hil : i.val < lows.length := by omega
  have hih : i.val < highs.length := by omega
  have hlo' := hlo _ (List.getElem_mem hil)
  have hhi' := hhi _ (List.getElem_mem hih)
  have fields := acquire_fields a lows highs high hl hh i tile
  have colours := acquire_colours (packetKey lows highs high) a i tile
  dsimp only
  rw [(fromReplay_data _ _ _ _).1,(fromReplay_data _ _ _ _).2,hkey,
    colours.1,colours.2,fields.1,fields.2]
  simp only [List.getElem?_eq_getElem hil,List.getElem?_eq_getElem hih,Option.getD_some]
  rcases hlo' with ⟨hcl,hvl⟩
  rcases hhi' with ⟨hch,hvh⟩
  split <;> simp_all only [ite_true,and_self]

end RiemannGaussian.SemiprimeD1ModeRoutingOriginal
