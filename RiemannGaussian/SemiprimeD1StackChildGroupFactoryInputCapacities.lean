/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBounds
/-! # One actual thirteen-input capacity bounds all acquired structural counts
This is a proof estimate only. No bound, count, key, mode or decoded record
enters the finite controller. All source high-zero padding is charged in its
literal tape lengths; original numeric N never enters this metadata domain.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputCapacities
open SemiprimeD1StackChildGroupFactory
namespace V
export SemiprimeD1StackChildGroupFactoryTraceBounds (Valid inputBytes)
end V
namespace S
export SemiprimeD1StackChildGroupFactoryForwardBounds (capacity)
end S
namespace F
export SemiprimeD1StackChildGroupFactoryForwardSource (rows)
export SemiprimeD1StackChildGroupFactoryForwardBucketsSource (endpoints)
end F
namespace Raw
export SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds
  (fieldBytes field_le_tapes fields_count packet_count packet_word selected_count selected_bytes old_count)
end Raw
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (oldPoints)
end Code
/-- The positive common byte capacity is fixed by the actual physical input lengths. -/
theorem capacity_pos (i:Inputs):1≤S.capacity i:=by dsimp only [S.capacity];omega
/-- Original owner/factor markers, including isolated vertices, are physically charged. -/
theorem vertices (i:Inputs):i.owners.length+i.factors.length≤S.capacity i:=by
  dsimp only [S.capacity,V.inputBytes];omega
/-- Every decoded occurrence field is charged by its two actual retained source tapes. -/
theorem field_bytes (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):∀f∈fields,Raw.fieldBytes f≤V.inputBytes i:=by
  intro f hf
  have h:=Raw.field_le_tapes fields f hf
  rw [←hv.pairs,←hv.placements] at h
  dsimp only [V.inputBytes]
  omega
/-- The actual paired source cannot encode more original occurrences than its physical tape bytes. -/
theorem occurrences (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):fields.length≤V.inputBytes i:=by
  have h:=Raw.fields_count fields
  rw [←hv.pairs] at h
  dsimp only [V.inputBytes];omega
/-- True computed endpoint count permits both sides and is paid before any packet duplication. -/
theorem endpoints_count (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):(F.endpoints i a coordinate ids fields).length≤S.capacity i:=by
  have h:=Raw.selected_count (F.rows i a coordinate ids fields)
  have hc:=occurrences i a coordinate ids packets fields hv
  simp only [F.rows,List.length_map] at h
  change (F.endpoints i a coordinate ids fields).length≤_ at h
  dsimp only [S.capacity]
  omega
/-- Every actually emitted endpoint preserves raw binary/source padding from real acquired fields. -/
theorem endpoint_bytes (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):∀e∈F.endpoints i a coordinate ids fields,
      SemiprimeD1StackChildGroupFactoryOperationBounds.endpointBytes e≤S.capacity i:=by
  have hc:∀r∈F.rows i a coordinate ids fields,Raw.fieldBytes r.fields≤V.inputBytes i:=by
    intro r hr
    obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hr
    exact field_bytes i a coordinate ids packets fields hv f hf
  have h:=Raw.selected_bytes (F.rows i a coordinate ids fields) (V.inputBytes i) hc
  intro e he
  have he':=h e he
  dsimp only [S.capacity];omega
/-- Every original old-side point remains present even if no activation side was selected. -/
theorem old_points (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):
    (Code.oldPoints (F.rows i a coordinate ids fields)).length≤S.capacity i:=by
  rw [Raw.old_count]
  have hc:=occurrences i a coordinate ids packets fields hv
  simp only [F.rows,List.length_map]
  dsimp only [S.capacity];omega
/-- Actual packet records, including empty/repeated raw words, are charged to their original vector. -/
theorem packets_count (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):packets.length≤S.capacity i:=by
  have h:=Raw.packet_count packets
  rw [←hv.packet_tape] at h
  dsimp only [S.capacity,V.inputBytes];omega
/-- Every retained raw packet word is physically present and paid; no literal-byte aliases are conflated. -/
theorem packet_bytes (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):∀packet∈packets,packet.length≤S.capacity i:=by
  intro packet hp
  have h:=Raw.packet_word packets packet hp
  rw [←hv.packet_tape] at h
  dsimp only [S.capacity,V.inputBytes];omega
/-- The one actual packet-vector copy is included in the same physical capacity. -/
theorem packet_tape (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:V.Valid i a coordinate ids packets fields):
    (SemiprimeD1TensorTapeCodec.vectorBits packets).length≤S.capacity i:=by
  rw [←hv.packet_tape]
  dsimp only [S.capacity,V.inputBytes];omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryInputCapacities
