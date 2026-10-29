/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTraceBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOperationBounds
/-! # Raw occurrence, endpoint and packet counts/bytes come from actual input tapes
No decoded count, field length, classification or recursive-child runtime is
supplied. The mathematical record views are bounded directly by their actual
retained framed source words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload)
end P
namespace K
export SemiprimeD1StackChildGroupFactoryEndpointKeys (pairs placements)
end K
namespace R
export SemiprimeD1StackChildGroupFactoryEndpointLoop (Row)
end R
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (side selected oldPoints)
end Code
namespace Op
export SemiprimeD1StackChildGroupFactoryOperationBounds (endpointBytes)
end Op
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All seven acquired original occurrence/placement fields, plus a positive byte. -/
def fieldBytes (f:P.Fields):Nat:=f.owner.length+f.factor.length+f.source.length+f.padding.length+
  f.packet.length+f.slot.length+f.edge.length+1
/-- The actual pair/placement record tapes pay every acquired field byte. -/
theorem field_le_tapes (fields:List P.Fields) (f:P.Fields) (hf:f∈fields):
    fieldBytes f≤(K.pairs fields).length+(K.placements fields).length:=by
  induction fields with
  | nil=>simp only [List.not_mem_nil] at hf
  | cons g gs ih=>
    simp only [List.mem_cons] at hf
    rcases hf with rfl|hf
    · simp only [K.pairs,K.placements,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,
        P.payload,List.length_nil,fieldBytes]
      omega
    · have ht:=ih hf
      simp only [K.pairs,K.placements,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
/-- Every actual paired source row has a physically present TRUE/tag/frame footprint. -/
theorem fields_count (fields:List P.Fields):fields.length≤(K.pairs fields).length:=by
  induction fields with
  | nil=>simp only [List.length_nil,K.pairs,List.length_cons];omega
  | cons f fs ih=>
    simp only [List.length_cons,K.pairs,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
/-- All actual source packets are charged even when their raw word is empty. -/
theorem packet_count (packets:List (List Bool)):packets.length≤(vectorBits packets).length:=by
  induction packets with
  | nil=>simp only [List.length_nil,vectorBits,List.length_cons];omega
  | cons p ps ih=>
    simp only [List.length_cons,vectorBits,SemiprimeSourceHistogramKeyBits.frame_length]
    omega
/-- Any actual raw packet word has a paid physical representation in the retained source tape. -/
theorem packet_word (packets:List (List Bool)) (packet:List Bool) (hp:packet∈packets):
    packet.length≤(vectorBits packets).length:=by
  induction packets with
  | nil=>simp only [List.not_mem_nil] at hp
  | cons p ps ih=>
    simp only [List.mem_cons] at hp
    rcases hp with rfl|hp
    · simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length];omega
    · have ht:=ih hp
      simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length];omega
/-- An emitted side contains only actual source fields and its one literal side bit. -/
theorem side_bytes (owner:Bool) (r:R.Row):Op.endpointBytes (Code.side owner r)≤fieldBytes r.fields+2:=by
  cases owner <;> simp only [Code.side,Op.endpointBytes,fieldBytes,Bool.false_eq_true,ite_false,ite_true,
    List.length_cons,List.length_nil] <;> omega
/-- Computed activation may retain both/one/neither endpoint; no branch creates more than two. -/
theorem selected_count (rows:List R.Row):(Code.selected rows).length≤2*rows.length:=by
  induction rows with
  | nil=>simp only [Code.selected,List.length_nil,Nat.mul_zero,le_refl]
  | cons r rs ih=>
    cases ho:r.ownerFlag <;> cases hf:r.factorFlag <;>
      simp only [Code.selected,ho,hf,Bool.false_eq_true,ite_false,ite_true,List.length_append,
        List.length_cons,List.length_nil] <;> omega
/-- Every actual selected endpoint inherits its raw-byte bound from a real original row. -/
theorem selected_bytes (rows:List R.Row) (cap:Nat) (hc:∀r∈rows,fieldBytes r.fields≤cap):
    ∀e∈Code.selected rows,Op.endpointBytes e≤cap+2:=by
  induction rows with
  | nil=>intro e he;simp only [Code.selected,List.not_mem_nil] at he
  | cons r rs ih=>
    have hh:=hc r List.mem_cons_self
    have ht:=ih (fun q h=>hc q (List.mem_cons_of_mem r h))
    intro e he
    cases ho:r.ownerFlag <;> cases hf:r.factorFlag
    all_goals simp only [Code.selected,ho,hf,Bool.false_eq_true,ite_false,ite_true,
      List.nil_append,List.cons_append,List.mem_cons] at he
    · exact ht e he
    · rcases he with rfl|he
      · exact (side_bytes false r).trans (Nat.add_le_add_right hh 2)
      · exact ht e he
    · rcases he with rfl|he
      · exact (side_bytes true r).trans (Nat.add_le_add_right hh 2)
      · exact ht e he
    · rcases he with rfl|rfl|he
      · exact (side_bytes true r).trans (Nat.add_le_add_right hh 2)
      · exact (side_bytes false r).trans (Nat.add_le_add_right hh 2)
      · exact ht e he
/-- Both old endpoints are retained literally regardless of activation, so old port count is exactly twice original rows. -/
theorem old_count (rows:List R.Row):(Code.oldPoints rows).length=2*rows.length:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih=>
    simp only [Code.oldPoints,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ih ⊢
    omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds
