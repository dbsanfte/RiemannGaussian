/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeActivation
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
import RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
import RiemannGaussian.SemiprimeD1ChildPullbackBudget
/-! # Exact physically parsed fields from original occurrence and placement tapes
The proof interpretation is derived from the real original two-source zip. Its
length, validity, key ranges and byte layouts are proved from the original
acquired metadata; no decoded field list or zip/permutation is a runtime input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeFields
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields payload)
end Parse
namespace K
export SemiprimeD1StackChildGroupFactoryEndpointKeys (pairs placements)
end K
namespace Key
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value)
end Key
namespace Native
export SemiprimeD1PacketInventory (Placement)
export SemiprimeD1PacketReplayOriginal (acquire placement_valid)
end Native
/-- Exactly the seven actual words supplied by the two real parsers. -/
def ofPair (keys:List Bool×List Bool) (out:Native.Placement):Parse.Fields:=
  ⟨keys.1,keys.2,out.source,out.padding,out.packet,out.slot,out.edge⟩
/-- No first-source record is dropped when the original acquired lengths match. -/
theorem pairs_zip (keys:List (List Bool×List Bool)) (placements:List Native.Placement)
    (hl:keys.length=placements.length):
    K.pairs ((keys.zip placements).map (fun p=>ofPair p.1 p.2))=
      SemiprimeD1StackOwnerLookup.records keys []:=by
  induction keys generalizing placements with
  | nil=>cases placements <;> simp_all [K.pairs,SemiprimeD1StackOwnerLookup.records]
  | cons key keys ih=>
    cases placements with
    | nil=>simp only [List.length_cons,List.length_nil] at hl;omega
    | cons out outs=>
      have ht:keys.length=outs.length:=by simp only [List.length_cons] at hl;omega
      change true::SemiprimeSourceHistogramKeyBits.frame key.1
        (SemiprimeSourceHistogramKeyBits.frame key.2 (K.pairs ((keys.zip outs).map (fun p=>ofPair p.1 p.2))))=_
      rw [ih outs ht]
      rfl
/-- No second-source byte is invented: every real valid placement has its exact six-field payload. -/
theorem placements_zip (keys:List (List Bool×List Bool)) (placements:List Native.Placement)
    (hl:keys.length=placements.length) (hv:∀p∈placements,p.valid=true):
    K.placements ((keys.zip placements).map (fun p=>ofPair p.1 p.2))=
      SemiprimeD1TensorTapeCodec.vectorBits (placements.map SemiprimeD1StackPacketInventoryEncoding.placementBytes):=by
  induction keys generalizing placements with
  | nil=>cases placements <;> simp_all [K.placements,SemiprimeD1TensorTapeCodec.vectorBits]
  | cons key keys ih=>
    cases placements with
    | nil=>simp only [List.length_cons,List.length_nil] at hl;omega
    | cons out outs=>
      have ht:keys.length=outs.length:=by simp only [List.length_cons] at hl;omega
      have hvalid:=hv out List.mem_cons_self
      have hrest:=ih outs ht (fun p hp=>hv p (List.mem_cons_of_mem out hp))
      have hbytes:Parse.payload (ofPair key out)=SemiprimeD1StackPacketInventoryEncoding.placementBytes out:=by
        simp only [ofPair,Parse.payload,SemiprimeD1StackPacketInventoryEncoding.placementBytes,hvalid]
      change true::SemiprimeSourceHistogramKeyBits.frame (Parse.payload (ofPair key out))
        (K.placements ((keys.zip outs).map (fun p=>ofPair p.1 p.2)))=_
      rw [hbytes,hrest]
      rfl
/-- Original acquired source, reused only as erased mathematical notation. -/
def source (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):=
  Native.acquire n F 64 a arity owner
/-- Exact already acquired original ordered key-pair list. -/
def keys (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):=
  SemiprimeD1StackSourceIncidenceSelectMeaning.originalKeys n F a arity owner
/-- Actual seven-field interpretation of the two physical source tapes. -/
def fields (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):List Parse.Fields:=
  ((keys n F a arity owner).zip (source n F a arity owner).placements).map (fun p=>ofPair p.1 p.2)
/-- Original source keys and real replay placements have the SAME derived original occurrence count. -/
theorem lengths (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    (keys n F a arity owner).length=(source n F a arity owner).placements.length:=by
  have hp:=SemiprimeD1ChildPullbackBudget.placements_length n F 64 a arity owner
  have hm:=(SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
  dsimp only [keys,SemiprimeD1StackSourceIncidenceSelectMeaning.originalKeys]
  rw [List.length_map,hm]
  exact hp.symm
/-- First actual input tape is exactly the full original compact pair tape, in original order. -/
theorem pairs_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    K.pairs (fields n F a arity owner)=SemiprimeD1StackOwnerLookup.records (keys n F a arity owner) []:=
  pairs_zip _ _ (lengths n F a arity owner)
/-- Second actual input tape is exactly the real acquired placements, with validity derived internally. -/
theorem placements_original (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    K.placements (fields n F a arity owner)=SemiprimeD1TensorTapeCodec.vectorBits
      ((source n F a arity owner).placements.map SemiprimeD1StackPacketInventoryEncoding.placementBytes):=
  placements_zip _ _ (lengths n F a arity owner)
    (fun p hp=>(Native.placement_valid n F 64 a arity owner p hp).1)
/-- Every parsed original owner/factor key lies in the original combined vertex namespace. -/
theorem domains (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n):
    ∀f∈fields n F a arity owner,SemiprimeBitArithmetic.bitValue f.owner<n+F ∧
      SemiprimeBitArithmetic.bitValue f.factor<n+F:=by
  intro f hf
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hf
  have hkey:p.1∈keys n F a arity owner:=(List.of_mem_zip hp).1
  exact SemiprimeD1StackSourceIncidenceSelectOccurrences.original_key_ranges n F a arity owner p.1 hkey
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeFields
