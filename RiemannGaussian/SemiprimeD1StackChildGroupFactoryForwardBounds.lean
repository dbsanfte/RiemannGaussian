/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationCapacities
/-! # Whole actual activation/forward-endpoint prefix has one fixed quartic clock
All classification and map bytes come from the physical acquired ID dictionary;
source fields/counts are charged to the same thirteen actual input words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBounds
open SemiprimeD1StackChildGroupFactory
namespace F
export SemiprimeD1StackChildGroupFactoryForwardSource (activation rows timeBound)
end F
namespace Raw
export SemiprimeD1StackChildGroupFactoryAcquisitionByteBounds (fieldBytes field_le_tapes fields_count)
end Raw
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
namespace Size
export SemiprimeD1StackChildGroupFactoryTraceBounds (inputBytes)
export SemiprimeD1StackChildGroupFactoryActivationCapacities (capacity inputSize source_timeBound_le)
end Size
namespace K
export SemiprimeD1StackChildGroupFactoryEndpointKeys (pairs placements row pairs_rows placements_rows rows_valid)
end K
/-- A fixed paid common count/byte allowance, never a runtime operand. -/
def capacity (i:Inputs):Nat:=8*(Size.inputBytes i+1)
/-- Entire same-program prefix clock is quartic in the actual thirteen physical input bytes. -/
theorem timeBound_le (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List P.Fields)
    (hids:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (he:i.environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hc:i.catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a)
    (hi:i.colourIndex=List.replicate coordinate true)
    (hlen:ids.length=i.owners.length+i.factors.length)
    (hpairs:i.occurrences=K.pairs fields) (hplacements:i.placements=K.placements fields)
    (hdom:∀f∈fields,SemiprimeBitArithmetic.bitValue f.owner < ids.length ∧
      SemiprimeBitArithmetic.bitValue f.factor < ids.length):
    F.timeBound i a coordinate ids fields≤1000000000*(capacity i+1)^4:=by
  let S:=capacity i
  have hs:Size.inputBytes i≤S:=by dsimp only [S,capacity];omega
  have hid:ids.length≤S:=by rw [hlen];dsimp only [S,capacity,Size.inputBytes];omega
  have hp:(K.pairs fields).length+(K.placements fields).length≤S:=by
    rw [←hpairs,←hplacements]
    dsimp only [S,capacity,Size.inputBytes];omega
  have hfields:∀f∈fields,Raw.fieldBytes f≤S:=fun f hf=>(Raw.field_le_tapes fields f hf).trans hp
  have hn:fields.length≤S:=(Raw.fields_count fields).trans (by omega)
  let ar:=F.activation a ids
  let er:=F.rows i a coordinate ids fields
  let entries:=SemiprimeD1StackChildGroupFactoryActivationMap.entries i coordinate [] ar
  have hal:ar.length=ids.length:=by
    simp only [ar,F.activation,SemiprimeD1StackChildGroupFactoryActivationMeaning.plan_length,List.length_reverse]
  have hem:i.environment=SemiprimeD1StackOwnerLookup.records (SemiprimeD1StackSourceEnvironmentEncoding.prefixRows ids) []:=he
  have hcm:i.catalogue=SemiprimeD1StackOwnerLookup.records
      (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) []:=
    hc.trans (SemiprimeD1StackPacketRowsMeaning.catalogue_original a).symm
  have hv:=SemiprimeD1StackChildGroupFactoryActivationMeaning.plan_valid_all a ids hids
  have hat:=Size.source_timeBound_le i coordinate (SemiprimeD1StackSourceEnvironmentEncoding.prefixRows ids)
    (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) ar hem hcm hi
    (by simpa only [hal] using hlen) hv
  have hcapacity:Size.capacity i≤S:=by dsimp only [Size.capacity,Size.inputSize,S,capacity,Size.inputBytes];omega
  have ham:SemiprimeD1StackChildGroupFactoryActivationSource.timeBound i coordinate
      (SemiprimeD1StackSourceEnvironmentEncoding.prefixRows ids)
      (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) ar≤200000000*S^3:=
    hat.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcapacity 3))
  have hmap:(SemiprimeD1StackOwnerLookup.records entries []).length≤10*(S+1)^2:=by
    have h:=SemiprimeD1StackChildGroupFactoryActivationMapBounds.zero_records_length i coordinate ar
    change (SemiprimeD1StackOwnerLookup.records entries []).length≤_ at h
    rw [hal] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega:ids.length+1≤S+1) 2))
  have her:∀r∈er,Raw.fieldBytes r.fields≤S:=by
    intro r hr
    obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hr
    exact hfields f hf
  have hvalid:SemiprimeD1StackChildGroupFactoryEndpointLoop.Valid entries er:=by
    apply K.rows_valid
    intro f hf
    simpa only [hal] using hdom f hf
  have hep:(SemiprimeD1StackChildGroupFactoryEndpointLoop.pairs er).length+
      (SemiprimeD1StackChildGroupFactoryEndpointLoop.placements er).length≤S:=by
    simpa only [er,F.rows,K.pairs_rows,K.placements_rows] using hp
  have hen:er.length≤S:=by simpa only [er,F.rows,List.length_map] using hn
  have het:=SemiprimeD1StackChildGroupFactoryEndpointBounds.source_time entries er S her hvalid hen hep hmap
  change SemiprimeD1StackChildGroupFactoryActivationSource.timeBound i coordinate
      (SemiprimeD1StackSourceEnvironmentEncoding.prefixRows ids)
      (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) ar+
    SemiprimeD1StackChildGroupFactoryEndpointSource.timeBound entries er≤1000000000*(S+1)^4
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardBounds
