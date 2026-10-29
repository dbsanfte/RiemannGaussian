/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointSource
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryEndpointKeys
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationOriginal
/-! # One actual thirteen-word source through original forward endpoint acquisition
All activation classifications are derived from the actual acquired complete
selected-ID environment/catalogue, then read by real numeric endpoint lookups.
Packet buckets, derived port order and the N/current-node caller remain later joins.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Act
export SemiprimeD1StackChildGroupFactoryActivationLoop (Row)
export SemiprimeD1StackChildGroupFactoryActivationMeaning (plan plan_length)
end Act
namespace ASource
export SemiprimeD1StackChildGroupFactoryActivationSource (result timeBound)
end ASource
namespace AMap
export SemiprimeD1StackChildGroupFactoryActivationMap (entries source_map)
end AMap
namespace Keys
export SemiprimeD1StackChildGroupFactoryEndpointKeys (row pairs placements pairs_rows placements_rows rows_valid)
end Keys
namespace End
export SemiprimeD1StackChildGroupFactoryEndpointSource (result timeBound source_trace)
end End
namespace Parse
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields cleanRoles)
end Parse
/-- Proof interpretation of the actually acquired all-vertex activation rows. -/
def activation (a:Nat) (ids:List (List Bool)):List Act.Row:=Act.plan a ids [] ids.reverse
/-- Endpoint classifications describe actual generated-map lookups; they are never physical input fields. -/
def rows (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):=
  fields.map (Keys.row i coordinate (activation a ids))
/-- Full actual115-word forward-catalogue endpoint, before the packet-copy instruction. -/
def result (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):Stack→List Bool:=
  End.result (ASource.result i coordinate (activation a ids)) (rows i a coordinate ids fields)
/-- Only clocks proved for these actual calls/copies/loops/reversals contribute. -/
def timeBound (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields):Nat:=
  ASource.timeBound i coordinate (SemiprimeD1StackSourceEnvironmentEncoding.prefixRows ids)
      (SemiprimeD1StackPacketRowsMeaning.originalEntries 64 a) (activation a ids)+
    End.timeBound (AMap.entries i coordinate [] (activation a ids)) (rows i a coordinate ids fields)
/-- Whole real entry from thirteen cache/header words through forward endpoints, with no supplied activation/key/permutation answer. -/
theorem source_trace (i:Inputs) (a coordinate:Nat) (ids:List (List Bool)) (fields:List Parse.Fields)
    (hids:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids)
    (he:i.environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids)
    (hc:i.catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a)
    (hi:i.colourIndex=List.replicate coordinate true)
    (hlen:ids.length=i.owners.length+i.factors.length)
    (hpairs:i.occurrences=Keys.pairs fields) (hplacements:i.placements=Keys.placements fields)
    (hdom:∀f∈fields,SemiprimeBitArithmetic.bitValue f.owner < ids.length ∧
      SemiprimeBitArithmetic.bitValue f.factor < ids.length):
    ∃t≤timeBound i a coordinate ids fields,
      Runs program t entry (input i) (.local 6 17) (result i a coordinate ids fields):=by
  obtain ⟨x,hx,h0,_⟩:=SemiprimeD1StackChildGroupFactoryActivationOriginal.source_original i a coordinate ids
    hids he hc hi hlen
  let first:=ASource.result i coordinate (activation a ids)
  let records:=AMap.entries i coordinate [] (activation a ids)
  let acquired:=rows i a coordinate ids fields
  have hpair:first (aux .occurrences)=SemiprimeD1StackChildGroupFactoryEndpointLoop.pairs acquired:=by
    change i.occurrences=SemiprimeD1StackChildGroupFactoryEndpointLoop.pairs acquired
    rw [show acquired=fields.map (Keys.row i coordinate (activation a ids)) from rfl,Keys.pairs_rows]
    exact hpairs
  have hplacement:first (aux .placements)=SemiprimeD1StackChildGroupFactoryEndpointLoop.placements acquired:=by
    change i.placements=SemiprimeD1StackChildGroupFactoryEndpointLoop.placements acquired
    rw [show acquired=fields.map (Keys.row i coordinate (activation a ids)) from rfl,Keys.placements_rows]
    exact hplacements
  have hfresh:∀k∈Parse.cleanRoles,first k=[]:=by
    simp [first,Parse.cleanRoles,ASource.result,
      SemiprimeD1StackChildGroupFactoryActivation.data,input,aux,field]
  have hmap:first (aux .activationMap)=SemiprimeD1StackOwnerLookup.records records []:=
    AMap.source_map i coordinate (activation a ids)
  have hvalid:SemiprimeD1StackChildGroupFactoryEndpointLoop.Valid records acquired:=by
    apply Keys.rows_valid
    intro f hf
    simpa only [activation,Act.plan_length,List.length_reverse] using hdom f hf
  have h1:=End.source_trace records acquired first hpair hplacement rfl rfl hfresh
    rfl rfl rfl rfl (by intro k;rfl) hmap rfl rfl rfl rfl hvalid
  refine ⟨x+End.timeBound records acquired,?_,join h0 h1⟩
  dsimp only [timeBound,records,acquired,activation] at hx ⊢
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryForwardSource
