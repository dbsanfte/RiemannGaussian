/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventorySeen
/-! # Entire actual sentinel/lookup/discovery/marker stage
Actual OLD marker words alone select first discovery. All dictionary scans and
obsolete override bytes are copied and read by the real source procedures.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryDiscovery
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryClass SemiprimeD1StackPacketInventorySeen
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace D
export SemiprimeD1StackSourceKeyFrequencyEncoding (Rows dictionary read coded encoded)
end D
local notation "ctl"=>Label.local
/-- Exact newest-first first-discovery packet list from the actually acquired old marker. -/
def nextPackets (rows:D.Rows) (packet:List Bool) (ps:List (List Bool)):List (List Bool):=
  if (D.read rows packet).isEmpty then packet::ps else ps
/-- Own complete stage cap is the sum of actual sentinel, whole lookup/copy/drain and bounded discovery/put traces. -/
def seenBound (rows:D.Rows) (packet:List Bool):Nat:=
  (5*packet.length+7)+SemiprimeD1StackPacketInventoryRead.readBound (D.encoded packet) (D.coded rows)+110*(packet.length+1)
/-- Complete actual packet discovery and marker update, with original order and retained OLD-j cache. -/
theorem seen_run (source stream key dictionary index edge cat slots packet slot:List Bool)
    (rows:D.Rows) (ps:List (List Bool)) (hist left right:List Bool) (hm:Markers rows):
    ∃t ≤ seenBound rows packet,Runs program t (ctl .encodePacket)
      (view {(fresh source stream key dictionary edge) with frameScratch:=index}
        (reader (vectorBits ps) hist left right []) (orientation cat (D.dictionary rows) slots packet slot [] []))
      (ctl (.placement 0))
      (view {(fresh source stream key dictionary edge) with frameScratch:=index,incNext:=[true]}
        (reader (vectorBits (nextPackets rows packet ps)) hist left right [])
        (orientation cat (D.dictionary ((packet,[true])::rows)) slots packet slot [] [])) :=by
  let f:W.Words:={(fresh source stream key dictionary edge) with frameScratch:=index}
  let rr:=reader (vectorBits ps) hist left right []
  let oo:=orientation cat (D.dictionary rows) slots packet slot [] []
  let encoded:=D.encoded packet
  let old:=D.read rows packet
  have h0:=sentinel_call .packet .encodePacket (.copyMap .seen) rfl (view f rr oo) packet rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr oo) (frequencyStack (F.lookupStack (.inr .query))) encoded) at h0
  rw [update_query] at h0
  let f1:W.Words:={f with query:=encoded}
  have hready:∀k,view f1 rr oo (lookupStack k)=(SemiprimeD1StackOwnerLookup.initial encoded []).data k:=by
    intro k;rcases k with k|k <;> cases k <;> rfl
  obtain ⟨t1,ht1,h1⟩:=SemiprimeD1StackPacketInventoryRead.read_run .seen f1 rr oo encoded (D.coded rows) hready rfl
  change Runs program t1 _ _ _ (view {f1 with lookupReader:=[],oldCount:=old} rr oo) at h1
  rcases read_marker rows packet hm with he|he
  · have h2:=discovery_run false source stream key dictionary index edge encoded cat (D.dictionary rows) slots packet slot ps hist left right
    change old=[] at he
    rw [he] at h1
    obtain ⟨t2,ht2,h2⟩:=h2
    obtain ⟨t3,ht3,h3⟩:=marker_run source stream key dictionary index edge cat slots packet slot rows
      (reader (vectorBits (packet::ps)) hist left right [])
    have h:=join (join (join h0 h1) h2) h3
    refine ⟨5*packet.length+7+t1+t2+t3,?_,?_⟩
    · unfold seenBound
      dsimp only [encoded] at ht1 ⊢
      omega
    · have hn:nextPackets rows packet ps=packet::ps:=by
        simp only [nextPackets,show D.read rows packet=[] from he,List.isEmpty_nil,ite_true]
      rw [hn]
      exact h
  · have h2:=discovery_run true source stream key dictionary index edge encoded cat (D.dictionary rows) slots packet slot ps hist left right
    change old=[true] at he
    rw [he] at h1
    obtain ⟨t2,ht2,h2⟩:=h2
    obtain ⟨t3,ht3,h3⟩:=marker_run source stream key dictionary index edge cat slots packet slot rows
      (reader (vectorBits ps) hist left right [])
    have h:=join (join (join h0 h1) h2) h3
    refine ⟨5*packet.length+7+t1+t2+t3,?_,?_⟩
    · unfold seenBound
      dsimp only [encoded] at ht1 ⊢
      omega
    · have hn:nextPackets rows packet ps=ps:=by
        simp only [nextPackets,show D.read rows packet=[true] from he,List.isEmpty_cons,Bool.false_eq_true,ite_false]
      rw [hn]
      exact h
end RiemannGaussian.SemiprimeD1StackPacketInventoryDiscovery
