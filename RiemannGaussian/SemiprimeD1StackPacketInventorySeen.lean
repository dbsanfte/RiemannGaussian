/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
import RiemannGaussian.SemiprimeD1StackPacketInventoryRead
/-! # Actual packet discovery and seen-marker overrides
The real sentinel lookup computes absence. Only its actual empty payload prepends
one packet, preserving the original newest-first first-discovery order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventorySeen
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryClass SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
namespace D
export SemiprimeD1StackSourceKeyFrequencyEncoding (Rows dictionary read coded encoded)
export SemiprimeD1StackSourceKeyFrequencyMeaning (read_cons)
end D
local notation "ctl"=>Label.local
/-- All actual stored seen values are real singleton true words. This invariant starts empty and is preserved by every real marker push. -/
def Markers (rows:D.Rows):Prop:=∀row∈rows,row.2=[true]
/-- The actual first-match payload is either absent or precisely the singleton marker, never an advised Boolean. -/
theorem read_marker (rows:D.Rows) (key:List Bool) (h:Markers rows):D.read rows key=[] ∨ D.read rows key=[true] :=by
  induction rows with
  | nil=>exact Or.inl rfl
  | cons row rows ih=>
    rw [D.read_cons]
    split
    · exact Or.inr (h row (List.mem_cons_self))
    · exact ih (fun r hr=>h r (List.mem_cons_of_mem _ hr))
/-- A nonempty singleton is physically popped and checked for EOF; real absence executes the packet Frame and true vector-tag push. -/
theorem discovery_run (found:Bool) (source stream key dictionary index edge encoded cat seen slots packet slot:List Bool)
    (ps:List (List Bool)) (hist left right:List Bool):
    ∃t ≤ 10*(packet.length+1),Runs program t (ctl .readSeen)
      (view {(fresh source stream key dictionary edge) with frameScratch:=index,query:=encoded,oldCount:=(if found then [true] else [])}
        (reader (vectorBits ps) hist left right []) (orientation cat seen slots packet slot [] []))
      (ctl .pushMarker)
      (view {(fresh source stream key dictionary edge) with frameScratch:=index,query:=encoded,oldCount:=[]}
        (reader (vectorBits (if found then ps else packet::ps)) hist left right [])
        (orientation cat seen slots packet slot [] [])) :=by
  let f:W.Words:={(fresh source stream key dictionary edge) with frameScratch:=index,query:=encoded}
  let oo:=orientation cat seen slots packet slot [] []
  cases found
  · have h0:=pop_run .readSeen (ctl .prependPacket) (ctl .abort) (ctl .seenEOF) oldCount
      (view {f with oldCount:=[]} (reader (vectorBits ps) hist left right []) oo) [] rfl rfl
    change Runs program 1 _ _ _ (Function.update (view {f with oldCount:=[]} (reader (vectorBits ps) hist left right []) oo)
      (frequencyStack (F.lookupStack (.inr .output))) []) at h0
    rw [update_oldCount] at h0
    have h1:=frame_call .packet .prependPacket .tagPacket rfl
      (view {f with oldCount:=[]} (reader (vectorBits ps) hist left right []) oo) packet (vectorBits ps) rfl rfl rfl
    change Runs program _ _ _ _ (Function.update (view {f with oldCount:=[]} (reader (vectorBits ps) hist left right []) oo)
      (readerAllocation (.inr .key)) (frame packet (vectorBits ps))) at h1
    rw [update_readerAllocation,reader_update_packets] at h1
    have h2:=push_run .tagPacket (ctl .pushMarker) packets true
      (view {f with oldCount:=[]} (reader (frame packet (vectorBits ps)) hist left right []) oo) rfl
    change Runs program 1 _ _ _ (Function.update (view {f with oldCount:=[]}
      (reader (frame packet (vectorBits ps)) hist left right []) oo) (readerAllocation (.inr .key))
        (true::frame packet (vectorBits ps))) at h2
    rw [update_readerAllocation,reader_update_packets] at h2
    have h:=join (join h0 h1) h2
    exact ⟨_,by omega,h⟩
  · have h0:=pop_run .readSeen (ctl .prependPacket) (ctl .abort) (ctl .seenEOF) oldCount
      (view {f with oldCount:=[true]} (reader (vectorBits ps) hist left right []) oo) [true] rfl rfl
    change Runs program 1 _ _ _ (Function.update (view {f with oldCount:=[true]} (reader (vectorBits ps) hist left right []) oo)
      (frequencyStack (F.lookupStack (.inr .output))) []) at h0
    rw [update_oldCount] at h0
    have h1:=peek_run .seenEOF (ctl .pushMarker) (ctl .abort) (ctl .abort) oldCount
      (view {f with oldCount:=[]} (reader (vectorBits ps) hist left right []) oo) [] rfl rfl
    have h:=join h0 h1
    exact ⟨2,by omega,h⟩
/-- One allocated seen-map update changes no packet output or retained catalogue/slot-map word. -/
theorem update_seen (cat seen slots packet slot high flag word:List Bool):
    Function.update (orientation cat seen slots packet slot high flag)
      (SemiprimeD1StackPacketOrientation.aux .rightInput) word=orientation cat word slots packet slot high flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual singleton marker push, two NEW Frames, true record tag and full query drain; the marker remains for the placement-valid field. -/
theorem marker_run (source stream key dictionary index edge cat slots packet slot:List Bool)
    (rows:D.Rows) (r:R.Stack→List Bool):
    ∃t ≤ 100*(packet.length+1),Runs program t (ctl .pushMarker)
      (view {(fresh source stream key dictionary edge) with frameScratch:=index,query:=D.encoded packet} r
        (orientation cat (D.dictionary rows) slots packet slot [] [])) (ctl (.placement 0))
      (view {(fresh source stream key dictionary edge) with frameScratch:=index,incNext:=[true]} r
        (orientation cat (D.dictionary ((packet,[true])::rows)) slots packet slot [] [])) :=by
  let f:W.Words:={(fresh source stream key dictionary edge) with frameScratch:=index}
  let encoded:=D.encoded packet
  let oldDict:=D.dictionary rows
  let ob (seen:List Bool):O.Stack→List Bool:=orientation cat seen slots packet slot [] []
  let f0:W.Words:={f with query:=encoded}
  have h0:=push_run .pushMarker (ctl (.frameValue .seen)) marker true (view f0 r (ob oldDict)) rfl
  change Runs program 1 _ _ _ (Function.update (view f0 r (ob oldDict)) (frequencyStack (F.aux .incNext)) [true]) at h0
  rw [update_incNext] at h0
  let f1:W.Words:={f0 with incNext:=[true]}
  have h1:=frame_call (.value .seen) (.frameValue .seen) (.frameKey .seen) rfl (view f1 r (ob oldDict)) [true] oldDict rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob oldDict))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .rightInput)) (frame [true] oldDict)) at h1
  rw [update_orientationAllocation] at h1
  dsimp only [ob] at h1
  rw [update_seen] at h1
  have h2:=frame_call (.key .seen) (.frameKey .seen) (.tagMap .seen) rfl
    (view f1 r (ob (frame [true] oldDict))) encoded (frame [true] oldDict) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob (frame [true] oldDict)))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .rightInput)) (frame encoded (frame [true] oldDict))) at h2
  rw [update_orientationAllocation] at h2
  dsimp only [ob] at h2
  rw [update_seen] at h2
  let newDict:=true::frame encoded (frame [true] oldDict)
  have h3:=push_run (.tagMap .seen) (ctl .clearSeenQuery) seen true (view f1 r (ob (frame encoded (frame [true] oldDict)))) rfl
  change Runs program 1 _ _ _ (Function.update (view f1 r (ob (frame encoded (frame [true] oldDict))))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .rightInput)) newDict) at h3
  rw [update_orientationAllocation] at h3
  dsimp only [ob] at h3
  rw [update_seen] at h3
  have h4:=drain_loop .clearSeenQuery (ctl (.placement 0)) query rfl (view f1 r (ob newDict)) encoded rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob newDict)) (frequencyStack (F.lookupStack (.inr .query))) []) at h4
  rw [update_query] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨_,?_,h⟩
  dsimp only [encoded,D.encoded]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventorySeen
