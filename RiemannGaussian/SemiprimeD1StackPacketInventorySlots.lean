/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Actual raw packet-slot address and positive-edge map override
The real orientation high word is drained, the actual slot is copied as a raw
tail, and two actual Frame calls write a sentinel-keyed newest-first override.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventorySlots
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryClass SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame frame_length)
namespace D
export SemiprimeD1StackSourceKeyFrequencyEncoding (Rows dictionary encoded)
end D
local notation "ctl"=>Label.local
/-- The actual temporary high/address/record buffer is a distinct allocated orientation word. -/
theorem update_high (cat seen slots packet slot high flag word:List Bool):
    Function.update (orientation cat seen slots packet slot high flag)
      (SemiprimeD1StackPacketOrientation.aux .highOutput) word=orientation cat seen slots packet slot word flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- The persistent slot dictionary is the displaced input allocation, outside every actual orientation write. -/
theorem update_slots (cat seen slots packet slot high flag word:List Bool):
    Function.update (orientation cat seen slots packet slot high flag)
      (SemiprimeD1StackPacketOrientation.aux .indexInput) word=orientation cat seen word packet slot high flag :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Complete real slot-map write: raw frame(packet,slot), actual sentinel, exact edge payload and full query/address cleanup. -/
theorem slots_run (source stream key dictionary index edge cat seen packet slot high:List Bool)
    (rows:D.Rows) (r:R.Stack→List Bool):
    ∃t ≤ 200*(packet.length+slot.length+high.length+edge.length+1),
      Runs program t (ctl .clearHigh)
        (view {(fresh source stream key dictionary edge) with frameScratch:=index} r
          (orientation cat seen (D.dictionary rows) packet slot high [])) (ctl .encodePacket)
        (view {(fresh source stream key dictionary edge) with frameScratch:=index} r
          (orientation cat seen (D.dictionary ((frame packet slot,edge)::rows)) packet slot [] [])) :=by
  let f:W.Words:={(fresh source stream key dictionary edge) with frameScratch:=index}
  let oldDict:=D.dictionary rows
  let address:=frame packet slot
  let encoded:=D.encoded address
  let ob (slots high:List Bool):O.Stack→List Bool:=orientation cat seen slots packet slot high []
  have h0:=drain_loop .clearHigh (ctl .copyAddress) buffer rfl (view f r (ob oldDict high)) high rfl
  change Runs program _ _ _ _ (Function.update (view f r (ob oldDict high))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) []) at h0
  rw [update_orientationAllocation] at h0
  dsimp only [ob] at h0
  rw [update_high] at h0
  have h1:=copy_call .slotAddress .copyAddress .frameAddress rfl (view f r (ob oldDict [])) slot [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f r (ob oldDict []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (slot++[])) at h1
  rw [List.append_nil,update_orientationAllocation] at h1
  dsimp only [ob] at h1
  rw [update_high] at h1
  have h2:=frame_call .address .frameAddress .encodeAddress rfl (view f r (ob oldDict slot)) packet slot rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f r (ob oldDict slot))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) address) at h2
  rw [update_orientationAllocation] at h2
  dsimp only [ob] at h2
  rw [update_high] at h2
  have h3:=sentinel_call .address .encodeAddress (.frameValue .slots) rfl (view f r (ob oldDict address)) address rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f r (ob oldDict address))
    (frequencyStack (F.lookupStack (.inr .query))) encoded) at h3
  rw [update_query] at h3
  let f1:W.Words:={f with query:=encoded}
  have h4:=frame_call (.value .slots) (.frameValue .slots) (.frameKey .slots) rfl
    (view f1 r (ob oldDict address)) edge oldDict rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob oldDict address))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .indexInput)) (frame edge oldDict)) at h4
  rw [update_orientationAllocation] at h4
  dsimp only [ob] at h4
  rw [update_slots] at h4
  have h5:=frame_call (.key .slots) (.frameKey .slots) (.tagMap .slots) rfl
    (view f1 r (ob (frame edge oldDict) address)) encoded (frame edge oldDict) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob (frame edge oldDict) address))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .indexInput)) (frame encoded (frame edge oldDict))) at h5
  rw [update_orientationAllocation] at h5
  dsimp only [ob] at h5
  rw [update_slots] at h5
  let newDict:=true::frame encoded (frame edge oldDict)
  have h6:=push_run (.tagMap .slots) (ctl .clearSlotQuery) slots true
    (view f1 r (ob (frame encoded (frame edge oldDict)) address)) rfl
  change Runs program 1 _ _ _ (Function.update (view f1 r (ob (frame encoded (frame edge oldDict)) address))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .indexInput)) newDict) at h6
  rw [update_orientationAllocation] at h6
  dsimp only [ob] at h6
  rw [update_slots] at h6
  have h7:=drain_loop .clearSlotQuery (ctl .clearAddress) query rfl (view f1 r (ob newDict address)) encoded rfl
  change Runs program _ _ _ _ (Function.update (view f1 r (ob newDict address))
    (frequencyStack (F.lookupStack (.inr .query))) []) at h7
  rw [update_query] at h7
  have h8:=drain_loop .clearAddress (ctl .encodePacket) buffer rfl (view f r (ob newDict address)) address rfl
  change Runs program _ _ _ _ (Function.update (view f r (ob newDict address))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) []) at h8
  rw [update_orientationAllocation] at h8
  dsimp only [ob] at h8
  rw [update_high] at h8
  have h:=join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  refine ⟨_,?_,h⟩
  dsimp only [encoded,D.encoded,address]
  simp only [List.length_append,List.length_cons,List.length_nil,frame_length]
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventorySlots
