/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Actual six-field placement logger and full temporary cleanup
All six fields are preserved real words. The validity singleton is the actual
marker pushed only after both real source guards pass. Each outer row is logged
in reverse, then the complete stream is reversed once at the source finish.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryLog
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryClass SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame frame_length)
local notation "ctl"=>Label.local
/-- Exact six-field chronological placement payload with a physically confirmed true validity singleton. -/
def rowWord (key index packet slot edge:List Bool):List Bool:=
  frame key (frame index (frame packet (frame slot (frame edge (frame [true] [])))))
/-- Every preserved field, both real frame buffers and every actual drain is paid in this fixed physical-width cap. -/
theorem log_run (source stream key dictionary index edge cat seen slots packet slot packets hist left right:List Bool):
    ∃t ≤ 1000*(key.length+index.length+packet.length+slot.length+edge.length+1),
      Runs program t (ctl (.placement 0))
        (view {(fresh source stream key dictionary edge) with frameScratch:=index,incNext:=[true]}
          (reader packets hist left right []) (orientation cat seen slots packet slot [] []))
        (ctl (.clearReader .leftWord))
        (view (fresh source stream [] dictionary edge)
          (reader packets ((true::frame (rowWord key index packet slot edge) []).reverse++hist) left right [])
          (orientation cat seen slots packet slot [] [])) :=by
  let f:W.Words:={(fresh source stream key dictionary edge) with frameScratch:=index,incNext:=[true]}
  let rr:=reader packets hist left right []
  let ob (high outer:List Bool):O.Stack→List Bool:=
    SemiprimeD1StackPacketOrientationView.view cat seen slots [] [] [] [] [] [] [] [] [] [] [] [] outer packet slot high
  have h0:=frame_call (.placement 0) (.placement 0) (.placement 1) rfl
    (view f rr (ob [] [])) [true] [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob [] []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame [true] [])) at h0
  rw [update_orientationAllocation] at h0
  dsimp only [ob] at h0
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h0
  have h1:=frame_call (.placement 1) (.placement 1) (.placement 2) rfl
    (view f rr (ob (frame [true] []) [])) edge (frame [true] []) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob (frame [true] []) []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame edge (frame [true] []))) at h1
  rw [update_orientationAllocation] at h1
  dsimp only [ob] at h1
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h1
  have h2:=frame_call (.placement 2) (.placement 2) (.placement 3) rfl
    (view f rr (ob (frame edge (frame [true] [])) [])) slot (frame edge (frame [true] [])) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob (frame edge (frame [true] [])) []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame slot (frame edge (frame [true] [])))) at h2
  rw [update_orientationAllocation] at h2
  dsimp only [ob] at h2
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h2
  have h3:=frame_call (.placement 3) (.placement 3) (.placement 4) rfl
    (view f rr (ob (frame slot (frame edge (frame [true] []))) [])) packet (frame slot (frame edge (frame [true] []))) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob (frame slot (frame edge (frame [true] []))) []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame packet (frame slot (frame edge (frame [true] []))))) at h3
  rw [update_orientationAllocation] at h3
  dsimp only [ob] at h3
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h3
  have h4:=frame_call (.placement 4) (.placement 4) (.placement 5) rfl
    (view f rr (ob (frame packet (frame slot (frame edge (frame [true] [])))) [])) index (frame packet (frame slot (frame edge (frame [true] [])))) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob (frame packet (frame slot (frame edge (frame [true] [])))) []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame index (frame packet (frame slot (frame edge (frame [true] [])))))) at h4
  rw [update_orientationAllocation] at h4
  dsimp only [ob] at h4
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h4
  have h5:=frame_call (.placement 5) (.placement 5) .tagPlacement rfl
    (view f rr (ob (frame index (frame packet (frame slot (frame edge (frame [true] []))))) [])) key (frame index (frame packet (frame slot (frame edge (frame [true] []))))) rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr (ob (frame index (frame packet (frame slot (frame edge (frame [true] []))))) []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) (frame key (frame index (frame packet (frame slot (frame edge (frame [true] []))))))) at h5
  rw [update_orientationAllocation] at h5
  dsimp only [ob] at h5
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h5
  let row:=rowWord key index packet slot edge
  have h6:=push_run .tagPlacement (ctl .framePlacement) placementHistory true (view f rr (ob row [])) rfl
  change Runs program 1 _ _ _ (Function.update (view f rr (ob row [])) (readerAllocation (.inr .catalogue)) (true::hist)) at h6
  rw [update_readerAllocation] at h6
  dsimp only [rr] at h6
  rw [reader_update_history] at h6
  let rr1:=reader packets (true::hist) left right []
  have h7:=frame_call .outer .framePlacement .reversePlacement rfl (view f rr1 (ob row [])) row [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f rr1 (ob row []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .slotHistory)) (frame row [])) at h7
  rw [update_orientationAllocation] at h7
  dsimp only [ob] at h7
  rw [SemiprimeD1StackPacketOrientationView.update_slotHistory] at h7
  have h8:=reverse_call .row .reversePlacement .clearPlacement rfl (view f rr1 (ob row (frame row []))) (frame row []) (true::hist) rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (view f rr1 (ob row (frame row [])))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .slotHistory)) [])
    (readerAllocation (.inr .catalogue)) ((frame row []).reverse++(true::hist))) at h8
  rw [update_orientationAllocation,update_readerAllocation] at h8
  dsimp only [ob,rr1] at h8
  rw [SemiprimeD1StackPacketOrientationView.update_slotHistory,reader_update_history] at h8
  let newHist:=(frame row []).reverse++(true::hist)
  let rr2:=reader packets newHist left right []
  have h9:=drain_loop .clearPlacement (ctl .clearMarker) buffer rfl (view f rr2 (ob row [])) row rfl
  change Runs program _ _ _ _ (Function.update (view f rr2 (ob row []))
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .highOutput)) []) at h9
  rw [update_orientationAllocation] at h9
  dsimp only [ob] at h9
  rw [SemiprimeD1StackPacketOrientationView.update_highOutput] at h9
  have h10:=drain_loop .clearMarker (ctl .clearOldIndex) marker rfl (view f rr2 (ob [] [])) [true] rfl
  change Runs program _ _ _ _ (Function.update (view f rr2 (ob [] [])) (frequencyStack (F.aux .incNext)) []) at h10
  rw [update_incNext] at h10
  let f1:W.Words:={f with incNext:=[]}
  have h11:=drain_loop .clearOldIndex (ctl .clearRaw) oldIndex rfl (view f1 rr2 (ob [] [])) index rfl
  change Runs program _ _ _ _ (Function.update (view f1 rr2 (ob [] [])) (frequencyStack (F.aux .frameScratch)) []) at h11
  rw [update_frameScratch] at h11
  let f2:W.Words:={f1 with frameScratch:=[]}
  have h12:=drain_loop .clearRaw (ctl (.clearReader .leftWord)) raw rfl (view f2 rr2 (ob [] [])) key rfl
  change Runs program _ _ _ _ (Function.update (view f2 rr2 (ob [] [])) (frequencyStack (F.aux .raw)) []) at h12
  rw [update_raw] at h12
  have h:=(join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12)
  have hh:newHist=(true::frame row []).reverse++hist:=by
    simp only [newHist,List.reverse_cons,List.singleton_append,List.append_assoc]
  change Runs program _ _ _ _ (view (fresh source stream [] dictionary edge)
    (reader packets newHist left right []) (orientation cat seen slots packet slot [] [])) at h
  rw [hh] at h
  refine ⟨_,?_,h⟩
  dsimp only [row,rowWord]
  simp only [frame_length,List.length_nil,List.length_cons]
  omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryLog
