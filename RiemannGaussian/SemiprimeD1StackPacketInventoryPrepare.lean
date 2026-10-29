/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryBanks
/-! # Actual initialization and source-key vector copy
The three maps and discovery vector start by real false pushes. Only the two
original source words are preloaded; every other cache/work cell starts empty.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryPrepare
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackPacketInventoryBanks
open SemiprimeD1StackPacketInventoryClass SemiprimeD1StackProcedureTrace
namespace OW
export SemiprimeD1StackPacketOrientationView (update_rightInput update_indexInput)
end OW
local notation "ctl"=>Label.local
/-- All59 actual initial cells contain exactly two source words and no prepared map, count, packet or clock. -/
theorem initial_data (keys alphabet:List Bool):
    (initial keys alphabet).data=view (fresh keys [] [] [] []) (reader [] [] [] [] []) (orientation alphabet [] [] [] [] [] []) :=by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · cases k <;> rfl
/-- Four literal empty-cache pushes and one complete paid preserving copy reach the clean first actual vector-tag read. -/
theorem prepare_run (keys alphabet:List Bool):
    Runs program (5*keys.length+8) (ctl .start) (initial keys alphabet).data (ctl .header)
      (boundary keys alphabet keys SemiprimeD1StackPacketInventoryEncoding.empty) :=by
  let f:=fresh keys [] [] [] []
  let r:=reader [] [] [] [] []
  let o:=orientation alphabet [] [] [] [] [] []
  have h0:=push_run .start (ctl .seedSeen) classes false (view f r o) rfl
  change Runs program 1 _ _ _ (Function.update (view f r o) (frequencyStack (F.aux .dictionary)) [false]) at h0
  rw [update_dictionary] at h0
  let f1:W.Words:={f with dictionary:=[false]}
  have h1:=push_run .seedSeen (ctl .seedSlots) seen false (view f1 r o) rfl
  change Runs program 1 _ _ _ (Function.update (view f1 r o)
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .rightInput)) [false]) at h1
  rw [update_orientationAllocation] at h1
  dsimp only [o,orientation] at h1
  rw [OW.update_rightInput] at h1
  let o1:=orientation alphabet [false] [] [] [] [] []
  have h2:=push_run .seedSlots (ctl .seedPackets) slots false (view f1 r o1) rfl
  change Runs program 1 _ _ _ (Function.update (view f1 r o1)
    (orientationAllocation (SemiprimeD1StackPacketOrientation.aux .indexInput)) [false]) at h2
  rw [update_orientationAllocation] at h2
  dsimp only [o1,orientation] at h2
  rw [OW.update_indexInput] at h2
  let o2:=orientation alphabet [false] [false] [] [] [] []
  have h3:=push_run .seedPackets (ctl .copyStream) packets false (view f1 r o2) rfl
  change Runs program 1 _ _ _ (Function.update (view f1 r o2) (readerAllocation (.inr .key)) [false]) at h3
  rw [update_readerAllocation] at h3
  dsimp only [r] at h3
  rw [reader_update_packets] at h3
  let r1:=reader [false] [] [] [] []
  have h4:=copy_call .stream .copyStream .header rfl (view f1 r1 o2) keys [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view f1 r1 o2) (frequencyStack (F.aux .reader)) (keys++[])) at h4
  rw [List.append_nil,update_reader] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  rw [initial_data]
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackPacketInventoryPrepare
