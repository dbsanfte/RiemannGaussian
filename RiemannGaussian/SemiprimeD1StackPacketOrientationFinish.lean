/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationRowView
/-! # Exact physical high-index retention and final key/slot reversals -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationFinish
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationView SemiprimeD1StackPacketOrientationRowView
open SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Both actual copies of the remaining raw high word, both consuming chronological reverses and the actual cursor drain. -/
theorem finish_run (originals:Fin 3→List Bool) (index kh sh:List Bool):
    Runs program (11*index.length+2*kh.length+2*sh.length+15) (ctl .copyHighOutput)
      (rowView originals (fun _=>[]) index (fun _=>[]) kh sh [] [] []) (ctl .accept)
      (rowView originals (fun _=>[]) [] (fun _=>[]) [] [] (kh.reverse++index) sh.reverse index) :=by
  let bank (cursor kh sh ko so hi:List Bool):Stack→List Bool:=
    view (originals 0) (originals 1) (originals 2) [] [] cursor [] [] [] [] [] [] [] [] kh sh ko so hi
  have h0:=copy_call .highOutput .copyHighOutput .copyKeyTail rfl (bank index kh sh [] [] []) index [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank index kh sh [] [] []) (aux .highOutput) (index++[])) at h0
  dsimp only [bank] at h0
  rw [List.append_nil,update_highOutput] at h0
  have h1:=copy_call .keyTail .copyKeyTail .reverseKey rfl (bank index kh sh [] [] index) index [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank index kh sh [] [] index) (aux .keyOutput) (index++[])) at h1
  dsimp only [bank] at h1
  rw [List.append_nil,update_keyOutput] at h1
  have h2:=reverse_call .key .reverseKey .reverseSlots rfl (bank index kh sh index [] index) kh index rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (bank index kh sh index [] index)
    (aux .keyHistory) []) (aux .keyOutput) (kh.reverse++index)) at h2
  dsimp only [bank] at h2
  rw [update_keyHistory,update_keyOutput] at h2
  have h3:=reverse_call .slots .reverseSlots .clearCursor rfl (bank index [] sh (kh.reverse++index) [] index) sh [] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (bank index [] sh (kh.reverse++index) [] index)
    (aux .slotHistory) []) (aux .slotOutput) (sh.reverse++[])) at h3
  dsimp only [bank] at h3
  rw [SemiprimeD1StackPacketOrientationView.update_slotHistory,update_slotOutput,List.append_nil] at h3
  have h4:=drain_loop .clearCursor (ctl .accept) (aux .indexCursor) rfl
    (bank index [] [] (kh.reverse++index) sh.reverse index) index rfl
  dsimp only [bank] at h4
  rw [update_indexCursor] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  convert h using 1 <;> first | rfl | omega
end RiemannGaussian.SemiprimeD1StackPacketOrientationFinish
