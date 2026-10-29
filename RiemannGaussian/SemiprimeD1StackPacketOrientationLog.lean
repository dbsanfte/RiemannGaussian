/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationRowView
import RiemannGaussian.SemiprimeD1StackPacketOrientationEncoding
/-! # Actual low/high copy, nested framing, reverse-key logging and full colour cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationLog
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationView SemiprimeD1StackPacketOrientationRowView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame frame_length)
local notation "ctl"=>Label.local
/-- Exact bytes copied by the real conditional low/high source wiring. -/
def pairField (ordered:Bool) (colours:Bool→List Bool):List Bool:=frame (colours (!ordered)) (colours ordered)
/-- Exact sum of actual preserving-copy, two Frame, Reverse and three full drain traces. -/
def emitTime (ordered:Bool) (colours:Bool→List Bool):Nat:=
  (5*(colours ordered).length+4)+(6*(colours (!ordered)).length+5)+
    (6*(pairField ordered colours).length+5)+(2*(frame (pairField ordered colours) []).length+3)+
    ((pairField ordered colours).length+1)+((colours false).length+1)+((colours true).length+1)
/-- Actual nested coordinate framing retains the raw high-colour tail, logs one exact outer field, then clears all work. -/
theorem emit_run (ordered:Bool) (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool):
    Runs program (emitTime ordered colours) (ctl (.copyHigh ordered))
      (rowView originals readers cursor colours kh sh ko so hi) (ctl .leftTag)
      (rowView originals readers cursor (fun _=>[]) ((frame (pairField ordered colours) []).reverse++kh) sh ko so hi) :=by
  let low:=colours (!ordered)
  let high:=colours ordered
  let pair:=frame low high
  let chunk:=frame pair []
  let bank (left right pairBuffer outer history:List Bool):Stack→List Bool:=
    view (originals 0) (originals 1) (originals 2) (readers false) (readers true) cursor left right
      [] pairBuffer [] outer [] [] history sh ko so hi
  have h0:=copy_call (.high ordered) (.copyHigh ordered) (.inner ordered) rfl
    (bank (colours false) (colours true) [] [] kh) high [] (by cases ordered <;> rfl) rfl rfl
  change Runs program _ _ _ _ (Function.update (bank (colours false) (colours true) [] [] kh) (operand true) (high++[])) at h0
  dsimp only [bank] at h0
  rw [List.append_nil,update_rightOperand] at h0
  have h1:=frame_call (.inner ordered) (.inner ordered) .outer rfl
    (bank (colours false) (colours true) high [] kh) low high (by cases ordered <;> rfl) rfl rfl
  change Runs program _ _ _ _ (Function.update (bank (colours false) (colours true) high [] kh) (operand true) pair) at h1
  dsimp only [bank] at h1
  rw [update_rightOperand] at h1
  have h2:=frame_call .outer .outer .reverseChunk rfl
    (bank (colours false) (colours true) pair [] kh) pair [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (bank (colours false) (colours true) pair [] kh) buffer chunk) at h2
  dsimp only [bank] at h2
  rw [update_bufferWord] at h2
  have h3:=reverse_call .chunk .reverseChunk .clearPair rfl
    (bank (colours false) (colours true) pair chunk kh) chunk kh rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (bank (colours false) (colours true) pair chunk kh) buffer []) (aux .keyHistory) (chunk.reverse++kh)) at h3
  dsimp only [bank] at h3
  rw [update_bufferWord,update_keyHistory] at h3
  have h4:=drain_loop .clearPair (ctl (.clearColour false)) (operand true) rfl
    (bank (colours false) (colours true) pair [] (chunk.reverse++kh)) pair rfl
  dsimp only [bank] at h4
  rw [update_rightOperand] at h4
  have h5:=drain_loop (.clearColour false) (ctl (.clearColour true)) (colour false) rfl
    (bank (colours false) (colours true) [] [] (chunk.reverse++kh)) (colours false) rfl
  dsimp only [bank] at h5
  rw [show colour false=aux .leftColour from rfl,update_leftColour] at h5
  have h6:=drain_loop (.clearColour true) (ctl .leftTag) (colour true) rfl
    (bank [] (colours true) [] [] (chunk.reverse++kh)) (colours true) rfl
  dsimp only [bank] at h6
  rw [show colour true=aux .rightColour from rfl,update_rightColour] at h6
  exact join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6
/-- Paid nested framing has a fixed linear bound in both actual colour word widths. -/
theorem emitTime_le (ordered:Bool) (colours:Bool→List Bool):
    emitTime ordered colours ≤ 200*((colours false).length+(colours true).length+1) :=by
  unfold emitTime pairField
  simp only [frame_length,List.length_nil]
  cases ordered <;> simp only [Bool.not_false,Bool.not_true] <;> omega
end RiemannGaussian.SemiprimeD1StackPacketOrientationLog
