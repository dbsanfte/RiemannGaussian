/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsRowView
import RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
/-! # One actual colour field parse and chronological reverse-row log
The field's physical false delimiter is read even for colour zero. Every field,
valid byte, row tag, preserving Frame, reversal and temporary-colour erase is
paid; no native append/reversal or supplied coefficient field is executed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsLog
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsPrimitives SemiprimeD1StackPacketRowsRowView
open SemiprimeD1StackPacketRowsEncoding (row)
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- A complete real colour-field source step, including its actual word cleanup and byte-order-correct row log. -/
theorem colour_run (side:Bool) (key catalogue:List Bool) (streams histories outputs:Bool→List Bool)
    (word tail:List Bool) (hi:streams side=frame word tail) :
    Runs program (19*word.length+20) (ctl (.parseColour side))
      (rowView key catalogue streams (fun _=>[]) histories outputs [])
      (ctl (if side then .leftEOF else .parseColour true))
      (rowView key catalogue (Function.update streams side tail) (fun _=>[])
        (Function.update histories side ((row word).reverse++histories side)) outputs []) :=by
  let rest:=Function.update streams side tail
  let words:=Function.update (fun _ :Bool=>[]) side word
  let tagged:=Function.update histories side (true::histories side)
  have hinput:rowView key catalogue streams (fun _=>[]) histories outputs []
      (fieldStack (.colour side) (.inl .input))=frame word tail:=by
    exact (stream_get key catalogue streams (fun _=>[]) histories outputs [] side).trans hi
  have hout:rowView key catalogue streams (fun _=>[]) histories outputs []
      (fieldStack (.colour side) (.inl .output))=[]:=by cases side <;> rfl
  have h0:=field_valid (.colour side) (.parseColour side) (.colourValid side) (ctl (.tagHistory side)) rfl rfl
    (rowView key catalogue streams (fun _=>[]) histories outputs []) word tail hinput hout rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (rowView key catalogue streams (fun _=>[]) histories outputs []) (rowBytes side) tail) (colourWord side) word) at h0
  rw [update_streams,update_words] at h0
  have h1:=push_run (.tagHistory side) (ctl (.frameColour side)) (history side) true
    (rowView key catalogue rest words histories outputs []) rfl
  rw [history_get] at h1
  change Runs program 1 _ _ _ (Function.update (rowView key catalogue rest words histories outputs [])
    (history side) (true::histories side)) at h1
  rw [update_histories] at h1
  have hw:rowView key catalogue rest words tagged outputs [] (frameStack side 0)=word:=by cases side <;> rfl
  have h2:=frame_call side (.frameColour side) (.reverseColour side) rfl
    (rowView key catalogue rest words tagged outputs []) word [] hw rfl rfl
  change Runs program _ _ _ _ (Function.update (rowView key catalogue rest words tagged outputs []) frameBuffer (frame word [])) at h2
  rw [update_buffer] at h2
  have hy:rowView key catalogue rest words tagged outputs (frame word []) (reverseStack (.colour side) 1)=
      true::histories side:=by cases side <;> rfl
  have h3:=reverse_call (.colour side) (.reverseColour side) (.clearColour side) rfl
    (rowView key catalogue rest words tagged outputs (frame word [])) (frame word []) (true::histories side) rfl hy
  change Runs program _ _ _ _ (Function.update (Function.update
    (rowView key catalogue rest words tagged outputs (frame word [])) frameBuffer []) (history side)
      ((frame word []).reverse++(true::histories side))) at h3
  rw [update_buffer,update_histories] at h3
  have he:Function.update tagged side ((frame word []).reverse++(true::histories side))=
      Function.update histories side ((row word).reverse++histories side):=by
    dsimp only [tagged]
    rw [Function.update_idem]
    congr 1
    simp only [row,List.reverse_cons,List.append_assoc,List.singleton_append]
  rw [he] at h3
  have h4:=drain_loop (.clearColour side) (ctl (if side then .leftEOF else .parseColour true)) (colourWord side) rfl
    (rowView key catalogue rest words (Function.update histories side ((row word).reverse++histories side)) outputs []) word
    (by cases side <;> rfl)
  rw [update_words] at h4
  have hz:Function.update words side []=(fun _ :Bool=>[]) :=by
    dsimp only [words]
    rw [Function.update_idem]
    exact Function.update_eq_self side (fun _ :Bool=>[])
  rw [hz] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have ht:(8*word.length+8)+1+(6*word.length+5)+(2*(frame word []).length+3)+(word.length+1)=
      19*word.length+20:=by
    rw [SemiprimeSourceHistogramKeyBits.frame_length]
    simp only [List.length_nil]
    omega
  simpa only [ht] using h
end RiemannGaussian.SemiprimeD1StackPacketRowsLog
