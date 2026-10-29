/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksView
/-! # Real coefficient framing and sequential actual/default field reads
The real source never changes a coefficient's binary padding or value. EOF is
peeked and retained while physical rank markers still require default zeros.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksFields
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives
open SemiprimeD1StackJetBlocksView SemiprimeD1StackJetBlocksEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exact actual single-field emission; all old context/source/loop words are retained. -/
def emitAfter (before:Stack→List Bool) (word hist:List Bool) :Stack→List Bool :=
  Function.update (Function.update before (aux .word) []) (aux .rowHistory) ((Codec.chunk word).reverse++hist)
/-- One real preserving Frame, true tag, real reverse and physical word cleanup emit exactly one coefficient field. -/
theorem emit_field (before:Stack→List Bool) (word hist:List Bool)
    (hw:before (aux .word)=word) (hh:before (aux .rowHistory)=hist)
    (hb:before (aux .frameBuffer)=[]) (hs:before (aux .frameScratch)=[]) :
    Runs program (11*word.length+14) (ctl .frame) before (ctl .inner) (emitAfter before word hist) :=by
  let b1:=Function.update before (aux .frameBuffer) (frame word [])
  let b2:=Function.update b1 (aux .frameBuffer) (Codec.chunk word)
  let b3:=Function.update (Function.update b2 (aux .frameBuffer) []) (aux .rowHistory) ((Codec.chunk word).reverse++hist)
  have h0:=frame_call before word [] hw hb hs
  have h1:=push_run .fieldTag (ctl .fieldReverse) (aux .frameBuffer) true b1 rfl
  have he1:Function.update b1 (aux .frameBuffer) (true::b1 (aux .frameBuffer))=b2:=by
    simp only [b2,b1,Codec.chunk,Function.update_self,Function.update_idem]
  rw [he1] at h1
  have h2:=reverse_call .field .fieldReverse .clearWord rfl b2 (Codec.chunk word) hist
    (by simp [b2,reverseStack]) (by simpa [b2,b1,reverseStack,aux,Function.update] using hh)
  have h3:=drain_loop .clearWord (ctl .inner) (aux .word) rfl b3 word
    (by simpa [b3,b2,b1,aux,Function.update] using hw)
  have h:=join (join (join h0 h1) h2) h3
  have he:Function.update b3 (aux .word) []=emitAfter before word hist:=by
    dsimp only [aux] at hb
    funext k;rcases k with k|k
    · rfl
    · cases k <;> simp [b3,b2,b1,emitAfter,aux,Function.update,hb]
  rw [he] at h
  have hl:=Codec.chunk_length word
  convert h using 1; omega
/-- Actual non-EOF coefficient read consumes one rank marker, one vector tag and one complete real field. -/
theorem real_slot (context:X.Stack→List Bool) (coefficients blocks todo hist history word:List Bool) (words:List (List Bool)) (r:Nat) :
    Runs program (19*word.length+25) (ctl .inner)
      (data context coefficients blocks todo (vectorBits (word::words)) (List.replicate (r+1) true) [] hist [] history)
      (ctl .inner) (data context coefficients blocks todo (vectorBits words) (List.replicate r true) []
        ((Codec.chunk word).reverse++hist) [] history) :=by
  let source:=data context coefficients blocks todo (vectorBits (word::words)) (List.replicate (r+1) true) [] hist [] history
  let b1:=data context coefficients blocks todo (vectorBits (word::words)) (List.replicate r true) [] hist [] history
  let b2:=data context coefficients blocks todo (frame word (vectorBits words)) (List.replicate r true) [] hist [] history
  let parsed:=data context coefficients blocks todo (vectorBits words) (List.replicate r true) word hist [] history
  have h0:Runs program 1 (ctl .inner) source (ctl .peek) b1:=by
    apply one_base program (ctl .inner) (ctl .peek)
      (.pop (aux .rankTodo) (ctl .rowSeed) (ctl .abort) (ctl .peek)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (ctl .peek) b1 (ctl .tag) b1:=by
    apply one_base program (ctl .peek) (ctl .tag)
      (.peek (aux .reader) (ctl .frame) (ctl .frame) (ctl .tag)) _ _ rfl
    · rfl
    · rfl
  have h2:Runs program 1 (ctl .tag) b1 (ctl .field) b2:=by
    apply one_base program (ctl .tag) (ctl .field)
      (.pop (aux .reader) (ctl .abort) (ctl .abort) (ctl .field)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h3:=field_call .field .valid rfl b2 word (vectorBits words) rfl rfl rfl rfl
  have he3:Function.update (Function.update (Function.update b2 fieldInput (vectorBits words)) fieldOutput word) (aux .valid) [true]=
      Function.update parsed (aux .valid) [true]:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> simp [b2,parsed,fieldInput,fieldOutput,fieldStack,data,aux,Function.update]
  rw [he3] at h3
  have h4:Runs program 1 (ctl .valid) (Function.update parsed (aux .valid) [true]) (ctl .frame) parsed:=by
    apply one_base program (ctl .valid) (ctl .frame)
      (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .frame)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h5:=emit_field parsed word hist rfl rfl rfl rfl
  have he5:emitAfter parsed word hist=data context coefficients blocks todo (vectorBits words) (List.replicate r true) []
      ((Codec.chunk word).reverse++hist) [] history:=by
    dsimp only [emitAfter,parsed]
    rw [data_word,data_rowHistory]
  rw [he5] at h5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  convert h using 1; omega
/-- Actual source EOF is peeked rather than consumed; one empty coefficient field still emits for each actual rank marker. -/
theorem empty_slot (context:X.Stack→List Bool) (coefficients blocks todo hist history:List Bool) (r:Nat) :
    Runs program 16 (ctl .inner)
      (data context coefficients blocks todo (vectorBits []) (List.replicate (r+1) true) [] hist [] history)
      (ctl .inner) (data context coefficients blocks todo (vectorBits []) (List.replicate r true) []
        ((Codec.chunk []).reverse++hist) [] history) :=by
  let source:=data context coefficients blocks todo (vectorBits []) (List.replicate (r+1) true) [] hist [] history
  let b1:=data context coefficients blocks todo (vectorBits []) (List.replicate r true) [] hist [] history
  have h0:Runs program 1 (ctl .inner) source (ctl .peek) b1:=by
    apply one_base program (ctl .inner) (ctl .peek)
      (.pop (aux .rankTodo) (ctl .rowSeed) (ctl .abort) (ctl .peek)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (ctl .peek) b1 (ctl .frame) b1:=by
    apply one_base program (ctl .peek) (ctl .frame)
      (.peek (aux .reader) (ctl .frame) (ctl .frame) (ctl .tag)) _ _ rfl
    · rfl
    · rfl
  have h2:=emit_field b1 [] hist rfl rfl rfl rfl
  have he2:emitAfter b1 [] hist=data context coefficients blocks todo (vectorBits []) (List.replicate r true) []
      ((Codec.chunk []).reverse++hist) [] history:=by
    dsimp only [emitAfter,b1]
    rw [data_word,data_rowHistory]
  rw [he2] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackJetBlocksFields
