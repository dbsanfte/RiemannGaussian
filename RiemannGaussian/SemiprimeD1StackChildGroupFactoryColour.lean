/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryFields
/-! # Actual unary-coordinate scan of acquired colour-vector bytes
This fragment consumes an actual unary colour coordinate and real framed row.
EOF yields the empty binary zero word. The NEW jet axis is never read here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryColour
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryFields SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Only the three words actually touched by the colour reader. -/
def view (before:Stack→List Bool) (cursor reader word:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update before (aux .colourCursor) cursor)
    (aux .colourReader) reader) (aux .colourWord) word
/-- Exact acquired word and unread row suffix, for proof statements only. -/
def result : Nat→List (List Bool)→List Bool×List Bool
  | _,[]=>([],[])
  | 0,w::ws=>(w,vectorBits ws)
  | n+1,_::ws=>result n ws
/-- Own elapsed physical clock, including EOF and all failed-coordinate erasure. -/
def time : Nat→List (List Bool)→Nat
  | 0,[]=>4
  | n+1,[]=>n+4
  | 0,w::_=>8*w.length+10
  | n+1,w::ws=>9*w.length+11+time n ws
/-- Reader writes keep the abstract surrounding115-word bank untouched. -/
theorem view_write_cursor (b:Stack→List Bool) (c r w v:List Bool):
    Function.update (view b c r w) (aux .colourCursor) v=view b v r w:=by
  funext k
  by_cases h0:k=aux .colourWord
  · subst k;simp [view,aux]
  by_cases h1:k=aux .colourReader
  · subst k;simp [view,aux]
  by_cases h2:k=aux .colourCursor
  · subst k;simp [view,aux]
  simp [view,h0,h1,h2]
theorem view_write_reader (b:Stack→List Bool) (c r w v:List Bool):
    Function.update (view b c r w) (aux .colourReader) v=view b c v w:=by
  funext k
  by_cases h0:k=aux .colourWord
  · subst k;simp [view,aux]
  by_cases h1:k=aux .colourReader
  · subst k;simp [view,aux]
  simp [view,h0,h1]
theorem view_write_word (b:Stack→List Bool) (c r w v:List Bool):
    Function.update (view b c r w) (aux .colourWord) v=view b c r v:=by
  exact Function.update_idem _ _ _
/-- Actual parser call and actual TRUE-pop, before either skipping or selecting. -/
theorem parsed (take:Bool) (before:Stack→List Bool) (cursor word:List Bool)
    (rows:List (List Bool))
    (hs:before (field (.inl .scratch))=[]) (hv:before (field (.inr ()))=[]):
    Runs program (8*word.length+8) (if take then .local 1 2 else .local 0 30)
      (view before cursor (frame word (vectorBits rows)) [])
      (if take then .local 1 6 else .local 1 0)
      (view before cursor (vectorBits rows) word):=by
  have h:=field_read 0 (if take then .local 1 2 else .local 0 30)
    (if take then .local 1 3 else .local 0 31)
    (if take then .local 1 6 else .local 1 0) abort abort
    (by cases take <;> rfl) (by cases take <;> rfl)
    (view before cursor (frame word (vectorBits rows)) []) word (vectorBits rows)
    (by simp [fieldStack,fieldPorts,view,aux])
    (by simp [fieldStack,fieldPorts,view,aux])
    (by simpa [view,field,aux] using hs)
    (by simpa [view,field,aux] using hv)
  change Runs program _ _ _ _
    (Function.update (Function.update (view before cursor (frame word (vectorBits rows)) [])
      (aux .colourReader) (vectorBits rows)) (aux .colourWord) word) at h
  rw [view_write_reader,view_write_word] at h
  exact h
/-- Once EOF is real, all remaining unary metadata and reader bytes are physically drained. -/
theorem default (before:Stack→List Bool) (cursor reader:List Bool):
    Runs program (cursor.length+reader.length+2) (.local 1 4) (view before cursor reader [])
      (.local 1 6) (view before [] [] []):=by
  have h0:=drain_loop (.local 1 4) (.local 1 5) (aux .colourCursor) rfl
    (view before cursor reader []) cursor (by simp [view,aux])
  rw [view_write_cursor] at h0
  have h1:=drain_loop (.local 1 5) (.local 1 6) (aux .colourReader) rfl
    (view before [] reader []) reader (by simp [view,aux])
  rw [view_write_reader] at h1
  have h:=join h0 h1
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
/-- Complete real colour-coordinate loop: no host row getter or decoded colour is an instruction. -/
theorem source_trace (before:Stack→List Bool) (n:Nat) (rows:List (List Bool))
    (hs:before (field (.inl .scratch))=[]) (hv:before (field (.inr ()))=[]):
    Runs program (time n rows) (.local 0 28) (view before (List.replicate n true) (vectorBits rows) [])
      (.local 1 6) (view before [] (result n rows).2 (result n rows).1):=by
  induction n generalizing rows with
  | zero=>
    have h0:=pop_run (.local 0 28) (.local 1 1) (.local 0 29) (.local 0 29)
      (aux .colourCursor) (view before [] (vectorBits rows) []) [] rfl
      (by simp [view,aux])
    simp only [List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose] at h0
    rw [view_write_cursor] at h0
    cases rows with
    | nil=>
      have h1:=pop_run (.local 1 1) (.local 1 4) (.local 1 4) (.local 1 2)
        (aux .colourReader) (view before [] [false] []) [false] rfl
        (by simp [view,aux])
      simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
      rw [view_write_reader] at h1
      exact join h0 (join h1 (default before [] []))
    | cons w ws=>
      have h1:=pop_run (.local 1 1) (.local 1 4) (.local 1 4) (.local 1 2)
        (aux .colourReader) (view before [] (vectorBits (w::ws)) []) (vectorBits (w::ws)) rfl
        (by simp [view,aux])
      simp only [vectorBits,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
      rw [view_write_reader] at h1
      have h:=join h0 (join h1 (parsed true before [] w ws hs hv))
      have ht:1+(1+(8*w.length+8))=8*w.length+10:=by omega
      rw [ht] at h
      simpa [time,result] using h
  | succ n ih=>
    have h0:=pop_run (.local 0 28) (.local 1 1) (.local 0 29) (.local 0 29)
      (aux .colourCursor) (view before (true::List.replicate n true) (vectorBits rows) [])
      (true::List.replicate n true) rfl (by simp [view,aux])
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [view_write_cursor] at h0
    cases rows with
    | nil=>
      have h1:=pop_run (.local 0 29) (.local 1 4) (.local 1 4) (.local 0 30)
        (aux .colourReader) (view before (List.replicate n true) [false] []) [false] rfl
        (by simp [view,aux])
      simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
      rw [view_write_reader] at h1
      have h:=join h0 (join h1 (default before (List.replicate n true) []))
      simpa only [time,result,List.length_replicate,List.length_nil,Nat.add_zero,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.replicate_succ] using h
    | cons w ws=>
      have h1:=pop_run (.local 0 29) (.local 1 4) (.local 1 4) (.local 0 30)
        (aux .colourReader) (view before (List.replicate n true) (vectorBits (w::ws)) [])
        (vectorBits (w::ws)) rfl (by simp [view,aux])
      simp only [vectorBits,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
      rw [view_write_reader] at h1
      have h2:=parsed false before (List.replicate n true) w ws hs hv
      have h3:=drain_loop (.local 1 0) (.local 0 28) (aux .colourWord) rfl
        (view before (List.replicate n true) (vectorBits ws) w) w
        (by simp [view,aux])
      rw [view_write_word] at h3
      have h:=join h0 (join h1 (join h2 (join h3 (ih ws))))
      have ht:1+(1+((8*w.length+8)+((w.length+1)+time n ws)))=9*w.length+11+time n ws:=by omega
      rw [ht] at h
      simpa only [time,result,List.replicate_succ,Bool.false_eq_true,ite_false] using h
/-- Semantic interpretation of the computed field, including every out-of-range default. -/
theorem result_word (n:Nat) (rows:List (List Bool)):(result n rows).1=rows.getD n []:=by
  induction n generalizing rows with
  | zero=>cases rows <;> simp [result]
  | succ n ih=>cases rows <;> simp [result,ih]
/-- The actual scan is linear in the physically supplied unary coordinate and row bytes. -/
theorem time_le (n:Nat) (rows:List (List Bool)):
    time n rows≤12*(n+(vectorBits rows).length+1):=by
  induction n generalizing rows with
  | zero=>
    cases rows with
    | nil=>simp [time,vectorBits]
    | cons w ws=>
      simp only [time,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
      omega
  | succ n ih=>
    cases rows with
    | nil=>simp only [time,vectorBits,List.length_cons,List.length_nil];omega
    | cons w ws=>
      have h:=ih ws
      simp only [time,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length] at h ⊢
      omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryColour
