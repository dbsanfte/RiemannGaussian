/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRows
import RiemannGaussian.SemiprimeD1PacketRows
/-! # Physical row-stream, lookup-presence and chronological logger identities
All definitions below describe actual bytes. No row, presence verdict, decoded
ID, coordinate count or list operation is an operand of the literal source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Map
export SemiprimeD1StackOwnerLookup (records result initial done program)
end Map
/-- Proof-side interpretation of the actual numeric dictionary match, including empty zero IDs. -/
def present (query:List Bool) :List (List Bool×List Bool)→Bool
  | []=>false
  | (key,_)::rows=>if bitValue key=bitValue query then true else present query rows
/-- Even an empty remaining record list has one real false terminator. -/
theorem records_nonempty (rows:List (List Bool×List Bool)) :Map.records rows []≠[] :=by
  cases rows <;> intro h <;> cases h
/-- Actual successful lookup retains a nonempty unread suffix; absence consumes its false terminator. -/
theorem result_presence (query:List Bool) (rows:List (List Bool×List Bool)) :
    (Map.result query rows []).2≠[] ↔ present query rows=true :=by
  induction rows with
  | nil=>simp only [Map.result,present,Bool.false_eq_true,ne_eq,not_true_eq_false]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    by_cases h:bitValue key=bitValue query
    · simp only [Map.result,present,h,ite_true]
      constructor
      · intro _;trivial
      · intro _;exact records_nonempty rows
    · simpa only [Map.result,present,h,ite_false] using ih
/-- The presence test is tied to the actual complete11-role source trace, not a supplied lookup answer. -/
theorem actual_lookup_presence (query:List Bool) (rows:List (List Bool×List Bool)) :
    SemiprimeD1StackCalls.run Map.program
        (SemiprimeD1StackOwnerLookupExecution.loopTime query rows+1)
        (Map.initial query (Map.records rows []))=some (Map.done query rows []) ∧
      ((Map.done query rows []).data (.inr .reader)≠[] ↔ present query rows=true) :=
  ⟨SemiprimeD1StackOwnerLookupExecution.source_run query rows [],result_presence query rows⟩
/-- Found zero-dimensional payload stays empty, while its unread false terminator witnesses actual presence. -/
theorem empty_payload_found (query:List Bool) (rows:List (List Bool×List Bool)) :
    (Map.done query ((query,[])::rows) []).data (.inr .output)=[] ∧
      (Map.done query ((query,[])::rows) []).data (.inr .reader)=Map.records rows [] ∧
      (Map.done query ((query,[])::rows) []).data (.inr .reader)≠[] :=by
  constructor
  · simp [Map.done,SemiprimeD1StackOwnerLookup.data,Map.result]
  · constructor
    · simp [Map.done,SemiprimeD1StackOwnerLookup.data,Map.result]
    · simpa only [Map.done,SemiprimeD1StackOwnerLookup.data,Map.result,ite_true] using records_nonempty rows
/-- Every field is nonempty as a byte stream, even when its colour word itself is empty zero. -/
theorem frame_nonempty (word tail:List Bool) :frame word tail≠[] :=by
  cases word <;> intro h <;> cases h
/-- Only actual EOF ends a raw colour stream; a leading false byte still denotes an empty field. -/
theorem serialize_cons_nonempty (word:List Bool) (words:List (List Bool)) :
    SemiprimeD1PacketRows.serialize (word::words)≠[] :=frame_nonempty _ _
/-- Exact per-colour chronological vector-row bytes emitted by the actual frame/reverse logger. -/
def row (word:List Bool) :List Bool :=true::frame word []
/-- Chronological rowsPrefix without a vector terminator, used only in trace specifications. -/
def rowsPrefix (words:List (List Bool)) :List Bool :=words.flatMap row
/-- Literal frame concatenation leaves its supplied physical tail intact. -/
theorem frame_append (word tail suffix:List Bool) :frame word tail++suffix=frame word (tail++suffix) :=by
  induction word with
  | nil=>rfl
  | cons b word ih=>simp only [frame,List.cons_append,ih]
/-- All physical row fragments form the exact old vector codec, including empty colour fields. -/
theorem prefix_vector (words:List (List Bool)) :rowsPrefix words++[false]=vectorBits words :=by
  induction words with
  | nil=>rfl
  | cons word words ih=>
    change (row word++rowsPrefix words)++[false]=true::frame word (vectorBits words)
    rw [List.append_assoc,ih]
    simp only [row,List.cons_append,frame_append,List.nil_append]
/-- One actual reverse-row append extends the complete reverse chronological history exactly. -/
theorem history_succ (old:List (List Bool)) (word:List Bool) :
    (row word).reverse++(rowsPrefix old).reverse=(rowsPrefix (old++[word])).reverse :=by
  simp only [rowsPrefix,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append]
/-- One literal logged field pays every raw word byte and both actual tags. -/
theorem row_length (word:List Bool) :(row word).length=2*word.length+2 :=by
  simp only [row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
end RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
