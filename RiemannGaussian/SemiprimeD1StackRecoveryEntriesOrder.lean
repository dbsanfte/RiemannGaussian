/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesLogger
/-! # Exact physical four-field stream order under actual reversed history
Only byte-concatenation identities occur here; all runtime construction is by
the actual Frame and ReverseWord traces, not a native append/output opcode.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesOrder
open SemiprimeD1StackRecoveryEntriesEncoding
open SemiprimeD1StackRecoveryEntriesLogger (chunk payload)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row)
open SemiprimeSourceHistogramKeyBits (frame)
/-- A physically framed word preserves the literal acquired unread tail. -/
theorem frame_append (word left right:List Bool):frame word (left++right)=frame word left++right:=by
  induction word with
  | nil=>rfl
  | cons bit word ih=>simp only [frame,List.cons_append,ih]
/-- All four actual output fields preserve the literal record tail. -/
theorem fields_append (entry:Entry) (left right:List Bool):fields entry (left++right)=fields entry left++right:=by
  simp only [fields,frame_append]
/-- Literal entry fields are exactly the four words acquired from the real input/read stages. -/
theorem payload_entry (children:List (List (List Bool))) (r:Row):payload r (selectedChild children (r 0) (r 1))=entry children r:=rfl
/-- Actual source chunks in original row order, described only as mathematical bytes. -/
def chunks (children:List (List (List Bool))):List Row → List Bool
  | []=>[]
  | r::rs=>chunk r (selectedChild children (r 0) (r 1))++chunks children rs
/-- One physical true-marker chunk prepends exactly its four actual frames to the unread output tail. -/
theorem chunk_tail (r:Row) (child tail:List Bool):
    true::fields (payload r child) tail=chunk r child++tail:=by
  have h:=fields_append (payload r child) [] tail
  simp only [List.nil_append] at h
  rw [h]
  rfl
/-- Final actual reverse plus false sentinel has exactly the specified whole entry tape bytes. -/
theorem output_chunks (rows:List Row) (children:List (List (List Bool))):
    outputTape rows children=chunks children rows++[false]:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih=>
    change true::fields (entry children r) (outputTape rs children)=_
    rw [←payload_entry,chunk_tail,ih]
    simp only [chunks,List.append_assoc]
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesOrder
