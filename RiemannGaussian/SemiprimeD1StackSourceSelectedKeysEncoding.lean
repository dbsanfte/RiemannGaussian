/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeys
import RiemannGaussian.SemiprimeSourceHistogramFeatureBits
/-! # Literal selected joint-key ABI and exact physical source banks
The second selected ID is the raw tail of the joint key. Vector framing is
outside that complete joint key. These lists/counts are proof interpretations
of acquired bytes; none is a label, source instruction or runtime callback.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeys
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact normalized original-prefix ID returned by the actual preserving environment lookup. -/
def readID (ids:List (List Bool)) (key:List Bool) :List Bool :=
  SemiprimeSourceHistogramPrefix.expected ids (SemiprimeBitArithmetic.bitValue key)
/-- EXACTold jointBytes(feature2,2): first ID framed, second ID RAWtail, not another framed field. -/
def joint (ids:List (List Bool)) (row:List Bool×List Bool) :List Bool :=
  frame (readID ids row.1) (readID ids row.2)
/-- One complete selected joint key per actual original occurrence, in precisely its original order. -/
def keys (ids:List (List Bool)) (rows:List (List Bool×List Bool)) :List (List Bool) :=rows.map (joint ids)
/-- One physical vector row, logged in reverse before the one final chronological reversal. -/
def chunk (ids:List (List Bool)) (row:List Bool×List Bool) :List Bool :=true::frame (joint ids row) []
/-- Exact chronological key-vector prefix, without its final false terminal. -/
def stream (ids:List (List Bool)) (rows:List (List Bool×List Bool)) :List Bool :=
  rows.foldr (fun row tail=>chunk ids row++tail) []
/-- Reversing the accumulated row log once yields the exact forward vector grammar. -/
theorem stream_vector (ids:List (List Bool)) (rows:List (List Bool×List Bool)) :
    stream ids rows++[false]=vectorBits (keys ids rows) :=by
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    change ((true::frame (joint ids row) [])++stream ids rows)++[false]=_
    rw [List.append_assoc,ih,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
    rfl
/-- Every original occurrence survives; equal keys remain separate vector entries. -/
theorem keys_length (ids:List (List Bool)) (rows:List (List Bool×List Bool)) :(keys ids rows).length=rows.length :=
  List.length_map _
/-- Literal key boundary agrees with the old two-feature producer at actual compact variable keys. -/
theorem joint_original (ids:List (List Bool)) (row:SemiprimeSourceHistogramPortKeys.PortRecord)
    (ho:SemiprimeSourceCompactBits.Compact row.ownerKey) (hf:SemiprimeSourceCompactBits.Compact row.factorKey) :
    joint ids (row.ownerKey,row.factorKey)=SemiprimeSourceHistogramFeatureBits.jointBytes
      (SemiprimeSourceHistogramPrefix.acquire ids).trie 2 2 row :=by
  have h21:(2:SemiprimeSourceIncidenceHistogram.Feature)≠1:=by decide
  simp only [SemiprimeSourceHistogramFeatureBits.jointBytes,SemiprimeSourceHistogramFeatureBits.componentKey,
    h21,ite_false,ite_true]
  rw [SemiprimeSourceHistogramPrefix.stored_eq ids row.ownerKey ho,
    SemiprimeSourceHistogramPrefix.stored_eq ids row.factorKey hf]
  rfl
/-- A selected zero/zero pair has key[false], and its enclosing singleton vector is not empty. -/
theorem zero_key :joint [[]] ([],[])=[false] ∧ vectorBits (keys [[]] [([],[])])=[true,true,false,false,false] :=⟨rfl,rfl⟩
/-- Proof-only names for actual acquired input words; not a runtime mode or list operand. -/
structure Inputs where
  /-- Newest-first selected prefix represented by the actual complete acquired dictionary. -/
  ids:List (List Bool)
  /-- Arbitrary actual chosen-ID word retained from the caller. -/
  chosen:List Bool
  /-- Arbitrary actual caller query is physically saved and restored. -/
  query:List Bool
  /-- Arbitrary actual retained prefix word. -/
  pfx:List Bool
  /-- Actual original ordered owner/factor key pairs, including repeated occurrences. -/
  rows:List (List Bool×List Bool)
/-- Concrete acquired dictionary/cache bank; its20 work/answer fields start empty. -/
def environment (i:Inputs) :SemiprimeD1StackSourceEnvironment.Stack→List Bool :=
  (SemiprimeD1StackSourceEnvironmentExecution.lookupReady i.ids i.chosen i.query i.pfx).data
/-- The retained actual pair stream supplied by the concrete occurrence source. -/
def tape (i:Inputs) :List Bool :=SemiprimeD1StackOwnerLookup.records i.rows []
/-- Complete-cache condition is a theorem-side consequence of selected IDs and actual endpoint ranges. -/
def Complete (i:Inputs) :Prop :=∀row∈i.rows,
  SemiprimeBitArithmetic.bitValue row.1 < i.ids.length ∧ SemiprimeBitArithmetic.bitValue row.2 < i.ids.length
/-- Sole prepared source fields are the physically acquired cache and occurrence tape. -/
def source (i:Inputs) :C.State Stack Label :=initial (environment i) (tape i)
/-- Complete final39-word store retains all25 environment words and original occurrence source. -/
def result (i:Inputs) :Stack→List Bool :=
  Function.update (data (environment i) (tape i)) (aux .output) (vectorBits (keys i.ids i.rows))
/-- Actual whole halt clears both transient flags and real return frames. -/
def done (i:Inputs) :C.State Stack Label :=⟨none,none,none,result i,[]⟩
/-- Own input budget counts actual source/dictionary/key/chosen/query/prefix bytes and a unit allowance. -/
def inputSize (i:Inputs) :Nat :=(tape i).length+
  SemiprimeD1StackSourceEnvironmentBounds.cacheSize i.ids i.chosen i.query i.pfx
/-- The byte budget is physically positive before every source. -/
theorem inputSize_pos (i:Inputs) :0 < inputSize i :=by
  unfold inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  omega
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysEncoding
