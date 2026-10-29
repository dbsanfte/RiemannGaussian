/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsEncoding
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
/-! # Exact original catalogue meanings for the actual numeric two-ID reader
Only proofs mention the original bank and dictionary. The source still has two
physical words, with no coordinate count or finite-word getter operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsMeaning
open SemiprimeD1StackPacketRowsEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceCompactBits (Compact)
namespace Rows
export SemiprimeSourceHistogramRows (Row layout expected expected_mem original_pair original_nodup)
end Rows
namespace Map
export SemiprimeD1StackOwnerLookup (result records)
end Map
/-- Literal catalogue conversion retains each original key and encoded row. -/
def entries (pairs:List (List Bool×Rows.Row)) :List (List Bool×List Bool) :=
  pairs.map (fun p=>(p.1,Rows.layout p.2))
/-- Numeric first-match equality agrees with the original byte-key trie on actual compact IDs. -/
theorem lookup_expected (pairs:List (List Bool×Rows.Row)) (q:List Bool) (hq:Compact q)
    (hc:∀p∈pairs,Compact p.1) :
    (Map.result q (entries pairs) []).1=Rows.expected pairs q :=by
  induction pairs with
  | nil=>rfl
  | cons p ps ih=>
    rcases p with ⟨k,v⟩
    have hk:=hc (k,v) (List.mem_cons_self)
    have he:(bitValue k=bitValue q) ↔ q=k:=by
      constructor
      · intro h;exact (SemiprimeSourceCompactWordIds.compact_value_injective k q hk hq h).symm
      · intro h;rw [h]
    simp only [entries,List.map_cons,Map.result,Rows.expected,he]
    split_ifs
    · rfl
    · exact ih (fun p hp=>hc p (List.mem_cons_of_mem _ hp))
/-- Actual catalogue membership implies a successful physical presence peek, even for empty payloads. -/
theorem present_mem (rows:List (List Bool×List Bool)) (q value:List Bool) (hm:(q,value)∈rows) :
    present q rows=true :=by
  induction rows with
  | nil=>simp at hm
  | cons p ps ih=>
    rcases p with ⟨k,v⟩
    simp only [present]
    split_ifs with h
    · rfl
    · rcases List.mem_cons.mp hm with he|he
      · cases he;exact (h rfl).elim
      · exact ih he
/-- Encoding rows commutes with the original exact paired inventory. -/
theorem entries_zip (ids:List (List Bool)) (rows:List Rows.Row) :
    entries (ids.zip rows)=ids.zip (rows.map Rows.layout) :=by
  induction ids generalizing rows with
  | nil=>rfl
  | cons id ids ih=>cases rows with
    | nil=>rfl
    | cons row rows=>simp only [List.zip_cons_cons,entries,List.map_cons];rw [←entries,ih]
/-- Original complete radix bank represented by the source's physical catalogue. -/
def originalEntries (r a:Nat) :List (List Bool×List Bool) :=
  entries ((SemiprimeSourceCompactWordBank.acquire r a).ids.zip
    (SemiprimeSourceCompactWordBank.acquire r a).rows)
/-- Exact original palette fields physically serialized by the original bank row. -/
def fields (r a:Nat) (id:List Bool) :List (List Bool) :=
  (SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r a) id).value.map
    (fun x=>(SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits)
/-- Both the actual lookup payload and the physical unread-reader presence witness come from the original acquired row. -/
theorem original_lookup (r a:Nat) [NeZero r] (id:List Bool)
    (hi:id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    (Map.result id (originalEntries r a) []).1=SemiprimeD1PacketRows.serialize (fields r a id) ∧
      present id (originalEntries r a)=true ∧ (fields r a id).length=a :=by
  let pairs:=(SemiprimeSourceCompactWordBank.acquire r a).ids.zip
    (SemiprimeSourceCompactWordBank.acquire r a).rows
  have hc:∀p∈pairs,Compact p.1:=by
    intro p hp
    apply SemiprimeSourceCompactWordBank.ids_compact r a p.1
    exact (List.of_mem_zip hp).1
  have hp:=Rows.original_pair r a id hi
  have he:=lookup_expected pairs id (SemiprimeSourceCompactWordBank.ids_compact r a id hi) hc
  rw [Rows.expected_mem _ _ _ (Rows.original_nodup r a) hp] at he
  refine ⟨?_,?_,?_⟩
  · change _=SemiprimeD1PacketRows.serialize
      ((SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r a) id).value.map _)
    rw [SemiprimeD1PacketRows.serialize_row]
    exact he
  · exact present_mem _ id _ (List.mem_map.mpr ⟨_,hp,rfl⟩)
  · exact (List.length_map ..).trans (SemiprimeSourceCompactWordBank.readRow_length r a id hi)
/-- The no-count physical reader and the old fixed-width parser produce the identical fields. -/
theorem fields_original (r a:Nat) [NeZero r] (id:List Bool)
    (hi:id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    fields r a id=(SemiprimeD1PacketRows.parse a (SemiprimeSourceHistogramRows.readRow
      (SemiprimeSourceHistogramRows.acquire r a) id).bits).fields :=by
  rw [SemiprimeSourceHistogramRows.lookup_original r a id hi,SemiprimeSourceHistogramRows.encodeRow_bits]
  have hp:=SemiprimeD1PacketRows.parse_row
    (SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r a) id).value
  rw [SemiprimeSourceCompactWordBank.readRow_length r a id hi] at hp
  exact hp.1.symm
/-- Catalogue output is precisely the actually executed frozen alphabet source's stopped word. -/
theorem catalogue_original (a:Nat) :
    SemiprimeD1StackOwnerLookup.records (originalEntries 64 a) []=
      SemiprimeD1StackSourceAlphabet64Encoding.result a (SemiprimeD1StackSourceAlphabet64.aux .output) :=by
  rw [SemiprimeD1StackSourceAlphabet64Original.output_original]
  rw [originalEntries,entries_zip]
  rfl
end RiemannGaussian.SemiprimeD1StackPacketRowsMeaning
