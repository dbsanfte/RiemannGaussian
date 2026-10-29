/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceAcquisitionBounds
import RiemannGaussian.SemiprimeD1OrientationForward
import RiemannGaussian.SemiprimeD1OrientationInverseBounds

/-! # Physical row reads for retained D1 pair keys
The executed reader splits the acquired pair ID once, performs two actual row
trie reads and parses each colour field once. It contains no finite-word getter.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketRows
open SemiprimeSourceHistogramKeyBits

/-- Parsed colour bytes and all physical parser reports. -/
structure Parsed where
  /-- Actual parsed compact-colour payloads in coordinate order. -/
  fields : List (List Bool)
  /-- Actual complete-parse flag, including the empty terminal tail. -/
  valid : Bool
  /-- Retained parser/read/copy and finite-control reports. -/
  clock : ℕ

/-- Parse exactly the original coordinate count, rejecting truncated fields. -/
def parse : ℕ → List Bool → Parsed
  | 0,bs => ⟨[],bs.isEmpty,2⟩
  | a+1,bs =>
    let field := split bs
    if field.valid then
      let tail := parse a field.rest
      ⟨field.first::tail.fields,tail.valid,field.clock+tail.clock+5⟩
    else ⟨[],false,field.clock+3⟩

/-- Literal framing of a finite list of acquired colour fields. -/
def serialize : List (List Bool) → List Bool
  | [] => []
  | x::xs => frame x (serialize xs)

/-- Every field of an acquired well-formed payload is read exactly. -/
theorem parse_serialize (xs : List (List Bool)) :
    (parse xs.length (serialize xs)).fields=xs ∧
      (parse xs.length (serialize xs)).valid=true := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simp only [List.length_cons,serialize,parse,split_frame,ite_true,ih.1,ih.2]
    simp

/-- The original row serializer uses exactly its physically trimmed magnitudes. -/
theorem serialize_row (row : SemiprimeSourceHistogramRows.Row) :
    serialize (row.map (fun x => (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits))=
      SemiprimeSourceHistogramRows.layout row := by
  induction row with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,serialize,SemiprimeSourceHistogramRows.layout,ih]

/-- Actual pair-row read, retaining split/read/parse reports. -/
structure PairRows where
  /-- Parsed original owner-colour row. -/
  left : List (List Bool)
  /-- Parsed original factor-colour row. -/
  right : List (List Bool)
  /-- Actual complete-parse flag, including the empty terminal tail. -/
  valid : Bool
  /-- Retained parser/read/copy and finite-control reports. -/
  clock : ℕ

/-- Read only the selected IDs encoded in the actual pair key. -/
def read (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (key : List Bool) : PairRows :=
  let ids := split key
  let lbytes := SemiprimeSourceHistogramRows.readRow dict ids.first
  let rbytes := SemiprimeSourceHistogramRows.readRow dict ids.rest
  let left := parse a lbytes.bits
  let right := parse a rbytes.bits
  ⟨left.fields,right.fields,ids.valid && left.valid && right.valid,
    ids.clock+lbytes.clock+rbytes.clock+left.clock+right.clock+9⟩

/-- Exact physical read semantics; all three acquisitions are literal calls. -/
theorem read_frame (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (leftId rightId : List Bool) :
    (read dict a (frame leftId rightId)).left=
      (parse a (SemiprimeSourceHistogramRows.readRow dict leftId).bits).fields ∧
    (read dict a (frame leftId rightId)).right=
      (parse a (SemiprimeSourceHistogramRows.readRow dict rightId).bits).fields := by
  simp only [read,split_frame]
  simp

/-- Original physical row output, not a supplied native colour function. -/
theorem parse_row (row : SemiprimeSourceHistogramRows.Row) :
    (parse row.length (SemiprimeSourceHistogramRows.layout row)).fields=
      row.map (fun x => (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits) ∧
    (parse row.length (SemiprimeSourceHistogramRows.layout row)).valid=true := by
  have h := parse_serialize
    (row.map (fun x => (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits))
  simpa only [List.length_map,serialize_row] using h

/-- Physical fields of an actual acquired row are the canonical palette bytes. -/
theorem original_fields (r a : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    (parse a (SemiprimeSourceHistogramRows.readRow
      (SemiprimeSourceHistogramRows.acquire r a) id).bits).fields=
      SemiprimeD1OrientationPalette.fields (SemiprimeSourceWordBankSemantics.decode r a id) ∧
    (parse a (SemiprimeSourceHistogramRows.readRow
      (SemiprimeSourceHistogramRows.acquire r a) id).bits).valid=true := by
  rw [SemiprimeSourceHistogramRows.lookup_original r a id hi,
    SemiprimeSourceHistogramRows.encodeRow_bits]
  let row := (SemiprimeSourceWordBank.readRow (SemiprimeSourceCompactWordBank.acquire r a) id).value
  have hlen := SemiprimeSourceCompactWordBank.readRow_length r a id hi
  change row.length=a at hlen
  have hp := parse_row row
  rw [hlen] at hp
  change (parse a (SemiprimeSourceHistogramRows.layout row)).fields=_ ∧
    (parse a (SemiprimeSourceHistogramRows.layout row)).valid=true
  rw [hp.1,hp.2]
  refine ⟨?_,rfl⟩
  have hvals := SemiprimeSourceHistogramRowKeys.original_colour_values r a id hi
  change row.map _=_ at hvals
  apply List.ext_getElem
  · simp only [List.length_map,SemiprimeD1OrientationPalette.fields,List.length_ofFn,hlen]
  · intro i h₁ h₂
    have hiv : i<a := by simpa only [SemiprimeD1OrientationPalette.fields,List.length_ofFn] using h₂
    have hrow : i<row.length := by omega
    have hv := congrArg (fun xs : List ℚ => xs[i]?) hvals
    simp only [List.getElem?_map, List.getElem?_eq_getElem hrow,
      Option.map_some,SemiprimeSourceWordBankRows.coordinates,
      List.getElem?_ofFn] at hv
    simp only [hiv, ↓reduceDIte,Option.some.injEq] at hv
    simp only [List.getElem_map,SemiprimeD1OrientationPalette.fields,List.getElem_ofFn]
    apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
      (SemiprimeSourceCompactBits.trim_compact _)
      (SemiprimeSourceHistogramHeadRefinement.numberKey_compact _)
    rw [SemiprimeSourceHistogramHeadRefinement.numberKey_value]
    exact_mod_cast hv

/-- Every parser prefix has at most the requested number of physical fields. -/
theorem parse_length (a : ℕ) (bs : List Bool) : (parse a bs).fields.length≤a := by
  induction a generalizing bs with
  | zero => simp only [parse,List.length_nil,Nat.zero_le]
  | succ a ih =>
    simp only [parse]
    split_ifs
    · simpa only [List.length_cons,Nat.add_le_add_iff_right] using ih _
    · simp

/-- Parser fields are actual bounded slices of the original acquired payload. -/
theorem parse_fields_bound (a : ℕ) (bs : List Bool) :
    ∀ field∈(parse a bs).fields,field.length≤bs.length := by
  induction a generalizing bs with
  | zero => simp [parse]
  | succ a ih =>
    intro field hf
    simp only [parse] at hf
    split_ifs at hf
    · rcases List.mem_cons.mp hf with he|he
      · subst field
        exact (SemiprimeD1OrientationInverseBounds.split_metrics bs).1
      · exact le_trans (ih _ field he) (SemiprimeD1OrientationInverseBounds.split_metrics bs).2.1
    · simp at hf

/-- Paid one-pass field parsing, including malformed/truncated input branches. -/
theorem parse_clock (a : ℕ) (bs : List Bool) :
    (parse a bs).clock≤(a+1)*(6*bs.length+8) := by
  induction a generalizing bs with
  | zero => simp only [parse];omega
  | succ a ih =>
    have hs := SemiprimeD1OrientationInverseBounds.split_metrics bs
    have ht := ih (split bs).rest
    simp only [parse]
    split_ifs <;> dsimp only
    · nlinarith
    · nlinarith

/-- Actual row dictionary reads and parser reports have a polynomial byte bound.
The hypotheses bound literal stored payloads, not semantic row answers. -/
theorem read_clock (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (key : List Bool) (B : ℕ)
    (hl : (SemiprimeSourceHistogramTrie.stored dict.trie (split key).first).length≤B)
    (hr : (SemiprimeSourceHistogramTrie.stored dict.trie (split key).rest).length≤B) :
    (read dict a key).clock≤22*key.length+6*B+2*(a+1)*(6*B+8)+40 := by
  have hs := SemiprimeD1OrientationInverseBounds.split_metrics key
  have hcl := SemiprimeSourceHistogramTrieBounds.lookup_clock dict.trie (split key).first B hl
  have hcr := SemiprimeSourceHistogramTrieBounds.lookup_clock dict.trie (split key).rest B hr
  have hpl := parse_clock a (SemiprimeSourceHistogramRows.readRow dict (split key).first).bits
  have hpr := parse_clock a (SemiprimeSourceHistogramRows.readRow dict (split key).rest).bits
  have hll : (SemiprimeSourceHistogramRows.readRow dict (split key).first).bits.length≤B := by
    simpa only [SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits] using hl
  have hrl : (SemiprimeSourceHistogramRows.readRow dict (split key).rest).bits.length≤B := by
    simpa only [SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits] using hr
  change (split key).clock+_+_+_+_+9≤_
  simp only [SemiprimeSourceHistogramRows.readRow] at hpl hpr hll hrl ⊢
  nlinarith

end RiemannGaussian.SemiprimeD1PacketRows
