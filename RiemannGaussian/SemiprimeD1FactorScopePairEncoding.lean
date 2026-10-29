/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairs
/-! # Exact nine-field input and factor-key/scope-ID pair byte specifications -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1FactorScopePairEncoding
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- Nine actual parsed fields, scope ID at0 and unchanged factor ordinal at2. -/
abbrev Record := Fin 9→List Bool
/-- Proof-only list view of the fixed nine physical input fields. -/
def fields (w : Record) : List (List Bool) := List.ofFn w
/-- Input suffix after a fixed number of actual field parses. -/
def suffix (w : Record) (n : Nat) (tail : List Bool) : List Bool :=
  ((fields w).drop n).foldr frame tail
/-- Exact source input record, without any artificial row tag. -/
def record (w : Record) (tail : List Bool) : List Bool := suffix w 0 tail
/-- EOF-terminated source stream, preserving original factor-major order. -/
def stream (rows : List Record) (tail : List Bool) : List Bool := rows.foldr record tail
/-- Actual original port plus actual acquired scope ID in authoritative order. -/
def joined (w : SemiprimeD1PortScopeEncoding.Port) (id : List Bool) : Record :=
  ![id,w 0,w 1,w 2,w 3,w 4,w 5,w 6,w 7]
/-- Literal source grammar agrees exactly with the fixed nine-field parser. -/
theorem joined_record (w : SemiprimeD1PortScopeEncoding.Port) (id tail : List Bool) :
    record (joined w id) tail=SemiprimeD1PortScopeEncoding.scopeFrame w id tail := rfl
/-- The ordered source output is exactly the zipped nine-field stream. -/
theorem joined_stream (ports : List SemiprimeD1PortScopeEncoding.Port) (ids : List (List Bool)) (tail : List Bool) :
    stream (List.zipWith joined ports ids) tail=SemiprimeD1PortScopeEncoding.output ports ids tail := by
  induction ports generalizing ids with
  | nil=>rfl
  | cons w ws ih=>cases ids with
    | nil=>rfl
    | cons id ids=>
      change record (joined w id) (stream (List.zipWith joined ws ids) tail)=_
      rw [joined_record,ih]
      rfl
/-- Every fixed parser step exposes precisely the next actual framed field. -/
theorem suffix_step (w : Record) (part : Fin 9) (tail : List Bool) :
    suffix w part.val tail=frame (w part) (suffix w (part.val+1) tail) := by fin_cases part <;> rfl
/-- All nine physical input fields consumed leaves the exact source suffix. -/
theorem suffix_end (w : Record) (tail : List Bool) : suffix w 9 tail=tail := rfl
/-- Key and scope are unchanged physical payloads, never recoded ordinals. -/
def pair (w : Record) : List Bool×List Bool := (w 2,w 0)
/-- Exact tagged two-field row before the one final false catalogue terminator. -/
def row (w : Record) : List Bool := true::frame (w 2) (frame (w 0) [])
/-- Forward row bytes used by the single final physical reversal. -/
def raw (rows : List Record) : List Bool := rows.foldr (fun w tail=>row w++tail) []
/-- Literal pair catalogue is the generic owner-fibre input grammar. -/
theorem raw_records (rows : List Record) (tail : List Bool) :
    raw rows++false::tail=SemiprimeD1StackOwnerFibre.records (rows.map pair) tail := by
  induction rows with
  | nil=>rfl
  | cons w rows ih=>
    change (row w++raw rows)++false::tail=true::frame (w 2)
      (frame (w 0) (SemiprimeD1StackOwnerFibre.records (rows.map pair) tail))
    rw [List.append_assoc,ih]
    simp only [row,List.cons_append]
    rw [←SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 2),
      ←SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 0)]
    rfl
/-- Actual byte payload mass of all nine input fields. -/
def mass (w : Record) : Nat := ((fields w).map List.length).sum
/-- Every input marker, data byte and field delimiter is counted. -/
theorem record_length (w : Record) (tail : List Bool) : (record w tail).length=2*mass w+9+tail.length := by
  have h (xs : List (List Bool)) : (xs.foldr frame tail).length=2*(xs.map List.length).sum+xs.length+tail.length := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>simp only [List.foldr_cons,frame_length,List.map_cons,List.sum_cons,List.length_cons,ih];omega
  simpa only [record,suffix,List.drop_zero,mass,fields,List.length_ofFn,Fintype.card_fin] using h (fields w)
end RiemannGaussian.SemiprimeD1FactorScopePairEncoding
