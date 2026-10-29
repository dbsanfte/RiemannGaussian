/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecord
/-! # Exact five-field original descriptor byte grammar and parser invariants -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- The actual five original catalogue fields, retaining all four coordinates. -/
abbrev Record := SemiprimeD1EdgeCatalogueEncoding.Record
/-- Literal physical suffix after n of the five framed fields. -/
def suffix (w : Record) (n : Nat) (tail : List Bool) : List Bool :=
  ((List.ofFn w).drop n).foldr frame tail
/-- Unchanged original descriptor format, without a row tag or extra terminator. -/
def record (w : Record) (tail : List Bool) : List Bool := suffix w 0 tail
/-- Actual cached prefix of the fixed physical parser. -/
def parsed (n : Nat) (w : Record) : Record := fun k=>if k.val<n then w k else []
/-- Physical payload mass of the descriptor, excluding framing cells. -/
def mass (w : Record) : Nat := ((List.ofFn w).map List.length).sum
/-- Each real field read exposes exactly its cached payload and the next suffix. -/
theorem suffix_step (w : Record) (part : Fin 5) (tail : List Bool) :
    suffix w part.val tail=frame (w part) (suffix w (part.val+1) tail) := by fin_cases part <;> rfl
/-- Five real reads leave the exact caller suffix. -/
theorem suffix_end (w : Record) (tail : List Bool) : suffix w 5 tail=tail := rfl
/-- One actual cache write advances the finite parsed-prefix invariant. -/
theorem parsed_step (w : Record) (part : Fin 5) :
    Function.update (parsed part.val w) part (w part)=parsed (part.val+1) w := by
  funext k;fin_cases part <;> fin_cases k <;> rfl
/-- All five original field bytes, including empty coordinates, are retained. -/
theorem parsed_end (w : Record) : parsed 5 w=w := by funext k;fin_cases k <;> rfl
/-- This grammar is byte-for-byte the existing original descriptor format. -/
theorem record_original (w : Record) (tail : List Bool) :
    record w tail=SemiprimeD1EdgeCatalogueEncoding.record w tail := rfl
/-- No new encoding or original vertex reconstruction executes. -/
theorem record_vertex {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits) (tail : List Bool) :
    record (SemiprimeD1EdgeCatalogueEncoding.vertex v) tail=
      SemiprimeD1VertexCatalogueEncoding.vertex v tail :=
  SemiprimeD1EdgeCatalogueEncoding.record_vertex v tail
/-- Actual tag bytes are part of the physical descriptor payload. -/
theorem tag_length_le_mass (w : Record) : (w 0).length ≤ mass w := by
  change (w 0).length≤(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+0))))
  omega
/-- Every data, marker and delimiter byte is included. -/
theorem record_length (w : Record) (tail : List Bool) :
    (record w tail).length=2*mass w+5+tail.length := by
  change (frame (w 0) (frame (w 1) (frame (w 2) (frame (w 3) (frame (w 4) tail))))).length=_
  simp only [frame_length]
  change _=2*((w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+0)))))+5+tail.length
  omega
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordEncoding
