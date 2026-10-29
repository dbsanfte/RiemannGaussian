/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityOriginal

/-! # Exact factor-major original port descriptors and physical ordinal counters
The native lists in this file are specifications only. The actual producer
parses the original tape, acquires each arity, and pushes every counter marker.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PortCatalogueEncoding
open SemiprimeMacroGraph
open SemiprimeD1EdgeCatalogueEncoding (Record record)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame frame_length)

/-- Eight actual fields; occurrence/factor/local ordinals remain control metadata.
The common-width binary scope-ID bank is a separate, consistent subsequent read. -/
def encode (occurrence factor slot:ℕ) (words:Record) (tail:List Bool) : List Bool :=
  frame (unary occurrence) (frame (unary factor) (frame (unary slot) (record words tail)))
/-- Total word payload, before the eight physical framing delimiters. -/
def mass (occurrence factor slot:ℕ) (words:Record) : ℕ :=
  occurrence+factor+slot+SemiprimeD1StackEdgeCatalogueParse.wordMass words
/-- Actual per-port framed byte size. -/
theorem encode_length (occurrence factor slot:ℕ) (words:Record) (tail:List Bool) :
    (encode occurrence factor slot words tail).length=2*mass occurrence factor slot words+tail.length+8 := by
  unfold encode mass
  simp only [frame_length,SemiprimeD1StackEdgeCatalogueScan.record_length,unary,List.length_replicate]
  omega
/-- Exact local-slot order: zero first, ascending through the actually acquired arity. -/
def slots (arity occurrence factor:ℕ) (words:Record) (tail:List Bool) : List Bool :=
  (List.range arity).foldr (fun slot rest=>encode (occurrence+slot) factor slot words rest) tail
/-- Actual factor-major descriptor specification, including zero-arity factors in its factor counter. -/
def fromVertices {r t digits:ℕ} : List (SubdividedVertex r t digits)→ℕ→ℕ→List Bool→List Bool
  | [],_,_,tail => tail
  | v::vs,factor,occurrence,tail =>
      slots (subdividedArity v) occurrence factor (SemiprimeD1EdgeCatalogueEncoding.vertex v)
        (fromVertices vs (factor+1) (occurrence+subdividedArity v) tail)
/-- Literal number of actual port occurrences in those original factors. -/
def occurrences {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) : ℕ :=
  (vs.map subdividedArity).sum
/-- Complete original family, retaining both arithmetic and equality factors. -/
def catalogue (r t digits:ℕ) (tail:List Bool) : List Bool :=
  fromVertices (SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values 0 0 tail
/-- Exact source-flat-list port count, without treating serialized bytes as graph size. -/
theorem original_count (r t digits:ℕ) :
    occurrences (SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values=
      (SemiprimeMacroFiniteEnumerations.incidences r t digits).values.length := by
  unfold occurrences SemiprimeMacroFiniteEnumerations.incidences SemiprimeFiniteEnumerations.sigma
  simp only [List.length_flatMap,List.length_map]
  congr 1
  apply List.map_congr_left
  intro v _
  exact (SemiprimeFiniteEnumerations.fin_length (subdividedArity v)).symm
end RiemannGaussian.SemiprimeD1PortCatalogueEncoding
