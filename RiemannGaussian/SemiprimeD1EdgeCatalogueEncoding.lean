/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1VertexCatalogueEncoding

/-! # Exact descriptor transduction specification for original half edges
These mathematical lists describe the physical parser/emit loops; they are not
runtime graph suppliers or instructions executing an original enumeration.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
open SemiprimeMacroGraph SemiprimeSourceHistogramKeyBits
open SemiprimeD1VertexCatalogueModes
open SemiprimeD1VertexCatalogueEncoding (transformCode)

/-- The five physically cached fields of one vertex descriptor. -/
abbrev Record := Fin 5→List Bool
/-- One literal original mode and its four unary coordinates. -/
def fields (mode:Mode) (i0 i1 i2 i3:ℕ) : Record :=
  ![List.replicate (code mode) true,List.replicate i0 true,List.replicate i1 true,
    List.replicate i2 true,List.replicate i3 true]
/-- Five framed fields, in the actual original descriptor order. -/
def record (words:Record) (tail:List Bool) : List Bool :=
  frame (words 0) (frame (words 1) (frame (words 2) (frame (words 3) (frame (words 4) tail))))
/-- Literal fields for every original arithmetic vertex. -/
def arithmetic {r t digits:ℕ} : Vertex r t digits→Record
  | .input side i => fields .input side.val i.val 0 0
  | .first tr j => fields .first (transformCode tr) j.val 0 0
  | .scale tr j k => fields .scale (transformCode tr) j.val k.val 0
  | .second tr k => fields .second (transformCode tr) k.val 0 0
  | .product i => fields .product i.val 0 0 0
  | .carryInitial => fields .carryInitial 0 0 0 0
  | .carry i => fields .carry i.val 0 0 0
  | .carryTerminal => fields .carryTerminal 0 0 0 0
  | .orGate side i => fields .orGate side.val i.val 0 0
  | .inputCheck side => fields .inputCheck side.val 0 0 0
/-- Literal equality-vertex fields, retaining actual signal and bit coordinates. -/
def bit {r t digits:ℕ} : BitSignal r t digits→Record
  | .inl (.input side i,b) => fields .wordInput side.val i.val b.val 0
  | .inl (.first tr j k,b) => fields .wordFirst (transformCode tr) j.val k.val b.val
  | .inl (.twiddle tr j k,b) => fields .wordTwiddle (transformCode tr) j.val k.val b.val
  | .inl (.second tr k j,b) => fields .wordSecond (transformCode tr) k.val j.val b.val
  | .inl (.product i,b) => fields .wordProduct i.val b.val 0 0
  | .inl (.carry i,b) => fields .wordCarry i.val b.val 0 0
  | .inr (.digit side i) => fields .flagDigit side.val i.val 0 0
  | .inr (.orOut side i) => fields .flagOr side.val i.val 0 0
/-- All actual original descriptor fields. -/
def vertex {r t digits:ℕ} : SubdividedVertex r t digits→Record
  | .inl v => arithmetic v
  | .inr signal => bit signal
/-- The complete parser input tape from literal original descriptors. -/
def tape (records:List Record) (tail:List Bool) : List Bool := records.foldr record tail
/-- Side is acquired physically as an empty or one-marker word. -/
def sideWord (side:Bool) : List Bool := if side then [true] else []
/-- The original half-edge encoding, with a physical side field before its signal descriptor. -/
def half (side:Bool) (words:Record) (tail:List Bool) : List Bool := frame (sideWord side) (record words tail)
/-- Exact original edge descriptor. -/
def edge {r t digits:ℕ} (e:Edge r t digits) (tail:List Bool) : List Bool := half e.2 (bit e.1) tail
/-- Physical ten-marker test selects precisely equality descriptors on original input. -/
abbrev selected (words:Record) : Prop := 10≤(words 0).length
/-- Mathematical output of the actual equality-selector and false/true emitter. -/
def output (records:List Record) (tail:List Bool) : List Bool :=
  records.foldr (fun words rest=>if selected words then half false words (half true words rest) else rest) tail

/-- The actual vertex encoding is exactly the five physically parsed fields. -/
theorem record_vertex {r t digits:ℕ} (v:SubdividedVertex r t digits) (tail:List Bool) :
    record (vertex v) tail=SemiprimeD1VertexCatalogueEncoding.vertex v tail := by
  rcases v with v|v
  · cases v <;> rfl
  · rcases v with ⟨w,b⟩|flag
    · cases w <;> rfl
    · cases flag <;> rfl
/-- Every arithmetic tag fails the actual fixed ten-marker test. -/
theorem arithmetic_not_selected {r t digits:ℕ} (v:Vertex r t digits) : ¬selected (arithmetic v) := by
  cases v <;> simp [selected,arithmetic,fields,code]
/-- Every word/flag equality tag passes the same physical length test. -/
theorem bit_selected {r t digits:ℕ} (signal:BitSignal r t digits) : selected (bit signal) := by
  rcases signal with ⟨w,b⟩|flag
  · cases w <;> simp [selected,bit,fields,code]
  · cases flag <;> simp [selected,bit,fields,code]
/-- Source descriptors are the exact complete original vertex tape. -/
theorem original_input (r t digits:ℕ) (tail:List Bool) :
    tape ((SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values.map vertex) tail=
      SemiprimeD1VertexCatalogueEncoding.catalogue r t digits tail := by
  rw [SemiprimeD1VertexCatalogueEncoding.original_vertices]
  simp only [tape,List.foldr_map,record_vertex]
/-- The exact full original edge order is bit-major, false then true, with all multiplicities. -/
theorem original_output (r t digits:ℕ) (tail:List Bool) :
    output ((SemiprimeMacroFiniteEnumerations.subdividedVertices r t digits).values.map vertex) tail=
      (SemiprimeMacroFiniteEnumerations.edges r t digits).values.foldr edge tail := by
  unfold output
  simp only [List.foldr_map,SemiprimeMacroFiniteEnumerations.subdividedVertices,
    SemiprimeFiniteEnumerations.sum,List.foldr_append,List.foldr_map]
  have ha:∀(vs:List (Vertex r t digits)) rest,
      vs.foldr (fun v acc=>if selected (vertex (.inl v)) then
        half false (vertex (.inl v)) (half true (vertex (.inl v)) acc) else acc) rest=rest:=by
    intro vs rest
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.foldr_cons]
      have hn:¬selected (vertex (.inl v)):=arithmetic_not_selected v
      simp only [ite_eq_right hn]
      exact ih
  rw [ha]
  have hb:∀(s:BitSignal r t digits) (rest:List Bool),
      (if selected (vertex (.inr s)) then half false (vertex (.inr s)) (half true (vertex (.inr s)) rest) else rest)=
        half false (bit s) (half true (bit s) rest):=by
    intro s rest
    rw [ite_eq_left (show selected (vertex (.inr s)) from bit_selected s)]
    rfl
  simp_rw [hb]
  rw [SemiprimeMacroFiniteEnumerations.edges,SemiprimeFiniteEnumerations.prod]
  rw [SemiprimeD1VertexCatalogueEncoding.foldr_product]
  rfl
end RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
