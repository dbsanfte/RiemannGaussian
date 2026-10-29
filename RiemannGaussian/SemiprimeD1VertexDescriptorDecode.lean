/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
/-! # Proof-side exact inverse for actual original vertex descriptors
This inverse licenses uniqueness of physical endpoint-key lookup. It is NOT
executed as a native graph/owner oracle by the forthcoming finite machine.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1VertexDescriptorDecode
open SemiprimeMacroGraph
open SemiprimeD1EdgeCatalogueEncoding
/-- Total proof-side bounded coordinate decoder. -/
def fin (n k:ℕ) : Option (Fin n) := if h:k<n then some ⟨k,h⟩ else none
/-- Every actual finite coordinate decodes identically. -/
@[simp] theorem fin_val {n:ℕ} (i:Fin n) : fin n i.val=some i := by simp [fin,i.isLt]
/-- Total proof-side decoder of the actual three transform tags. -/
def transform (k:ℕ) : Option Transform :=
  if h:k<2 then some (.inl ⟨k,h⟩) else if k=2 then some (.inr ()) else none
/-- Each actual transform code is decoded without an ordering premise. -/
@[simp] theorem transform_code (tr:Transform) :
    transform (SemiprimeD1VertexCatalogueEncoding.transformCode tr)=some tr := by
  cases tr with
  | inl side => simp [transform,SemiprimeD1VertexCatalogueEncoding.transformCode,side.isLt]
  | inr u => cases u;rfl
/-- Literal finite constructor reconstruction, used only in semantic uniqueness proofs. -/
def numbers (r t digits code a b c d:ℕ) : Option (SubdividedVertex r t digits) :=
  match code with
  | 0 => do let s←fin 2 a;let i←fin (r*t) b;pure (.inl (.input s i))
  | 1 => do let tr←transform a;let j←fin r b;pure (.inl (.first tr j))
  | 2 => do let tr←transform a;let j←fin r b;let k←fin t c;pure (.inl (.scale tr j k))
  | 3 => do let tr←transform a;let k←fin t b;pure (.inl (.second tr k))
  | 4 => do let i←fin (r*t) a;pure (.inl (.product i))
  | 5 => pure (.inl .carryInitial)
  | 6 => do let i←fin (r*t) a;pure (.inl (.carry i))
  | 7 => pure (.inl .carryTerminal)
  | 8 => do let s←fin 2 a;let i←fin (digits-1) b;pure (.inl (.orGate s i))
  | 9 => do let s←fin 2 a;pure (.inl (.inputCheck s))
  | 10 => do let s←fin 2 a;let i←fin (r*t) b;let bit←fin (r*t+1) c;pure (.inr (.inl (.input s i,bit)))
  | 11 => do let tr←transform a;let j←fin r b;let k←fin t c;let bit←fin (r*t+1) d;pure (.inr (.inl (.first tr j k,bit)))
  | 12 => do let tr←transform a;let j←fin r b;let k←fin t c;let bit←fin (r*t+1) d;pure (.inr (.inl (.twiddle tr j k,bit)))
  | 13 => do let tr←transform a;let k←fin t b;let j←fin r c;let bit←fin (r*t+1) d;pure (.inr (.inl (.second tr k j,bit)))
  | 14 => do let i←fin (r*t) a;let bit←fin (r*t+1) b;pure (.inr (.inl (.product i,bit)))
  | 15 => do let i←fin (r*t+1) a;let bit←fin (r*t+1) b;pure (.inr (.inl (.carry i,bit)))
  | 16 => do let s←fin 2 a;let i←fin digits b;pure (.inr (.inr (.digit s i)))
  | 17 => do let s←fin 2 a;let i←fin (digits-1) b;pure (.inr (.inr (.orOut s i)))
  | _ => none
/-- Physical descriptor words are interpreted by their actual unary lengths, for proofs only. -/
def decode (r t digits:ℕ) (words:Record) : Option (SubdividedVertex r t digits) :=
  numbers r t digits (words 0).length (words 1).length (words 2).length (words 3).length (words 4).length
/-- Every actual original vertex has exactly its literal tag/coordinate descriptor. -/
theorem decode_vertex {r t digits:ℕ} (v:SubdividedVertex r t digits) :
    decode r t digits (vertex v)=some v := by
  cases v with
  | inl v => cases v <;> simp [decode,vertex,arithmetic,fields,numbers,SemiprimeD1VertexCatalogueModes.code]
  | inr signal =>
    cases signal with
    | inl pair =>
      rcases pair with ⟨word,b⟩
      cases word <;> simp [decode,vertex,SemiprimeD1EdgeCatalogueEncoding.bit,fields,numbers,SemiprimeD1VertexCatalogueModes.code]
    | inr flag => cases flag <;> simp [decode,vertex,SemiprimeD1EdgeCatalogueEncoding.bit,fields,numbers,SemiprimeD1VertexCatalogueModes.code]
/-- Physical descriptor equality cannot alias two original vertices. -/
theorem vertex_injective (r t digits:ℕ) : Function.Injective (vertex (r:=r) (t:=t) (digits:=digits)) := by
  intro v w h
  have hd:=congrArg (decode r t digits) h
  rw [decode_vertex,decode_vertex] at hd
  exact Option.some.inj hd
end RiemannGaussian.SemiprimeD1VertexDescriptorDecode
