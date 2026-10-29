/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeRecords
/-! # Literal original port/ID stream specification
All list constructors here are proof specifications. The fixed physical
machine parses the actual retained tapes and never consumes these lists as
an advised enumeration or output answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PortScopeEncoding
open SemiprimeSourceHistogramKeyBits (frame frame_length)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeMacroGraph
/-- The existing eight actually serialized original port fields. -/
abbrev Port := Fin 8→List Bool
/-- Literal eight-field input record, preserving empty first ordinal zero. -/
def portFrame (w:Port) (tail:List Bool) : List Bool :=
  frame (w 0) (frame (w 1) (frame (w 2) (frame (w 3)
    (frame (w 4) (frame (w 5) (frame (w 6) (frame (w 7) tail)))))))
/-- Literal original port tape, without any extra record marker. -/
def portTape (ports:List Port) (tail:List Bool) : List Bool := ports.foldr portFrame tail
/-- Actual scope ID precedes every unchanged original port field. -/
def scopeFrame (w:Port) (id tail:List Bool) : List Bool := frame id (portFrame w tail)
/-- Exact physical cache after reading the eight port fields and one actual ID. -/
def cached (w:Port) (id:List Bool) (j:Fin 9) : List Bool :=
  if h:j.val<8 then w ⟨j.val,h⟩ else id
/-- The ID field in the real finite cache is exactly the parsed physical word. -/
theorem cached_id (w:Port) (id:List Bool) : cached w id 8=id := rfl
/-- Every original port field remains byte-for-byte in its old cache position. -/
theorem cached_port (w:Port) (id:List Bool) (j:Fin 8) :
    cached w id ⟨j.val,by omega⟩=w j := by simp [cached,j.isLt]
/-- Exact zipped output, only asserted for equally long actual source streams. -/
def output : List Port→List (List Bool)→List Bool→List Bool
  | w::ws,id::ids,tail => scopeFrame w id (output ws ids tail)
  | _,_,tail => tail
/-- The actual eight-field byte mass. -/
def portMass (w:Port) : ℕ :=
  (w 0).length+(w 1).length+(w 2).length+(w 3).length+
    (w 4).length+(w 5).length+(w 6).length+(w 7).length
/-- Exact input bytes, including all eight physical terminators. -/
theorem portFrame_length (w:Port) (tail:List Bool) :
    (portFrame w tail).length=2*portMass w+tail.length+8 := by
  unfold portFrame portMass
  simp only [frame_length]
  omega
/-- Appended port suffixes are preserved literally. -/
theorem portFrame_append (w:Port) (tail:List Bool) : portFrame w tail=portFrame w []++tail := by
  unfold portFrame
  rw [SemiprimeD1StackEdgeCatalogueEmit.frame_append (w 7) tail,
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 6),SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 5),
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 4),SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 3),
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 2),SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 1),
    SemiprimeD1StackEdgeCatalogueEmit.frame_tail (w 0)]
/-- Scope-record framing preserves every actual tail bit. -/
theorem scopeFrame_append (w:Port) (id tail:List Bool) : scopeFrame w id tail=scopeFrame w id []++tail := by
  unfold scopeFrame
  rw [portFrame_append,SemiprimeD1StackEdgeCatalogueEmit.frame_tail]
/-- Source tape concatenation is exactly list concatenation, including duplicates. -/
theorem portTape_append (xs ys:List Port) (tail:List Bool) :
    portTape (xs++ys) tail=portTape xs (portTape ys tail) := by
  simp only [portTape,List.foldr_append]
/-- Literal fields physically emitted by the frozen original port loop. -/
def fields (words:SemiprimeD1EdgeCatalogueEncoding.Record) (n f slot:ℕ) : Port :=
  SemiprimeD1StackPortCatalogueEmit.sourceField words (unary slot) (unary f) (unary n)
/-- Existing original emission and the eight-field input format are identical. -/
theorem fields_frame (words:SemiprimeD1EdgeCatalogueEncoding.Record) (n f slot:ℕ) (tail:List Bool) :
    portFrame (fields words n f slot) tail=
      SemiprimeD1StackPortCatalogueEmit.record8 words (unary slot) (unary f) (unary n) tail := rfl
/-- Actual local-slot/occurrence order, as mathematical records only. -/
def localPorts (words:SemiprimeD1EdgeCatalogueEncoding.Record) : ℕ→ℕ→ℕ→ℕ→List Port
  | 0,_,_,_ => []
  | fuel+1,n,f,slot => fields words n f slot::localPorts words fuel (n+1) f (slot+1)
/-- Exact source occurrence count at every local-loop prefix. -/
theorem localPorts_length (words:SemiprimeD1EdgeCatalogueEncoding.Record) (fuel n f slot:ℕ) :
    (localPorts words fuel n f slot).length=fuel := by
  induction fuel generalizing n slot with
  | zero => rfl
  | succ fuel ih => simp only [localPorts,List.length_cons,ih]
/-- The mathematical record list is the SAME actual old emitted tape, without an ordering assumption. -/
theorem localPorts_tape (words:SemiprimeD1EdgeCatalogueEncoding.Record) (fuel n f slot:ℕ) (tail:List Bool) :
    portTape (localPorts words fuel n f slot) tail=
      SemiprimeD1StackPortCatalogueLoop.records words fuel n f slot tail := by
  induction fuel generalizing n slot with
  | zero => rfl
  | succ fuel ih =>
    change portFrame (fields words n f slot) (portTape (localPorts words fuel (n+1) f (slot+1)) tail)=_
    rw [ih,fields_frame]
    rfl
/-- Exact factor-major original port list, retaining zero-arity factors in its factor ordinal. -/
def ports {r t digits:ℕ} : List (SubdividedVertex r t digits)→ℕ→ℕ→List Port
  | [],_,_ => []
  | v::vs,f,n => localPorts (SemiprimeD1EdgeCatalogueEncoding.vertex v) (subdividedArity v) n f 0++
      ports vs (f+1) (n+subdividedArity v)
/-- Every actual original port occurs once in this exact ordered specification. -/
theorem ports_length {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (f n:ℕ) :
    (ports vs f n).length=SemiprimeD1StackPortCatalogueTransduction.count vs := by
  induction vs generalizing f n with
  | nil => rfl
  | cons v vs ih => simp only [ports,List.length_append,localPorts_length,ih,
      SemiprimeD1StackPortCatalogueTransduction.count,List.map_cons,List.sum_cons]
/-- Full source tape is exactly the already-proved original factor-major physical output. -/
theorem ports_tape {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (f n:ℕ) (tail:List Bool) :
    portTape (ports vs f n) tail=SemiprimeD1StackPortCatalogueTransduction.output vs f n tail := by
  induction vs generalizing f n with
  | nil => rfl
  | cons v vs ih => rw [ports,portTape_append,ih,localPorts_tape];rfl
end RiemannGaussian.SemiprimeD1PortScopeEncoding
