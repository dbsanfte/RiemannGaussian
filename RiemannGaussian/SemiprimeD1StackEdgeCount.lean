/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitCountLoop
import RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
/-! # Physical six-field edge-record counting
The first false is a legitimate empty side field, NOT vector EOF. The actual
loop peeks only for an empty tape, parses exactly six complete fields, consumes
every validity bit and payload, and pushes two occurrence markers and one wire marker per complete edge record.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackEdgeCount
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Same seven literal physical roles as the frozen preserving cache scanner. -/
abbrev Stack := SemiprimeD1StackDigitCount.Stack
/-- Seven-word physical payload, no native record count in control. -/
abbrev data := SemiprimeD1StackDigitCount.data
/-- Literal source-preserving whole-tape copy operands. -/
abbrev copyStack := SemiprimeD1StackDigitCount.copyStack
/-- Literal actual field-reader operands. -/
abbrev fieldStack := SemiprimeD1StackDigitCount.fieldStack
/-- Fixed six-field control, including acquired validity and physical payload drain. -/
inductive Control where
  | start | peekRecord | pushCount | pushSecond | pushWire | done | abort
  | read (part : Fin 6) | valid (part : Fin 6) | clear (part : Fin 6)
  deriving DecidableEq,Fintype
/-- Static real Copy and field-parser calls, independent of all edge metadata. -/
abbrev Label := Control ⊕ (Fin 9 ⊕ Field.Label)
/-- Fixed included Copy labels. -/
def copyLabel (pc : Fin 9) : Label := .inr (.inl pc)
/-- Fixed included real field-parser labels. -/
def fieldLabel (pc : Field.Label) : Label := .inr (.inr pc)
/-- Only after the sixth complete field does an edge contribute its actual markers. -/
def afterClear (part : Fin 6) : Label :=
  if h : part.val<5 then .inl (.read ⟨part.val+1,by omega⟩) else .inl .pushCount
/-- One fixed physical tape-counting program; false head bits are parsed. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => SemiprimeD1StackMultiplierLink.instruction copyStack copyLabel (SemiprimeD1StackCopy.code pc)
  | .inr (.inr pc) => SemiprimeD1StackMultiplierLink.instruction fieldStack fieldLabel (Field.code pc)
  | .inl .start => .call (copyLabel 0) (.inl .peekRecord)
  | .inl .peekRecord => .base (.peek .reader (.inl .done) (.inl (.read 0)) (.inl (.read 0)))
  | .inl (.read part) => .call (fieldLabel (Field.active .tagPop (none,false))) (.inl (.valid part))
  | .inl (.valid part) => .base (.pop .valid (.inl .abort) (.inl .abort) (.inl (.clear part)))
  | .inl (.clear part) => .base (.pop .word (afterClear part) (.inl (.clear part)) (.inl (.clear part)))
  | .inl .pushCount => .base (.push .count true (.inl .pushSecond))
  | .inl .pushSecond => .base (.push .count true (.inl .pushWire))
  | .inl .pushWire => .base (.push .copyScratch true (.inl .peekRecord))
  | .inl .done | .inl .abort => .base .halt
/-- Exact six ordinary fields of one edge record; used only as input specification. -/
abbrev Record := Fin 6→List Bool
/-- Actual edge-record input grammar, with NO extra vector marker. -/
def record (words : Record) (tail : List Bool) : List Bool :=
  SemiprimeSourceHistogramKeyBits.frame (words 0)
    (SemiprimeSourceHistogramKeyBits.frame (words 1)
      (SemiprimeSourceHistogramKeyBits.frame (words 2)
        (SemiprimeSourceHistogramKeyBits.frame (words 3)
          (SemiprimeSourceHistogramKeyBits.frame (words 4)
            (SemiprimeSourceHistogramKeyBits.frame (words 5) tail)))))
/-- Full sequence of complete six-field records. -/
def tape (records : List Record) (tail : List Bool) : List Bool := records.foldr record tail
/-- Actual seven-stack fixed machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine SemiprimeD1StackDigitCount.Stack.bank SemiprimeD1StackDigitCount.Stack.count (.inl .start) program
/-- Bank-only entry has no reader, count or parsed-field answer. -/
def initial (bank : List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,data bank [] [] [] [] [] [],[]⟩
/-- Complete physical result preserves original bank and returns acquired markers. -/
def done (bank : List Bool) (n : ℕ) : C.State Stack Label :=
  ⟨none,none,none,data bank [] (List.replicate (2*n) true) [] [] [] (List.replicate n true),[]⟩
/-- After the initial preserving Copy, its emptied scratch is never used by
field reads and retains one physically acquired wire marker per record. -/
def wireCount : Stack := .copyScratch
/-- Exact bytes of one six-field record, including empty fields. -/
theorem record_length (words : Record) (tail : List Bool) :
    (record words tail).length=2*((List.finRange 6).map (fun i=>(words i).length)).sum+6+tail.length := by
  simp [record,SemiprimeSourceHistogramKeyBits.frame_length,List.finRange_succ,List.map_cons,List.sum_cons]
  omega
/-- Six physical fields pay at least one byte per complete record. -/
theorem count_le_bytes (records : List Record) : records.length≤(tape records []).length := by
  induction records with
  | nil => simp [tape]
  | cons r rs ih =>
    simp only [tape,List.foldr_cons,record_length,List.length_cons] at *
    omega
/-- An original half-edge is exactly side + tag + four coordinates. -/
def edgeFields {r t digits : ℕ} (edge : SemiprimeMacroGraph.Edge r t digits) : Record :=
  ![SemiprimeD1EdgeCatalogueEncoding.sideWord edge.2,
    SemiprimeD1EdgeCatalogueEncoding.bit edge.1 0,SemiprimeD1EdgeCatalogueEncoding.bit edge.1 1,
    SemiprimeD1EdgeCatalogueEncoding.bit edge.1 2,SemiprimeD1EdgeCatalogueEncoding.bit edge.1 3,
    SemiprimeD1EdgeCatalogueEncoding.bit edge.1 4]
/-- Exact original input grammar, not a graph/record getter executed by the counter. -/
theorem record_edge {r t digits : ℕ} (edge : SemiprimeMacroGraph.Edge r t digits) (tail : List Bool) :
    record (edgeFields edge) tail=SemiprimeD1EdgeCatalogueEncoding.edge edge tail := rfl
/-- Full actual original edge tape has exactly this six-field-per-record encoding. -/
theorem original_tape {r t digits : ℕ} (edges : List (SemiprimeMacroGraph.Edge r t digits)) :
    tape (edges.map edgeFields) []=edges.foldr SemiprimeD1EdgeCatalogueEncoding.edge [] := by
  simp only [tape,List.foldr_map,record_edge]

end RiemannGaussian.SemiprimeD1StackEdgeCount
