/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecords
/-! # Proof-side paired physical record and descriptor streams
Rows specify bytes physically parsed by the fixed caller. No row, typed vertex,
side option or mathematical table is a runtime control operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1StackMarkedRootRecords
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual parsed tag/side shape. EMPTY tag is the valid first constructor. -/
def Shape (fields : Fin 5 → List Bool) : Option Bool → Prop
  | none => ∃ tail, fields 0=true::tail
  | some sideBit => fields 0=[] ∧ fields 1=if sideBit then [true] else []
/-- A paired acquired record, specified with its physical fields and arbitrary scope payloads. -/
structure Row where
  /-- Original physical scope-field payloads; only count enters the table scanner. -/
  scope : List (List Bool)
  /-- Actual old parsed table bytes, including every coefficient and branch. -/
  oldTable : List Bool
  /-- Five actual descriptor fields, all parsed and drained physically. -/
  fields : Fin 5 → List Bool
  /-- Proof-side classification of the actual parsed input tag. -/
  inputSide : Option Bool
  /-- No extra branch verdict is supplied: the shape is proved from actual bytes. -/
  shape : Shape fields inputSide
/-- Actual factor-record stream with its single FALSE terminator. -/
def oldRecords (rows : List Row) : List Bool :=
  rows.foldr (fun row tail => true::frame (vectorBits row.scope) (frame row.oldTable tail)) [false]
/-- Actual descriptor stream has no row tags and EMPTY EOF. -/
def descriptors (rows : List Row) : List Bool :=
  rows.foldr (fun row tail => SemiprimeD1EdgeCatalogueEncoding.record row.fields tail) []
/-- Proof-side output of the ACTUAL144 source, or literal byte relay. -/
def newTable (bits : List Bool) (row : Row) : List Bool :=
  match row.inputSide with
  | none => row.oldTable
  | some sideBit => SemiprimeD1StackMarkedPublicInputTableExecution.outputTape bits (row.fields 2) sideBit row.scope
/-- One newly acquired marked factor record, with the original ports unchanged. -/
def newRow (bits : List Bool) (row : Row) : List Bool :=
  SemiprimeD1StackVertexRecordStream.row (vectorBits row.scope) (newTable bits row)
/-- Complete chronological marked factor payload before the single output terminator. -/
def payload (bits : List Bool) (rows : List Row) : List Bool :=
  rows.foldr (fun row tail => newRow bits row++tail) []
/-- Constructor recognition is pure specification of actual original unary tags. -/
def inputSide {r t digits : Nat} : SemiprimeMacroGraph.SubdividedVertex r t digits → Option Bool
  | .inl (.input side _) => some (decide (side=1))
  | _ => none
/-- Every original descriptor satisfies the actual physical tag/side branch invariant. -/
theorem original_shape {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits) :
    Shape (SemiprimeD1EdgeCatalogueEncoding.vertex v) (inputSide v) := by
  rcases v with v|v
  · cases v with
    | input side i => fin_cases side <;> exact ⟨rfl,rfl⟩
    | first tr j | scale tr j k | second tr k | product k | carry k | orGate side i | inputCheck side =>
      exact ⟨_,rfl⟩
    | carryInitial | carryTerminal => exact ⟨_,rfl⟩
  · rcases v with ⟨word,bit⟩|flag
    · cases word <;> exact ⟨_,rfl⟩
    · cases flag <;> exact ⟨_,rfl⟩
/-- Exact original paired row at any acquired original factor index. -/
def originalRow (N : Nat) (hN : 0 < N) (f : Fin (SemiprimePublicAcquiredExecution.factorCount N)) : Row where
  scope := (SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts N f).map
    (fun p => List.replicate p true)
  oldTable := SemiprimeD1TensorTapeCodec.tape (SemiprimeD1StackFullFactorCatalogueOriginal.localVertex N hN f).table
  fields := SemiprimeD1EdgeCatalogueEncoding.vertex (SemiprimeD1BooleanFactorCatalogueIndices.vertex N f)
  inputSide := inputSide (SemiprimeD1BooleanFactorCatalogueIndices.vertex N f)
  shape := original_shape _
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsEncoding
