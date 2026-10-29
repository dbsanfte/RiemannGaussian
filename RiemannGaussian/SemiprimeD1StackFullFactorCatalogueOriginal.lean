/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueExecution
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesOriginal
/-! # Exact original ALL-factor node records in unchanged factor/incidence order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueOriginal
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueLoop
open SemiprimeD1StackFullFactorCatalogueRows SemiprimeD1StackFullFactorCatalogueExecution
open SemiprimeD1BooleanFactorCatalogueIndices (key scopeWords indices vertex)
open SemiprimeD1BooleanFactorCatalogueIndicesBounds (occurrences cons_values)
open SemiprimeD1BooleanFactorCatalogueIndicesOriginal (numericPorts numericPorts_length numericPorts_lt scopeWords_idAt)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount indexedArity)
namespace L
export SemiprimeD1StackVertexRecordStreamExecution (rows history rows_records)
end L
/-- Actual original numeric scope length equals the old typed local factor arity. -/
theorem numeric_arity (N:Nat) (f:Fin (factorCount N)) :
    (numericPorts N f).length=SemiprimeMacroGraph.subdividedArity (vertex N f):=
  numericPorts_length N f
/-- The complete original factor table, with unchanged ordered numeric occurrence names. -/
def localVertex (N:Nat) (hN:0<N) (f:Fin (factorCount N)) :SemiprimeD1LeafCounter.Vertex:=
  SemiprimeD1StackAllDescriptorRecordOriginal.vertex N hN (vertex N f) (numericPorts N f) (numeric_arity N f)
/-- ALL original factor vertices in source order; no arithmetic tag is filtered or omitted. -/
def factorVertices (N:Nat) (hN:0<N) (fs:List (Fin (factorCount N))) :List SemiprimeD1LeafCounter.Vertex:=
  fs.map (localVertex N hN)
/-- Every actual18-tag call appends EXACTLY the old complete original local row. -/
theorem history_one (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (hist out:List Bool) :
    afterRow bits f.val f hist out=(SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackVertexReadExecution.portTape (localVertex (bitValue bits) hN f).ports)
      (SemiprimeD1TensorTapeCodec.tape (localVertex (bitValue bits) hN f).table)).reverse++hist:=by
  have h:=SemiprimeD1StackAllDescriptorRecordOriginal.history_original bits hc hN (vertex (bitValue bits) f)
    (occurrences (bitValue bits)) (numericPorts (bitValue bits) f) (numericPorts_lt _ f) (numeric_arity _ f)
    [] hist out
  simpa only [afterRow,scopeWords_idAt bits hc hN f,L.history,L.rows,List.nil_append,List.append_nil,
    List.reverse_nil,localVertex] using h
/-- The actual whole sweep has exactly the complete original chronological reverse history. -/
theorem history_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist out:List Bool) :
    afterRows bits n fs hist out=(L.rows (factorVertices (bitValue bits) hN fs)).reverse++hist:=by
  induction fs generalizing n hist with
  | nil=>rfl
  | cons f fs ih=>
    have horder:=cons_values (bitValue bits) n f fs hseq
    have hrow:=history_one bits hc hN f hist out
    rw [horder.1] at hrow
    rw [afterRows,hrow]
    have h:=ih (n+1) horder.2
      ((SemiprimeD1StackVertexRecordStream.row
        (SemiprimeD1StackVertexReadExecution.portTape (localVertex (bitValue bits) hN f).ports)
        (SemiprimeD1TensorTapeCodec.tape (localVertex (bitValue bits) hN f).table)).reverse++hist)
    simpa only [factorVertices,List.map_cons,L.rows,List.reverse_append,List.append_assoc] using h
/-- Complete output bytes equal the frozen leaf reader's original ALL-factor record stream. -/
theorem output_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    outputTape bits=SemiprimeD1StackVertexProduct.records
      (factorVertices (bitValue bits) hN (indices (bitValue bits))):=by
  have h:=history_original bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) [] [false]
  unfold outputTape
  rw [h]
  simp only [List.append_nil,List.reverse_reverse]
  exact L.rows_records _
/-- The SAME actual N-only final output has all original arithmetic/Boolean/equality factors. -/
theorem final_output (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (done bits).data output=SemiprimeD1StackVertexProduct.records
      (factorVertices (bitValue bits) hN (indices (bitValue bits))):=
  output_original bits hc hN
/-- All original local ports retain the unchanged factor-major occurrence enumeration. -/
theorem local_ports (N:Nat) (hN:0<N) (f:Fin (factorCount N)) :
    (localVertex N hN f).ports=(SemiprimeD1RootTensorTables.factorNode N hN f).ports.map
      (SemiprimeD1BooleanFactorCatalogueIndicesOriginal.portOrdinal N):=
  SemiprimeD1BooleanFactorCatalogueIndicesOriginal.numericPorts_factorNode N hN f
/-- Generic root-table dimension rewriting changes no literal output byte. -/
theorem build_bytes_congr (m n:Nat) (h:m=n) (producer:List Bool→SemiprimeD1JetAffineCoefficient.JetRun) :
    SemiprimeD1TensorTapeCodec.tape (SemiprimeD1TensorTables.build m producer).table=
      SemiprimeD1TensorTapeCodec.tape (SemiprimeD1TensorTables.build n producer).table:=by cases h;rfl
/-- Actual local node table bytes are EXACT the old factorNode table, including every arithmetic tag. -/
theorem local_table (N:Nat) (hN:0<N) (f:Fin (factorCount N)) :
    SemiprimeD1TensorTapeCodec.tape (localVertex N hN f).table=
      SemiprimeD1TensorTapeCodec.tape (SemiprimeD1RootTensorTables.factorNode N hN f).table:=by
  change SemiprimeD1TensorTapeCodec.tape
    (cast (congrArg SemiprimeD1TensorTables.Table (numeric_arity N f).symm)
      (SemiprimeD1BooleanRootTablesOriginal.reference N hN (vertex N f)))=_
  rw [SemiprimeD1StackBooleanRecordOriginal.tape_cast (numeric_arity N f).symm
    (SemiprimeD1BooleanRootTablesOriginal.reference N hN (vertex N f))]
  change SemiprimeD1TensorTapeCodec.tape (SemiprimeD1BooleanRootTablesOriginal.reference N hN
    ((SemiprimePublicAcquiredExecution.vertexEnumeration N).equivFin f))=_
  rw [SemiprimeD1BooleanRootTablesOriginal.reference_indexed]
  exact (build_bytes_congr _ _ (SemiprimeD1RootTensorTables.factorNode_degree N hN f)
    (SemiprimeD1RootTensorTables.factorProducer N hN f)).symm
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueOriginal
