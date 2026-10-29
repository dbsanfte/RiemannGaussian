/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueExecution
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesOriginal
/-! # Exact original chronological Boolean factor records from binary N
The actual occurrence-ID bank is converted by the paid serializer. Every
retained local table is the original integer0/1 table before any products.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueOriginal
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueLoop
open SemiprimeD1StackBooleanFactorCataloguePrimitives
open SemiprimeD1StackBooleanFactorCatalogueExecution
open SemiprimeD1BooleanFactorCatalogueIndices (scopeWords indices vertex)
open SemiprimeD1BooleanFactorCatalogueIndicesBounds (occurrences)
open SemiprimeD1BooleanFactorCatalogueIndicesOriginal (numericPorts numericPorts_length numericPorts_lt)
open SemiprimeD1StackBooleanDescriptorRecordOriginal (originalMode)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount indexedArity)
namespace B
export SemiprimeD1StackBooleanRecordOriginal (vertex row_original)
end B
namespace L
export SemiprimeD1StackVertexRecordStreamExecution (rows rows_records)
end L
/-- Original numeric port count is the old typed local-table arity. -/
theorem numeric_arity (N : Nat) (f : Fin (factorCount N)) :
    (numericPorts N f).length=SemiprimeMacroGraph.subdividedArity (vertex N f) :=
  numericPorts_length N f
/-- The exact old leaf vertex, retaining original ordered occurrence ports and table. -/
def localVertex (N : Nat) (hN:0<N) (f : Fin (factorCount N)) : SemiprimeD1LeafCounter.Vertex :=
  B.vertex N hN (vertex N f) (numericPorts N f) (numeric_arity N f)
/-- The original Boolean factor subsequence, preserving complete original source order. -/
def booleanVertices (N : Nat) (hN:0<N) (fs : List (Fin (factorCount N))) : List SemiprimeD1LeafCounter.Vertex :=
  fs.filterMap (fun f=>match originalMode (vertex N f) with
    | none=>none | some _=>some (localVertex N hN f))
/-- ONE actual Boolean row has exactly the old numeric scopes and original table;
no graph permutation or uncharged binary-to-unary conversion is assumed. -/
theorem history_some (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f : Fin (factorCount (bitValue bits))) (mode : SemiprimeD1StackBooleanEntry.Mode)
    (hm:originalMode (vertex (bitValue bits) f)=some mode) (hist : List Bool) :
    DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits f.val) hist=
      (SemiprimeD1StackVertexRecordStream.row
        (SemiprimeD1StackVertexReadExecution.portTape (localVertex (bitValue bits) hN f).ports)
        (SemiprimeD1TensorTapeCodec.tape (localVertex (bitValue bits) hN f).table)).reverse++hist := by
  obtain ⟨_,_,_,hmatch⟩:=SemiprimeD1StackBooleanDescriptorRecordOriginal.original_dispatch
    (bitValue bits) hN (vertex (bitValue bits) f) mode hm
  have hr:=B.row_original (bitValue bits) hN (vertex (bitValue bits) f) mode hmatch (occurrences (bitValue bits))
    (numericPorts (bitValue bits) f) (numericPorts_lt _ f) (numeric_arity _ f)
  have h:=congrArg (fun row : List Bool=>row.reverse++hist) hr
  simpa only [SemiprimeD1StackBooleanDescriptorRecordAll.afterHistory,hm,
    SemiprimeD1BooleanFactorCatalogueIndicesOriginal.scopeWords_idAt bits hc hN f,localVertex] using h
/-- Every actual descriptor sweep accumulates the exact original reverse row log. -/
theorem history_original (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist : List Bool) :
    afterRows bits n fs hist=(L.rows (booleanVertices (bitValue bits) hN fs)).reverse++hist := by
  induction fs generalizing n hist with
  | nil=>rfl
  | cons f fs ih=>
    have horder:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.cons_values (bitValue bits) n f fs hseq
    cases hm:originalMode (vertex (bitValue bits) f) with
    | none=>
      have hh:DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits n) hist=hist:=by
        simp only [SemiprimeD1StackBooleanDescriptorRecordAll.afterHistory,hm]
      rw [afterRows,hh]
      have h:=ih (n+1) horder.2 hist
      simpa only [booleanVertices,List.filterMap_cons,hm] using h
    | some mode=>
      have hh:=history_some bits hc hN f mode hm hist
      rw [horder.1] at hh
      rw [afterRows,hh]
      have h:=ih (n+1) horder.2
        ((SemiprimeD1StackVertexRecordStream.row
          (SemiprimeD1StackVertexReadExecution.portTape (localVertex (bitValue bits) hN f).ports)
          (SemiprimeD1TensorTapeCodec.tape (localVertex (bitValue bits) hN f).table)).reverse++hist)
      simpa only [booleanVertices,List.filterMap_cons,hm,L.rows,List.reverse_append,List.append_assoc] using h
/-- The actual full output is byte-for-byte the original leaf's complete Boolean
factor-record subsequence, including the single final false terminator. -/
theorem output_original (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    outputTape bits=SemiprimeD1StackVertexProduct.records
      (booleanVertices (bitValue bits) hN (indices (bitValue bits))) := by
  have h:=history_original bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) []
  unfold outputTape
  rw [h]
  simp only [List.append_nil,List.reverse_reverse]
  exact L.rows_records _
/-- Literal final output stack of the same actual N-only machine. -/
theorem final_output (bits : List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (done bits).data output=SemiprimeD1StackVertexProduct.records
      (booleanVertices (bitValue bits) hN (indices (bitValue bits))) :=
  output_original bits hc hN
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueOriginal
