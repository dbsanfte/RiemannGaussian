/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueOriginal
/-! # Actual zero-history source clocks bound each new row and whole history
The bound is extracted from the SAME actual dispatcher source execution.
No native table report or supplied output-size/clock function is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueHistoryBounds
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueRows
open SemiprimeD1StackFullFactorCatalogueLoop SemiprimeD1StackFullFactorCatalogueOriginal
open SemiprimeD1BooleanFactorCatalogueIndices (scopeWords vertex)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
namespace DC
export SemiprimeD1StackAllDescriptorRecordCleanup (mass word_le_mass)
end DC
/-- Actual clean physical operand mass for one source call with empty accumulators. -/
def rowInputMass (bits:List Bool) (f:Fin (factorCount (bitValue bits))) :Nat:=
  DC.mass (D.cleanData (DR.rawFields bits (vertex (bitValue bits) f))
    (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits f.val)) [] [])
/-- Actual original source's zero-history run allowance plus its actual acquired input bytes. -/
def rowCap (bits:List Bool) (f:Fin (factorCount (bitValue bits))) :Nat:=
  rowInputMass bits f+DS.timeBound (DR.originalCode (vertex (bitValue bits) f))
    (DR.rawFields bits (vertex (bitValue bits) f)) (scopeWords bits f.val) [] []
/-- Exact old literal row bytes, used only to express the actual output bound. -/
def rowBytes (N:Nat) (hN:0<N) (f:Fin (factorCount N)) :List Bool:=
  SemiprimeD1StackVertexRecordStream.row
    (SemiprimeD1StackVertexReadExecution.portTape (localVertex N hN f).ports)
    (SemiprimeD1TensorTapeCodec.tape (localVertex N hN f).table)
/-- Actual source execution from empty history pays every newly produced row byte. -/
theorem row_bytes_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) :(rowBytes (bitValue bits) hN f).length≤rowCap bits f:=by
  let v:=vertex (bitValue bits) f
  let rawWords:=DR.rawFields bits v
  let scopes:=scopeWords bits f.val
  obtain ⟨htag,h2,h3,h4⟩:=DR.raw_canonical bits v
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAllDescriptorRecordExecution.source_run (DR.originalCode v) rawWords
    htag h2 h3 h4 (DR.raw_transform_bound bits v) hc hN scopes [] []
  have hi (k:D.Stack) :((SemiprimeD1StackAllDescriptorRecord.initial rawWords
      (SemiprimeD1TensorTapeCodec.vectorBits scopes) [] []).data k).length≤rowInputMass bits f:=
    DC.word_le_mass _ k
  have hd:=SemiprimeD1StackReturnLink.run_data_bound D.program t (rowInputMass bits f) _ _ hi hr
  have hh:=hd SemiprimeD1StackAllDescriptorRecord.history
  change (afterRow bits f.val f [] []).length≤rowInputMass bits f+t at hh
  rw [history_one bits hc hN f [] [],List.append_nil,List.length_reverse] at hh
  exact hh.trans (Nat.add_le_add_left ht (rowInputMass bits f))
/-- Original output row length is bounded by the sum of actual zero-history source costs. -/
theorem rows_bytes_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fs:List (Fin (factorCount (bitValue bits)))) :
    (SemiprimeD1StackVertexRecordStreamExecution.rows (factorVertices (bitValue bits) hN fs)).length≤
      (fs.map (rowCap bits)).sum:=by
  induction fs with
  | nil=>rfl
  | cons f fs ih=>
    have h:=row_bytes_le bits hc hN f
    change ((rowBytes (bitValue bits) hN f)++
      SemiprimeD1StackVertexRecordStreamExecution.rows (factorVertices (bitValue bits) hN fs)).length≤_
    rw [List.length_append]
    simp only [List.map_cons,List.sum_cons];omega
/-- Real history grows additively; it does not incur an exponential-in-factor-count recurrence. -/
theorem history_length_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist out:List Bool) :
    (afterRows bits n fs hist out).length≤(fs.map (rowCap bits)).sum+hist.length:=by
  rw [history_original bits hc hN n fs hseq hist out,List.length_append,List.length_reverse]
  exact Nat.add_le_add_right (rows_bytes_le bits hc hN fs) hist.length
/-- Every actual current row increases history only by its own paid zero-history output allowance. -/
theorem history_increment (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (hist out:List Bool) :
    (afterRow bits f.val f hist out).length≤rowCap bits f+hist.length:=by
  rw [history_one bits hc hN f hist out,List.length_append,List.length_reverse]
  exact Nat.add_le_add_right (row_bytes_le bits hc hN f) hist.length
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueHistoryBounds
