/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexRecordSpliceExecution
import RiemannGaussian.SemiprimeD1StackVertexProduct
/-! # The existing native vertex codec admits exact linear accumulation
Active and inactive record builders both produce this SAME codec. The final
singleton FALSE is cancelled physically by the actual two-word splicer. The
whole vertex-loop supplier/stream zip is still a separate caller obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackVertexRecordSpliceMeaning
open SemiprimeD1StackVertexRecordSplice SemiprimeD1StackVertexRecordSpliceExecution
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (frame_append)
/-- A complete native vertex row without its surrounding stream's final EOF. -/
def row (v : SemiprimeD1LeafCounter.Vertex) : List Bool :=
  true::frame (SemiprimeD1StackVertexReadExecution.portTape v.ports)
    (frame (SemiprimeD1TensorTapeCodec.tape v.table) [])
/-- The singleton's LAST bit is exactly one FALSE, independently of EVERY coefficient bit. -/
theorem singleton_stream (v : SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexProduct.records [v]=row v++[false] := by
  simp only [row,SemiprimeD1StackVertexProduct.records,List.cons_append,frame_append,List.nil_append]
/-- Exact whole raw record concatenation; no field parsing or word-value quotient is involved. -/
theorem cons_stream (v : SemiprimeD1LeafCounter.Vertex) (vs : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexProduct.records (v::vs)=row v++SemiprimeD1StackVertexProduct.records vs := by
  simp only [row,SemiprimeD1StackVertexProduct.records,List.cons_append,frame_append,List.nil_append]
/-- The SAME physical two-word source accepts the ENTIRE acquired record of either native builder. -/
theorem source_vertex (v : SemiprimeD1LeafCounter.Vertex) (history : List Bool) :
    SemiprimeD1StackCalls.run program (timeBound (row v))
      (initial (SemiprimeD1StackVertexProduct.records [v]) history)=some (done ((row v).reverse++history)) := by
  rw [singleton_stream]
  exact source_run (row v) history
/-- A whole chronological native stream is the row concatenation followed by ONE final FALSE. -/
theorem records_rows (vs : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexProduct.records vs=vs.flatMap row++[false] := by
  induction vs with
  | nil=>rfl
  | cons v vs ih=>rw [cons_stream,ih,List.flatMap_cons,List.append_assoc]
/-- Summing actual SAME-source per-row clocks is linear in TOTAL row bytes, with no old-history length term.
This is a budget identity for actual component calls, not a claim that the full vertex supplier loop is implemented here. -/
theorem additive_clock (vs : List SemiprimeD1LeafCounter.Vertex) :
    (vs.map (fun v=>timeBound (row v))).sum=2*(vs.flatMap row).length+7*vs.length := by
  induction vs with
  | nil=>rfl
  | cons v vs ih=>
    rw [List.map_cons,List.sum_cons,ih,List.flatMap_cons,List.length_append,List.length_cons]
    unfold timeBound
    omega
end RiemannGaussian.SemiprimeD1StackVertexRecordSpliceMeaning
