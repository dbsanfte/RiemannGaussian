/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBody
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCleanup
/-! # One complete original-order row, including byte acquisition and cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRows
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1StackMarkedRootRecordsBody SemiprimeD1StackMarkedRootRecordsCleanup
open SemiprimeD1StackMarkedRootRecordsPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
/-- All five descriptor byte lengths; this proof precedes any concrete graph instantiation. -/
theorem mass_eq (fields : Fin 5 → List Bool) :
    SemiprimeD1StackMarkedRootRecordsParse.mass fields=
      (fields 0).length+(fields 1).length+(fields 2).length+(fields 3).length+(fields 4).length := by
  simp only [SemiprimeD1StackMarkedRootRecordsParse.mass,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change (fields 0).length+((fields 1).length+((fields 2).length+((fields 3).length+((fields 4).length+0))))=_
  omega
/-- The common logger consumes exactly the original port tape on both actual branches. -/
theorem branch_ports (bits : List Bool) (row : Row) : (branchTable bits row).portsWord=vectorBits row.scope := by
  cases h : row.inputSide <;> simp only [branchTable,h]
/-- The common logger sees the actual new marked table or byte-identical original relay. -/
theorem branch_table (bits : List Bool) (row : Row) : (branchTable bits row).tableWord=newTable bits row := by
  cases h : row.inputSide <;> simp only [branchTable,newTable,h]
/-- The actual log accumulator is unchanged by the tag/side/table acquisition. -/
theorem branch_history (row : Row) (rec desc hist out : List Bool) :
    (branchWork row rec desc hist out).history=hist := by cases h : row.inputSide <;> simp only [branchWork,h]
/-- Every physically acquired count/side and every retained raw field byte is paid in cleanup. -/
theorem cleanup_bound (bits : List Bool) (row : Row) (rec desc hist out : List Bool) :
    let p := branchTable bits row
    let w := branchWork row rec desc hist out
    w.tag.length+w.coord0.length+p.indexWord.length+w.coord2.length+w.coord3.length+
      p.sideWord.length+p.countWord.length+8 ≤
      SemiprimeD1StackMarkedRootRecordsParse.mass row.fields+row.scope.length+10 := by
  have hm := mass_eq row.fields
  cases h : row.inputSide <;>
    simp only [branchTable,branchWork,h,List.length_cons,List.length_nil,List.length_replicate] <;> omega
/-- Own per-row cap sums only the actual parser/source/logger/cleanup caps. -/
def rowBudget (bits : List Bool) (row : Row) : Nat :=
  8*((vectorBits row.scope).length+row.oldTable.length+SemiprimeD1StackMarkedRootRecordsParse.mass row.fields)+57+
    bodyBudget bits row+(3*((vectorBits row.scope).length+(newTable bits row).length)+7)+
    (SemiprimeD1StackMarkedRootRecordsParse.mass row.fields+row.scope.length+10)
/-- All actual parsed fields and counted arity words are empty at the next physical row boundary. -/
theorem row_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (row : Row) (recordTail descriptorTail hist out : List Bool)
    (hn : r R.originalInput=bits) (hb : bits≠[]) :
    ∃ t ≤ rowBudget bits row, Runs program t (ctl .rowTag)
      (view r v bits {} {records := true::frame (vectorBits row.scope) (frame row.oldTable recordTail),descriptors := SemiprimeD1EdgeCatalogueEncoding.record row.fields descriptorTail,history := hist,output := out})
      (ctl .rowTag)
      (view r v bits {} {records := recordTail,descriptors := descriptorTail,history := (newRow bits row).reverse++hist,output := out}) := by
  have h0 := SemiprimeD1StackMarkedRootRecordsParse.parse_run r v bits (vectorBits row.scope)
    row.oldTable row.fields recordTail descriptorTail hist out
  obtain ⟨a,ha,h1⟩ := body_run r v bits row recordTail descriptorTail hist out hn hb
  let p := branchTable bits row
  let w := branchWork row recordTail descriptorTail hist out
  have h2 := log_run r v bits p w
  have h3 := cleanup_run r v bits {p with portsWord := [],tableWord := []}
    {w with history := (SemiprimeD1StackVertexRecordStream.row p.portsWord p.tableWord).reverse++w.history}
  have h := join h0 (join h1 (join h2 h3))
  have hc := cleanup_bound bits row recordTail descriptorTail hist out
  let t := (8*((vectorBits row.scope).length+row.oldTable.length+SemiprimeD1StackMarkedRootRecordsParse.mass row.fields)+57)+
    (a+((SemiprimeD1StackVertexRecordStream.recordTime p.portsWord p.tableWord+1)+
      (w.tag.length+w.coord0.length+p.indexWord.length+w.coord2.length+w.coord3.length+p.sideWord.length+p.countWord.length+8)))
  refine ⟨t,?_,?_⟩
  · dsimp only [t,p,w] at *
    unfold rowBudget SemiprimeD1StackVertexRecordStream.recordTime
    rw [branch_ports,branch_table]
    omega
  · change Runs program t _ _ _ _ at h
    dsimp only [p,w] at h
    cases hs : row.inputSide <;>
      simpa only [t,p,w,branchTable,branchWork,newRow,newTable,hs] using h
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRows
