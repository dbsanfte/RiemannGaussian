/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsParse
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsSide
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsTableCall
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsEncoding
/-! # Real parsed-tag dispatch: byte relay or complete marked-input reacquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBody
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1StackMarkedRootRecordsPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- The physically reached table/template/count bank before the common real logger. -/
def branchTable (bits : List Bool) (row : Row) : TableWork :=
  match row.inputSide with
  | none => {indexWord := row.fields 2,portsWord := vectorBits row.scope,tableWord := row.oldTable}
  | some b => {indexWord := row.fields 2,sideWord := [b],portsWord := vectorBits row.scope,countWord := List.replicate row.scope.length true,tableWord := newTable bits row}
/-- Input-side parsing actually consumes coord0; relay retains every raw descriptor field. -/
def branchWork (row : Row) (recordTail descriptorTail hist out : List Bool) : Work :=
  match row.inputSide with
  | none => {records := recordTail,descriptors := descriptorTail,tag := row.fields 0,coord0 := row.fields 1,coord2 := row.fields 3,coord3 := row.fields 4,history := hist,output := out}
  | some _ => {records := recordTail,descriptors := descriptorTail,coord2 := row.fields 3,coord3 := row.fields 4,history := hist,output := out}
/-- Actual branch cap is solely the sum of executed primitive/source caps. -/
def bodyBudget (bits : List Bool) (row : Row) : Nat :=
  match row.inputSide with
  | none => 1
  | some b => row.oldTable.length+SemiprimeD1StackMarkedPublicInputTableExecution.runBound bits (row.fields 2) b row.scope+6
/-- Both branches reach the SAME actual logger; no side, coefficient or arity answer is input. -/
theorem body_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (row : Row) (recordTail descriptorTail hist out : List Bool)
    (hn : r R.originalInput=bits) (hb : bits≠[]) :
    ∃ t ≤ bodyBudget bits row, Runs program t (ctl .caseTag)
      (SemiprimeD1StackMarkedRootRecordsParse.parsed r v bits (vectorBits row.scope) row.oldTable row.fields
        recordTail descriptorTail hist out) (ctl .log)
      (view r v bits (branchTable bits row) (branchWork row recordTail descriptorTail hist out)) := by
  cases hside : row.inputSide with
  | none =>
    have hs := row.shape
    rw [hside] at hs
    obtain ⟨tail,ht⟩ := hs
    have h := SemiprimeD1StackMarkedRootRecordsSide.relay_tag r v bits
      ({indexWord := row.fields 2,portsWord := vectorBits row.scope,tableWord := row.oldTable} : TableWork)
      ({records := recordTail,descriptors := descriptorTail,coord0 := row.fields 1,coord2 := row.fields 3,coord3 := row.fields 4,history := hist,output := out} : Work) tail
    refine ⟨1,by simp only [bodyBudget,hside];omega,?_⟩
    simpa only [SemiprimeD1StackMarkedRootRecordsParse.parsed,branchTable,branchWork,hside,ht] using h
  | some b =>
    have hs := row.shape
    rw [hside] at hs
    rcases hs with ⟨htag,hcoord⟩
    let p : TableWork := {indexWord := row.fields 2,portsWord := vectorBits row.scope,tableWord := row.oldTable}
    let w : Work := {records := recordTail,descriptors := descriptorTail,coord2 := row.fields 3,coord3 := row.fields 4,history := hist,output := out}
    have h0 := SemiprimeD1StackMarkedRootRecordsSide.input_tag r v bits p {w with coord0 := row.fields 1}
    rw [hcoord] at h0
    obtain ⟨a,ha,h1⟩ := SemiprimeD1StackMarkedRootRecordsSide.normalize r v bits p w b
    have h2 := SemiprimeD1StackMarkedRootRecordsSide.clear_table r v bits {p with sideWord := [b]} w
    obtain ⟨c,hc,h3⟩ := SemiprimeD1StackMarkedRootRecordsTableCall.table_run r v bits (row.fields 2) b row.scope w hn hb
    have h := join (join (join h0 h1) h2) h3
    refine ⟨((1+a)+(row.oldTable.length+1))+c,?_,?_⟩
    · simp only [bodyBudget,hside]
      omega
    · simpa only [SemiprimeD1StackMarkedRootRecordsParse.parsed,branchTable,branchWork,newTable,hside,htag,hcoord,p,w] using h
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsBody
