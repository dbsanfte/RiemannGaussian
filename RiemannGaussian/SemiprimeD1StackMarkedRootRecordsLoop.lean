/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRows
/-! # Complete real paired-record sweep, including the two distinct physical EOFs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLoop
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsEncoding
open SemiprimeD1StackMarkedRootRecordsRows SemiprimeD1StackMarkedRootRecordsFields
open SemiprimeD1StackMarkedRootRecordsPrimitives SemiprimeD1StackProcedureTrace
/-- One actual FALSE pop, then real record EOF and independent EMPTY descriptor EOF checks. -/
theorem end_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits hist out : List Bool) :
    Runs program 3 (ctl .rowTag) (view r v bits {} {records := [false],history := hist,output := out})
      (ctl .reverseFactors) (view r v bits {} {history := hist,output := out}) := by
  have h0 := record_end (view r v bits {} {records := [false],history := hist,output := out}) rfl
  rw [set_records] at h0
  have h1 : Runs program 1 (ctl .recordEOF) (view r v bits {} {history := hist,output := out})
      (ctl .descriptorEOF) (view r v bits {} {history := hist,output := out}) := by
    apply one_base program _ _ (.peek (aux .recordReader) (ctl .descriptorEOF) (ctl .abort) (ctl .abort)) _ _ rfl
    · rfl
    · rfl
  have h2 : Runs program 1 (ctl .descriptorEOF) (view r v bits {} {history := hist,output := out})
      (ctl .reverseFactors) (view r v bits {} {history := hist,output := out}) := by
    apply one_base program _ _ (.peek (aux .descriptorReader) (ctl .reverseFactors) (ctl .abort) (ctl .abort)) _ _ rfl
    · rfl
    · rfl
  exact join (join h0 h1) h2
/-- Fixed sum of the SAME program's real row caps plus physical completion checks. -/
def loopBudget (bits : List Bool) (rows : List Row) : Nat := (rows.map (rowBudget bits)).sum+3
/-- All original paired rows are consumed in forward order, preserving both actual source banks. -/
theorem loop_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (rows : List Row) (hist out : List Bool) (hn : r R.originalInput=bits) (hb : bits≠[]) :
    ∃ t ≤ loopBudget bits rows, Runs program t (ctl .rowTag)
      (view r v bits {} {records := oldRecords rows,descriptors := descriptors rows,history := hist,output := out})
      (ctl .reverseFactors) (view r v bits {} {history := (payload bits rows).reverse++hist,output := out}) := by
  induction rows generalizing hist with
  | nil =>
    refine ⟨3,by simp only [loopBudget,List.map_nil,List.sum_nil];omega,?_⟩
    exact end_run r v bits hist out
  | cons row rows ih =>
    obtain ⟨a,ha,h0⟩ := row_run r v bits row (oldRecords rows) (descriptors rows) hist out hn hb
    obtain ⟨b,hb0,h1⟩ := ih ((newRow bits row).reverse++hist)
    refine ⟨a+b,?_,?_⟩
    · simp only [loopBudget,List.map_cons,List.sum_cons] at hb0 ⊢
      omega
    · simpa only [oldRecords,descriptors,payload,List.foldr_cons,List.reverse_append,List.append_assoc]
        using join h0 h1
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLoop
