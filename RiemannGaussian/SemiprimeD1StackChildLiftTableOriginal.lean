/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTableInput
import RiemannGaussian.SemiprimeD1StackChildLiftTableMeaning
/-! # Whole actual eager child-table acquisition with original per-entry lifts
Every scope marker, assignment, parent lookup, individual integer lift, payload
copy, source drain, DFS return and final reversal is executed by one fixed
program. Actual parent-record extraction and child-vertex assembly remain caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableOriginal
open SemiprimeD1StackChildLiftTable
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace Input
export SemiprimeD1StackChildLiftTableInput (original budget raw_empty source_trace)
end Input
namespace V
export SemiprimeD1StackVectorTableBounds (runBound)
end V
/-- Exact actually copied original six-word template, with every other55 source role EMPTY. -/
def original {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) : E.Stack→List Bool :=
  Input.original (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
    (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp
/-- Original literal per-assignment integer lifts occur only in the output specification. -/
def answer {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (raw : List Bool) : List (List Bool) :=
  (SemiprimeD1ChildTableCopyTape.entry old extra (SemiprimeBitArithmetic.bitValue newp) parent order raw).words
/-- Complete physical halt retains the template and scope while all live61 source roles are EMPTY. -/
def done {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackVectorTableExecution.done source (original old extra oldp newp parent order)
    scope (answer old extra newp parent order)
/-- Own actual source clock pays every scope byte and every real entry call and source-bank cleanup. -/
def timeBound {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) : ℕ :=
  V.runBound source (original old extra oldp newp parent order) scope (Input.budget old extra oldp newp parent order)
/-- The entire serialized child table is EXACTLY the original eager per-entry integer lift, in original port order. -/
theorem output_original {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order : List ℕ) (scope : List (List Bool)) :
    (done old extra oldp newp parent order scope).data (SemiprimeD1StackVectorTable.aux .output)=
      tape (SemiprimeD1StackChildLiftTableMeaning.table old extra (SemiprimeBitArithmetic.bitValue newp)
        scope.length parent order) := by
  change tape (SemiprimeD1StackVectorTableSpec.tree (answer old extra newp parent order) [] scope.length)=_
  unfold answer
  rw [SemiprimeD1StackChildLiftTableMeaning.tree_original]
/-- SAME whole fixed134-role source acquires every table entry itself; no entry vectors or table answers are input. -/
theorem source_run {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order : List ℕ) (scope : List (List Bool)) :
    ∃t ≤ timeBound old extra oldp newp parent order scope,
      SemiprimeD1StackCalls.run program t
        (initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
          (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits scope))=
      some (done old extra oldp newp parent order scope) ∧
      (done old extra oldp newp parent order scope).data (SemiprimeD1StackVectorTable.aux .output)=
        tape (SemiprimeD1StackChildLiftTableMeaning.table old extra (SemiprimeBitArithmetic.bitValue newp)
          scope.length parent order) := by
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackVectorTableBounds.source_run_bounded source
    (original old extra oldp newp parent order) (Input.raw_empty _ _ _ _ _ _)
    (answer old extra newp parent order) (Input.budget old extra oldp newp parent order)
    (Input.source_trace old ho extra he oldp newp hp parent hg order) scope
  exact ⟨t,ht,hr,output_original old extra oldp newp parent order scope⟩
end RiemannGaussian.SemiprimeD1StackChildLiftTableOriginal
