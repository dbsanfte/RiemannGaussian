/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
/-! # Actual unary-side to singleton conversion before the144-role source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsSide
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual []/[TRUE] side parsing; the TRUE case additionally pays the real EOF peek. -/
theorem normalize (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (sideBit : Bool) :
    ∃ t ≤ 3, Runs program t (ctl .sideRead)
      (view r v bits {p with sideWord := []} {w with coord0 := if sideBit then [true] else []})
      (ctl .clearOldTable) (view r v bits {p with sideWord := [sideBit]} {w with coord0 := []}) := by
  cases sideBit
  · have h0 : Runs program 1 (ctl .sideRead)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) (ctl .sideFalse)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) := by
      apply one_base program _ _ (.pop (aux .coord0) (ctl .sideFalse) (ctl .abort) (ctl .sideEOF)) _ _ rfl
      · rfl
      · exact set_coord0 _ _ _ _ _ _
    have h1 : Runs program 1 (ctl .sideFalse)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) (ctl .clearOldTable)
        (view r v bits {p with sideWord := [false]} {w with coord0 := []}) := by
      apply one_base program _ _ (.push side false (ctl .clearOldTable)) _ _ rfl
      · rfl
      · exact set_sideWord _ _ _ _ _ _
    exact ⟨2,by omega,join h0 h1⟩
  · have h0 : Runs program 1 (ctl .sideRead)
        (view r v bits {p with sideWord := []} {w with coord0 := [true]}) (ctl .sideEOF)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) := by
      apply one_base program _ _ (.pop (aux .coord0) (ctl .sideFalse) (ctl .abort) (ctl .sideEOF)) _ _ rfl
      · rfl
      · exact set_coord0 _ _ _ _ _ _
    have h1 : Runs program 1 (ctl .sideEOF)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) (ctl .sideTrue)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) := by
      apply one_base program _ _ (.peek (aux .coord0) (ctl .sideTrue) (ctl .abort) (ctl .abort)) _ _ rfl
      · rfl
      · rfl
    have h2 : Runs program 1 (ctl .sideTrue)
        (view r v bits {p with sideWord := []} {w with coord0 := []}) (ctl .clearOldTable)
        (view r v bits {p with sideWord := [true]} {w with coord0 := []}) := by
      apply one_base program _ _ (.push side true (ctl .clearOldTable)) _ _ rfl
      · rfl
      · exact set_sideWord _ _ _ _ _ _
    exact ⟨3,by omega,join (join h0 h1) h2⟩
/-- Every old table byte is physically erased before any new table computation. -/
theorem clear_table (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) :
    Runs program (p.tableWord.length+1) (ctl .clearOldTable) (view r v bits p w)
      (ctl .inputTable) (view r v bits {p with tableWord := []} w) := by
  have h := SemiprimeD1StackPhysicalLoops.drain program (ctl .clearOldTable) (ctl .inputTable)
    table rfl (view r v bits p w) p.tableWord
  rw [show Function.update (view r v bits p w) table p.tableWord=view r v bits p w from
    Function.update_eq_self _ _,set_tableWord] at h
  exact h
/-- EMPTY parsed input tag really enters side decoding, including valid side zero. -/
theorem input_tag (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) :
    Runs program 1 (ctl .caseTag) (view r v bits p {w with tag := []})
      (ctl .sideRead) (view r v bits p {w with tag := []}) := by
  apply one_base program _ _ (.peek (aux .tag) (ctl .sideRead) (ctl .abort) (ctl .log)) _ _ rfl
  · rfl
  · rfl
/-- Every other canonical original tag takes the actual byte-relay branch. -/
theorem relay_tag (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) (tail : List Bool) :
    Runs program 1 (ctl .caseTag) (view r v bits p {w with tag := true::tail})
      (ctl .log) (view r v bits p {w with tag := true::tail}) := by
  apply one_base program _ _ (.peek (aux .tag) (ctl .sideRead) (ctl .abort) (ctl .log)) _ _ rfl
  · rfl
  · rfl
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsSide
