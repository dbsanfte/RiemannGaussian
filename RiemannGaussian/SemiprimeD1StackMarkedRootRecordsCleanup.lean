/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLogger
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
/-! # Same-row logging followed by paid field/side/count erasure -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCleanup
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackProcedureTrace
/-- The actual logger consumes both fields before any per-row metadata is cleared. -/
theorem log_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) :
    Runs program (SemiprimeD1StackVertexRecordStream.recordTime p.portsWord p.tableWord+1) (ctl .log)
      (view r v bits p w) (ctl (.clearField 0))
      (view r v bits {p with portsWord := [],tableWord := []}
        {w with history := (SemiprimeD1StackVertexRecordStream.row p.portsWord p.tableWord).reverse++w.history}) := by
  have h := SemiprimeD1StackMarkedRootRecordsLogger.record_call (view r v bits p w)
  change Runs program (SemiprimeD1StackVertexRecordStream.recordTime p.portsWord p.tableWord+1)
    (ctl .log) (view r v bits p w) (ctl (.clearField 0))
    (Function.update (Function.update (Function.update (view r v bits p w) ports []) table [])
      (aux .history) ((SemiprimeD1StackVertexRecordStream.row p.portsWord p.tableWord).reverse++w.history)) at h
  rw [set_portsWord,set_tableWord,set_history] at h
  exact h
/-- All actual metadata bytes, seven real EOF reads and the next-row jump are paid. -/
theorem cleanup_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits : List Bool)
    (p : TableWork) (w : Work) :
    Runs program (w.tag.length+w.coord0.length+p.indexWord.length+w.coord2.length+w.coord3.length+
      p.sideWord.length+p.countWord.length+8) (ctl (.clearField 0)) (view r v bits p w) (ctl .rowTag)
      (view r v bits {p with indexWord := [],sideWord := [],countWord := []}
        {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) := by
  have h0 := SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearField 0)) (ctl (.clearField 1)) (coordinate 0) rfl
    (view r v bits p w) w.tag
  change Runs program _ _ (Function.update (view r v bits p w) (aux .tag) w.tag) _
    (Function.update (view r v bits p w) (aux .tag) []) at h0
  rw [show Function.update (view r v bits p w) (aux .tag) w.tag=view r v bits p w from Function.update_eq_self _ _,set_tag] at h0
  have h1 := SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearField 1)) (ctl (.clearField 2)) (coordinate 1) rfl
    (view r v bits p {w with tag := []}) w.coord0
  change Runs program _ _ (Function.update (view r v bits p {w with tag := []}) (aux .coord0) w.coord0) _
    (Function.update (view r v bits p {w with tag := []}) (aux .coord0) []) at h1
  rw [show Function.update (view r v bits p {w with tag := []}) (aux .coord0) w.coord0=view r v bits p {w with tag := []} from Function.update_eq_self _ _,set_coord0] at h1
  have h2 := SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearField 2)) (ctl (.clearField 3)) (coordinate 2) rfl
    (view r v bits p {w with tag := [],coord0 := []}) p.indexWord
  change Runs program _ _ (Function.update (view r v bits p {w with tag := [],coord0 := []}) (index) p.indexWord) _
    (Function.update (view r v bits p {w with tag := [],coord0 := []}) (index) []) at h2
  rw [show Function.update (view r v bits p {w with tag := [],coord0 := []}) (index) p.indexWord=view r v bits p {w with tag := [],coord0 := []} from Function.update_eq_self _ _,set_indexWord] at h2
  have h3 := SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearField 3)) (ctl (.clearField 4)) (coordinate 3) rfl
    (view r v bits {p with indexWord := []} {w with tag := [],coord0 := []}) w.coord2
  change Runs program _ _ (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := []}) (aux .coord2) w.coord2) _
    (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := []}) (aux .coord2) []) at h3
  rw [show Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := []}) (aux .coord2) w.coord2=view r v bits {p with indexWord := []} {w with tag := [],coord0 := []} from Function.update_eq_self _ _,set_coord2] at h3
  have h4 := SemiprimeD1StackPhysicalLoops.drain program (ctl (.clearField 4)) (ctl .clearSide) (coordinate 4) rfl
    (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := []}) w.coord3
  change Runs program _ _ (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := []}) (aux .coord3) w.coord3) _
    (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := []}) (aux .coord3) []) at h4
  rw [show Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := []}) (aux .coord3) w.coord3=view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := []} from Function.update_eq_self _ _,set_coord3] at h4
  have h5 := SemiprimeD1StackPhysicalLoops.drain program (ctl .clearSide) (ctl .clearCount) side rfl
    (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) p.sideWord
  change Runs program _ _ (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (side) p.sideWord) _
    (Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (side) []) at h5
  rw [show Function.update (view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (side) p.sideWord=view r v bits {p with indexWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []} from Function.update_eq_self _ _,set_sideWord] at h5
  have h6 := SemiprimeD1StackPhysicalLoops.drain program (ctl .clearCount) (ctl .next) count rfl
    (view r v bits {p with indexWord := [],sideWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) p.countWord
  change Runs program _ _ (Function.update (view r v bits {p with indexWord := [],sideWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (count) p.countWord) _
    (Function.update (view r v bits {p with indexWord := [],sideWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (count) []) at h6
  rw [show Function.update (view r v bits {p with indexWord := [],sideWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) (count) p.countWord=view r v bits {p with indexWord := [],sideWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []} from Function.update_eq_self _ _,set_countWord] at h6
  have h7 : Runs program 1 (ctl .next) (view r v bits {p with indexWord := [],sideWord := [],countWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []})
      (ctl .rowTag) (view r v bits {p with indexWord := [],sideWord := [],countWord := []} {w with tag := [],coord0 := [],coord2 := [],coord3 := []}) := by
    apply one_base program _ _ (.jump (ctl .rowTag)) _ _ rfl
    · rfl
    · rfl
  have h := join h0 (join h1 (join h2 (join h3 (join h4 (join h5 (join h6 h7))))))
  convert h using 1
  omega
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsCleanup
