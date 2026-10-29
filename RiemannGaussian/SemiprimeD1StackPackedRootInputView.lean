/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputEncoding
/-! # Actual acquired-bank relations for the shared marked continuation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputView
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackMultiplierLink (DataRel)
/-- All207 new marked-source roles are genuinely empty at its honest ready entry. -/
theorem ready_private_empty (bits : List Bool) (hN : 0<bitValue bits) (k : Private) :
    (SemiprimeD1StackMarkedRootRecordsExecution.ready bits hN).data (.inr k)=[] := by
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · change SemiprimeD1StackMarkedRootRecords.privateTable
        (SemiprimeD1StackMarkedRootRecordsTableView.tableWords bits [] [] [] [] []) k=[]
      rw [SemiprimeD1StackMarkedRootRecordsExecution.private_empty]
      simp only [SemiprimeD1StackMarkedRootRecords.privateTable,ite_self]
    · cases k <;> rfl
/-- The SAME acquired2270 bank supplies the entire real ready2011 front door. -/
theorem marked_ready_rel (bits : List Bool) (hN : 0<bitValue bits) :
    DataRel markedStack (rootReady bits hN)
      (SemiprimeD1StackMarkedRootRecordsExecution.ready bits hN).data (rootReady bits hN) := by
  constructor
  · intro k
    rcases k with k|k
    · exact SemiprimeD1PackedRootRetained.source_projection bits hN k
    · exact (ready_private_empty bits hN k).symm
  · intro k _
    rfl
/-- The marked continuation restores every old1804 word and retains every foreign2270 word. -/
theorem marked_result_rel (bits : List Bool) (hN : 0<bitValue bits) :
    DataRel markedStack (rootReady bits hN)
      (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN).data (markedReady bits hN) := by
  constructor
  · intro k
    rcases k with k|k
    · exact (SemiprimeD1PackedRootRetained.source_projection bits hN k).trans
        (SemiprimeD1StackMarkedRootRecordsOriginal.root_preserved bits hN k).symm
    · rfl
  · intro k hk
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · exact (hk (.inr k) rfl).elim
      · rfl
/-- The actual copied N forms the full honest28-role source front door. -/
theorem context_ready_rel (bits : List Bool) (hN : 0<bitValue bits) :
    DataRel contextStack (contextReady bits hN) (J.input bits) (contextReady bits hN) := by
  constructor
  · intro k
    rfl
  · intro k _
    rfl
/-- Acquiring the new header retains ALL actual original and marked record-source data. -/
theorem context_result_rel (bits : List Bool) (hN : 0<bitValue bits) :
    DataRel contextStack (contextReady bits hN)
      (SemiprimeD1StackPackedRootContextEncoding.done bits).data (result bits hN) := by
  constructor
  · intro k
    rfl
  · intro k hk
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · exact (hk k rfl).elim
end RiemannGaussian.SemiprimeD1StackPackedRootInputView
