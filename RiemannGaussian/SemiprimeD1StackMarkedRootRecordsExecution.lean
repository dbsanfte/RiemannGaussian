/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsAlignment
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsLoop
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFinish
/-! # Whole original-binary-N marked root-record source and actual-cache ready entry -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsExecution
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsTableView SemiprimeD1StackMarkedRootRecordsRowView
open SemiprimeD1StackMarkedRootRecordsEncoding SemiprimeD1StackMarkedRootRecordsAlignment
open SemiprimeD1StackMarkedRootRecordsAcquisition SemiprimeD1StackMarkedRootRecordsLoop
open SemiprimeD1StackMarkedRootRecordsPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- SAME actual stopped1804 cache, never a supplied factor or owner stream. -/
def retained (bits : List Bool) (hN : 0 < bitValue bits) : R.Stack → List Bool :=
  SemiprimeD1StackRootNetworkRecordsExecution.result bits hN [] []
/-- Complete original paired row list, mathematical byte notation only. -/
def rows (bits : List Bool) (hN : 0 < bitValue bits) : List Row :=
  originalRows (bitValue bits) hN (SemiprimeD1BooleanFactorCatalogueIndices.indices (bitValue bits))
/-- Actual original owner payload retained by the real1804 source. -/
def owners (bits : List Bool) (hN : 0 < bitValue bits) : List Bool :=
  SemiprimeD1StackRootNetworkRecordsExecution.ownerBytes bits hN []
/-- The SAME ready label accepts precisely its actual old source cache and empty new work. -/
def ready (bits : List Bool) (hN : 0 < bitValue bits) : C.State Stack Label :=
  ⟨some (ctl .ready),none,none,view (retained bits hN) (fun _ => []) bits {} {},[]⟩
/-- Whole owner-first marked root record stream, with exactly one terminal FALSE. -/
def outputTape (bits : List Bool) (hN : 0 < bitValue bits) : List Bool :=
  owners bits hN++(payload bits (rows bits hN)++[false])
/-- All1804 old roles and all53 fresh roles survive; only new output and TRUEstatus remain. -/
def result (bits : List Bool) (hN : 0 < bitValue bits) : Stack → List Bool :=
  view (retained bits hN) (VE.result bits) bits {} {status := [true],output := outputTape bits hN}
/-- Literal clean halt with empty actual return cells and transient flags. -/
def done (bits : List Bool) (hN : 0 < bitValue bits) : C.State Stack Label :=
  ⟨none,none,none,result bits hN,[]⟩
/-- Own ready clock charges fresh catalogue, every parsed row/source and both output joins. -/
def readyBound (bits : List Bool) (hN : 0 < bitValue bits) : Nat :=
  setupBudget (retained bits hN) bits+loopBudget bits (rows bits hN)+
    (2*(payload bits (rows bits hN)).length+3)+(9*(owners bits hN).length+19)+1
/-- Whole own clock additionally pays the ACTUAL complete1804 source once. -/
def timeBound (bits : List Bool) (hN : 0 < bitValue bits) : Nat :=
  SemiprimeD1StackRootNetworkRecordsExecution.timeBound bits hN [] []+2+readyBound bits hN
/-- Shared-N template shadows are physically empty before any row has been parsed. -/
theorem private_empty (bits : List Bool) :
    privateTable (tableWords bits [] [] [] [] [])=privateTable (fun _ => []) := by
  funext k
  by_cases h : k=tableNumber
  · simp only [privateTable,h,ite_true]
  · simp only [privateTable,h,ite_false,tableWords]
    split_ifs <;> rfl
/-- Literal real1804 call produces the exact SAME cache accepted by the ready entry. -/
theorem root_run (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ SemiprimeD1StackRootNetworkRecordsExecution.timeBound bits hN [] []+2,
      Runs program t (ctl .start) (input bits) (ctl .ready) (ready bits hN).data := by
  apply SemiprimeD1StackMarkedRootRecordsCalls.root_call bits hc hN
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k
        · rfl
        · change Sum.elim (privateTable (tableWords bits [] [] [] [] [])) (words {}) k=
            Sum.elim (privateTable (fun _ => [])) (fun _ => []) k
          rw [private_empty]
          rcases k with k|k <;> cases k <;> rfl
/-- Whole actual ready trace: no root rerun, no prepared table, no geometry or coefficient supplier. -/
theorem ready_trace (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t, t+1 ≤ readyBound bits hN ∧ Runs program t (ctl .ready) (ready bits hN).data
      (ctl .done) (result bits hN) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact Nat.lt_irrefl _ hN
  obtain ⟨a,ha,h0⟩ := setup_run (retained bits hN) bits rfl rfl hb
  change Runs program a _ _ _
    (view (retained bits hN) (VE.result bits) bits {} {records := SemiprimeD1StackRootNetworkRecordsExecution.result bits hN [] [] (R.factorStack SemiprimeD1StackFullFactorCatalogue.output),descriptors := descriptorBytes bits,output := [false]}) at h0
  rw [factor_cache bits hc hN,descriptor_cache bits hc hN] at h0
  obtain ⟨b,hb0,h1⟩ := loop_run (retained bits hN) (VE.result bits) bits (rows bits hN) [] [false] rfl hb
  simp only [List.append_nil] at h1
  have h2 := SemiprimeD1StackMarkedRootRecordsLogger.reverse_call
    (view (retained bits hN) (VE.result bits) bits {} {history := (payload bits (rows bits hN)).reverse,output := [false]})
  change Runs program (2*(payload bits (rows bits hN)).reverse.length+3) _ _ _
    (Function.update (Function.update
      (view (retained bits hN) (VE.result bits) bits {} {history := (payload bits (rows bits hN)).reverse,output := [false]})
      (aux .history) []) (aux .output) ((payload bits (rows bits hN)).reverse.reverse++[false])) at h2
  rw [set_history,set_output,List.length_reverse,List.reverse_reverse] at h2
  have h3 := SemiprimeD1StackMarkedRootRecordsFinish.join_run (retained bits hN) (VE.result bits) bits
    (owners bits hN) (payload bits (rows bits hN)++[false]) rfl rfl rfl rfl
  refine ⟨a+(b+((2*(payload bits (rows bits hN)).length+3)+(9*(owners bits hN).length+19))),?_,
    join h0 (join h1 (join h2 h3))⟩
  unfold readyBound
  omega
/-- SAME actual ready entry reaches its real halt with empty return stack. -/
theorem ready_run (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ readyBound bits hN, C.run program t (ready bits hN)=some (done bits hN) := by
  obtain ⟨t,ht,h⟩ := ready_trace bits hc hN
  obtain ⟨finish,hf,hs⟩ := h [] (ready bits hN) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits hN) [] finish hs
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some];exact hh⟩
/-- The whole parameterless source starts from original binary N ONLY. -/
theorem source_run (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0 < bitValue bits) :
    ∃ t ≤ timeBound bits hN, C.run program t (initial bits)=some (done bits hN) := by
  obtain ⟨a,ha,h0⟩ := root_run bits hc hN
  obtain ⟨b,hb,h1⟩ := ready_trace bits hc hN
  have h := join h0 h1
  obtain ⟨finish,hf,hs⟩ := h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh := halt_run program (ctl .done) rfl (result bits hN) [] finish hs
  refine ⟨(a+b)+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
    exact hh
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsExecution
