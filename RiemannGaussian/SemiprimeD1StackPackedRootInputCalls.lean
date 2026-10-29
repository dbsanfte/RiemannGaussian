/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootInputPrimitives
/-! # Three actual whole source calls with the shared original bank retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedRootInputCalls
open SemiprimeD1StackPackedRootInput SemiprimeD1StackPackedRootInputEncoding
open SemiprimeD1StackPackedRootInputView SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- The real2270 source executes once from binary N alone. -/
theorem root_call (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ SemiprimeD1StackRootPacketInventoryBounds.runBound bits+1,
      Runs program t (.local .start) (input bits) (.local .marked) (rootReady bits hN) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootPacketInventoryBounds.source_run_bounded bits hc hN
  refine ⟨t+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program rootStack Label.root Sum.inl_injective
    R.program (.local .start) (fun _ => rfl) (.local .start) (.local .marked) rfl t
    (R.initial bits) (SemiprimeD1StackRootPacketInventoryEncoding.done bits hN) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      rfl
    · intro k _
      rfl
  · constructor
    · intro k
      rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The real marked continuation consumes precisely its actual retained old bank, without root replay. -/
theorem marked_call (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t ≤ SemiprimeD1StackMarkedRootRecordsExecution.readyBound bits hN+1,
      Runs program t (.local .marked) (rootReady bits hN) (.local .copyNumber) (markedReady bits hN) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackMarkedRootRecordsExecution.ready_run bits hc hN
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program markedStack Label.marked marked_injective
    W.program (W.ctl .ready) (fun _ => rfl) (.local .marked) (.local .copyNumber) rfl t
    (SemiprimeD1StackMarkedRootRecordsExecution.ready bits hN)
    (SemiprimeD1StackMarkedRootRecordsExecution.done bits hN) _ _ rfl rfl rfl rfl hr
    (marked_ready_rel bits hN) (marked_result_rel bits hN)
/-- The real context source acquires the new precision/rank/TRUEwidth from the physically copied N. -/
theorem context_call (bits : List Bool) (hN : 0<bitValue bits) :
    ∃t ≤ 2000*(bits.length+1)^2+1,
      Runs program t (.local .context) (contextReady bits hN) (.local .done) (result bits hN) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPackedRootContextExecution.source_run_bounded bits
  refine ⟨t+1,by simpa only [SemiprimeD1StackPackedRootContextExecution.polynomial] using Nat.add_le_add_right ht 1,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program contextStack Label.context context_injective
    J.program (.inl .start) (fun _ => rfl) (.local .context) (.local .done) rfl t
    (SemiprimeD1StackPackedRootContext.initial bits) (SemiprimeD1StackPackedRootContextEncoding.done bits)
    _ _ rfl rfl rfl rfl hr (context_ready_rel bits hN) (context_result_rel bits hN)
end RiemannGaussian.SemiprimeD1StackPackedRootInputCalls
