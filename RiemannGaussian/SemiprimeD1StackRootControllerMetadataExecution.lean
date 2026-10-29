/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootControllerMetadata

/-! # Actual one-input root source and schedule composition
The already acquired M tally is retained. The actual schedule program reads
the same binary N in place, preserving every previously acquired source cell.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootControllerMetadataExecution
open SemiprimeD1StackRootControllerMetadata SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual original source call; no count, graph, ordinal bank or source cache is supplied. -/
theorem source_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤SemiprimeD1StackRootScopeBankBounds.polynomial bits.length,
      Runs program (t+1) (ctl .start) (input bits) (ctl .schedule) (afterSource bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScopeBankBounds.source_run_polynomial bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program sourceStack sourceLabel Sum.inl_injective
    S.program (.inl .start) (fun _=>rfl) (ctl .start) (ctl .schedule) rfl t
    (S.initial bits) (S.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>
        rcases k with k|k
        · cases k <;> rfl
        · rcases k with k|k <;> cases k <;> rfl
/-- Reuse any actually acquired source cache with its retained N role; every source cell is preserved. -/
theorem prepared_schedule_call (bits:List Bool) (source:S.Stack→List Bool)
    (hinput:source S.originalInput=bits) :
    ∃t≤SemiprimeD1StackRootScheduleExecution.runBound bits,
      Runs program (t+1) (ctl .schedule) (payload source (R.input bits))
        (ctl .done) (payload source (R.result bits)) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackRootScheduleExecution.source_run bits
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program scheduleStack scheduleLabel schedule_injective
    R.program .start (fun _=>rfl) (ctl .schedule) (ctl .done) rfl t
    (R.initial bits) (R.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k
      exact payload_schedule source (R.input bits) hinput k
    · intro k _;rfl
  · constructor
    · intro k
      exact payload_schedule source (R.result bits)
        (hinput.trans (SemiprimeD1StackRootScheduleOriginal.input_preserved bits).symm) k
    · intro k hk;cases k with
      | inl k=>rfl
      | inr k=>
        by_cases he:k=R.boot .input
        · subst k;rfl
        · exact (hk k (by simp only [scheduleStack,he,ite_false])).elim
/-- Actual schedule acquisition reuses the original source's already retained N role. -/
theorem schedule_call (bits:List Bool) :
    ∃t≤SemiprimeD1StackRootScheduleExecution.runBound bits,
      Runs program (t+1) (ctl .schedule) (afterSource bits) (ctl .done) (result bits) :=
  prepared_schedule_call bits (S.result bits) (source_retained_N bits)
/-- Entire same-program acquisition prefix, preserving every caller's real outer frames. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t,t+1≤runBound bits ∧ Runs program t (ctl .start) (input bits) (ctl .done) (result bits) := by
  obtain ⟨s,hs,h0⟩:=source_call bits hc hN
  obtain ⟨r,hr,h1⟩:=schedule_call bits
  refine ⟨(s+1)+(r+1),?_,runs_trans program _ _ _ _ _ _ _ _ h0 h1⟩
  unfold runBound
  omega
/-- Complete actual original-N source halt, including both nested calls and the final halt. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t≤runBound bits,SemiprimeD1StackCalls.run program t (initial bits)=some (done bits) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN
  obtain ⟨finish,hf,hs⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
end RiemannGaussian.SemiprimeD1StackRootControllerMetadataExecution
